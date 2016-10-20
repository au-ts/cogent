/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include <bilbyfs.h>

#define GIM_HASH_SIZE 2048

int gim_init(struct bilbyfs_info *bi)
{
        int i;

        bi->gim_hash = vmalloc(sizeof(*(bi->gim_hash)) * GIM_HASH_SIZE);
        if (!bi->gim_hash)
                return -ENOMEM;
        for (i = 0; i < GIM_HASH_SIZE; i++) {
                bi->gim_hash[i] = RBT_ROOT;
        }
        return 0;
}

void gim_clean(struct bilbyfs_info *bi)
{
      struct rbt_root *gim_tree;
      struct rbt_node *node;
      int i;

      for (i = 0; i < GIM_HASH_SIZE; i++) {
              gim_tree = &bi->gim_hash[i];
              for (node = rbt_first(gim_tree);
                   node;
                   node = rbt_first(gim_tree)) {
                      rbt_erase(node, gim_tree);
                      allocpool_free_single(node);
              }
      }
      vfree(bi->gim_hash);
      bi->gim_hash = NULL;
}

static u32 gim_hash_inum(u32 inum)
{
        return inum % GIM_HASH_SIZE;
}

/* Rb search from Linux Documentation */
static struct gim_node *gim_index_search(struct bilbyfs_info *bi, obj_id id)
{
        u32 hash = gim_hash_inum(inum_from_id(id));
        struct rbt_root *root = &bi->gim_hash[hash];
      struct rbt_node *node = root->rbt_node;
      struct gim_node *gnode;
      /*
      struct timeval st, stp;

      do_gettimeofday(&st);
      */
      while (node) {
              gnode = container_of(node, struct gim_node, node);

              if (id < gnode->id)
                      node = node->rbt_left;
              else if (id > gnode->id)
                      node = node->rbt_right;
              else {
                      /*
                      do_gettimeofday(&stp);
                      pr_err("timed gim search : %ld sec %ld usec\n", stp.tv_sec - st.tv_sec, stp. tv_usec - st.tv_usec);
                      */
                      return gnode;
              }
      }
      /*
      do_gettimeofday(&stp);
      pr_err("timed gim search : %ld sec %ld usec\n", stp.tv_sec - st.tv_sec, stp. tv_usec - st.tv_usec);
                      */
      return NULL;
}

static struct gim_node *gim_insert_or_replace(struct bilbyfs_info *bi, obj_id id, struct gim_node *allocated_node)
{
        u32 hash = gim_hash_inum(inum_from_id(id));
        struct rbt_root *root = &bi->gim_hash[hash];
        struct rbt_node **new = &(root->rbt_node), *parent = NULL;
        struct gim_node *xnode;

        /* Figure out where to put new node */
        while (*new) {
                xnode = container_of(*new, struct gim_node, node);

                parent = *new;
                if (id < xnode->id)
                        new = &((*new)->rbt_left);
                else if (id > xnode->id)
                        new = &((*new)->rbt_right);
                else {
                        kfree(allocated_node);
                        return xnode;
                }
        }

        xnode = allocated_node ? allocated_node : allocpool_pop(&bi->node_pool);
        memset(xnode, 0, sizeof(*xnode));
        xnode->id = id;
        /* Add new node and rebalance tree. */
        rbt_link_node(&xnode->node, parent, new);
        rbt_insert_color(&xnode->node, root);
        return xnode;
}

int gim_mark_garbage_cnt(struct bilbyfs_info *bi, obj_id id, struct obj_addr *addr, u32 count, struct gim_node *allocated_node)
{
        struct gim_node *gnode = gim_insert_or_replace(bi, id, allocated_node);

        if (gnode->sqnum < addr->sqnum)
                gnode->sqnum = addr->sqnum;
        gnode->count += count;
        return 0;
}

int gim_mark_garbage(struct bilbyfs_info *bi, obj_id id, struct obj_addr *addr, struct gim_node *allocated_node)
{
        return gim_mark_garbage_cnt(bi, id, addr, 1, allocated_node);
}

struct gim_node *gim_next_node(struct bilbyfs_info *bi, struct gim_node *curr_gnode)
{
        struct rbt_node *node;
        struct gim_node *gnode;
        struct gim_node *gnode_greater = NULL;
        obj_id id = curr_gnode->id;
        u32  inum = inum_from_id(id);
        u32 hash = gim_hash_inum(inum);

        node = bi->gim_hash[hash].rbt_node;

      /* Find a elem greater than @id then follow only left branches
       * to find a lower id closer to @id.
       */
      while (node) {
              gnode = container_of(node, struct gim_node, node);

              if (id < gnode->id) {
                      gnode_greater = gnode;
                      node = node->rbt_left;
              } else if (id >= gnode->id) {
                      node = node->rbt_right;
              }
      }
      return gnode_greater;
}

int gim_is_removable(struct bilbyfs_info *bi, struct obj_ch *obj)
{
        obj_id id;
        u64 sqnum = le64_to_cpu(obj->sqnum);
        u32 id_type;
        struct gim_node *gnode, *pre_gnode = NULL;

        // Padding object can be always garbage collected
        if (obj->type == BILBYFS_PAD_OBJ || obj->type == BILBYFS_SUM_OBJ)
                return BILBYFS_TRUE;

        // Object not found in garbage list
        id = get_obj_id(obj);
        gnode = gim_index_search(bi, id);
        if (!gnode)
                return BILBYFS_FALSE;

        // Object version is newer
        if (sqnum > gnode->sqnum) /*  Is this possible? In which circumstances? */
                return BILBYFS_FALSE;

        // Deletion object
        if (obj->type == BILBYFS_DEL_OBJ) {
                id_type = type_from_id(id);
                switch (id_type) {
                case BILBYFS_DENTARR_OBJ:
                        return BILBYFS_TRUE;
                case BILBYFS_INODE_OBJ:
                case BILBYFS_DATA_OBJ:
                        while (gnode != NULL && (pre_gnode == NULL ||
                               inum_from_id(gnode->id) == inum_from_id(pre_gnode->id))) {
                                if (sqnum >= gnode->sqnum && gnode->count > 1)
                                        return BILBYFS_FALSE;

                                pre_gnode = gnode;
                                gnode = gim_next_node(bi, gnode);
                        }
                        return BILBYFS_TRUE;
                default:
                        bilbyfs_assert(0);
                }
        }

        // Other objects in the garbage list
        return BILBYFS_TRUE;
}

int gim_garbage_collected(struct bilbyfs_info *bi, struct obj_ch *obj)
{
        struct gim_node *gnode;
        obj_id id;
        u32 hash;

        if (obj->type == BILBYFS_PAD_OBJ || obj->type == BILBYFS_SUM_OBJ)
                return 0;

        id = get_obj_id(obj);
        hash = gim_hash_inum(inum_from_id(id));
        gnode = gim_index_search(bi, id);
        if (gnode) {
                gnode->count--;
                if (gnode->count <= 0) {
                        rbt_erase(&gnode->node, &bi->gim_hash[hash]);
                        allocpool_free_single(gnode);
                }
                return 0;
        }

        return -ENOENT;
}

