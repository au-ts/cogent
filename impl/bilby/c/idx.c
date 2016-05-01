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

#define IDX_HASH_SIZE 2048

int idx_init(struct bilbyfs_info *bi)
{
        int i;

        bi->idx_hash = vmalloc(sizeof(*(bi->idx_hash)) * IDX_HASH_SIZE);
        if (!bi->idx_hash)
                return -ENOMEM;
        for (i = 0; i < IDX_HASH_SIZE; i++) {
                bi->idx_hash[i] = RBT_ROOT;
        }
        return 0;
}

void idx_clean(struct bilbyfs_info *bi)
{
      struct rbt_root *idx_tree;
      struct rbt_node *node;
      int i;

      for (i = 0; i < IDX_HASH_SIZE; i++) {
              idx_tree = &bi->idx_hash[i];
              for (node = rbt_first(idx_tree);
                   node;
                   node = rbt_first(idx_tree)) {
                      rbt_erase(node, idx_tree);
                      kfree(node);
              }
      }
      vfree(bi->idx_hash);
      bi->idx_hash = NULL;
}

/* Rb search from Linux Documentation */
static struct idx_node *idx_index_search(struct rbt_root *root, obj_id id)
{
      struct rbt_node *node = root->rbt_node;
      struct idx_node *xnode;
      /*
      struct timeval st, stp;

      do_gettimeofday(&st);
      */
      while (node) {
              xnode = container_of(node, struct idx_node, node);

              if (id < xnode->id)
                      node = node->rbt_left;
              else if (id > xnode->id)
                      node = node->rbt_right;
              else {
                      /*
                      do_gettimeofday(&stp);
                      pr_err("timed index search : %ld sec %ld usec\n", stp.tv_sec - st.tv_sec, stp. tv_usec - st.tv_usec);
                      */
                      return xnode;
              }
      }
      /*
      do_gettimeofday(&stp);
      pr_err("timed index search : %ld sec %ld usec\n", stp.tv_sec - st.tv_sec, stp. tv_usec - st.tv_usec);
      */
      return NULL;
}

static u32 idx_hash_inum(u32 inum)
{
        return inum % IDX_HASH_SIZE;
}

int idx_get_obj_addr(struct bilbyfs_info *bi, obj_id id, struct obj_addr *addr)
{
        struct idx_node *xnode;
        u32 inum = inum_from_id(id);
        u32 hash = idx_hash_inum(inum);

        xnode = idx_index_search(&bi->idx_hash[hash], id);

        if (!xnode)
                return -ENOENT;
        *addr = xnode->addr;
        return 0;
}

/* Rb insert from Linux Documentation */
static struct idx_node *index_insert_or_replace(struct bilbyfs_info *bi, struct rbt_root *root, obj_id id, struct idx_node *allocated_node)
{
      struct rbt_node **new = &(root->rbt_node), *parent = NULL;
      struct idx_node *xnode;

      /* Figure out where to put new node */
      while (*new) {
              xnode = container_of(*new, struct idx_node, node);

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

int idx_set_obj_addr(struct bilbyfs_info *bi, obj_id id, struct obj_addr *addr, struct idx_node *allocated_node)
{
        struct idx_node *xnode;
        u32  inum = inum_from_id(id);
        u32 hash = idx_hash_inum(inum);

        xnode = index_insert_or_replace(bi, &bi->idx_hash[hash], id, allocated_node);
        xnode->addr = *addr;
        return 0;
}

struct idx_node *idx_get_or_create_obj_addr_node(struct bilbyfs_info *bi, obj_id id)
{
        u32  inum = inum_from_id(id);
        u32 hash = idx_hash_inum(inum);

        return index_insert_or_replace(bi, &bi->idx_hash[hash], id, NULL);
}

obj_id idx_next_obj_id(struct bilbyfs_info *bi, obj_id id)
{
        struct rbt_node *node;
        struct idx_node *xnode;
        struct idx_node *xnode_greater = NULL;
        u32 inum = inum_from_id(id);
        u32 hash = idx_hash_inum(inum);

        node = bi->idx_hash[hash].rbt_node;


      /* Find a elem greater than @id then follow only left branches
       * to find a lower id closer to @id.
       */
      while (node) {
              xnode = container_of(node, struct idx_node, node);

              if (id < xnode->id) {
                      xnode_greater = xnode;
                      node = node->rbt_left;
              } else if (id >= xnode->id) {
                      node = node->rbt_right;
              }
      }
      if (!xnode_greater)
              return NIL_ID;
      if (inum != inum_from_id(xnode_greater->id))
              return NIL_ID;
      return xnode_greater->id;
}

void *idx_del_obj_addr(struct bilbyfs_info *bi, obj_id id)
{
        struct idx_node *xnode;
        u32  inum = inum_from_id(id);
        u32 hash = idx_hash_inum(inum);

        xnode = idx_index_search(&bi->idx_hash[hash], id);
        bilbyfs_assert(xnode);
        rbt_erase(&xnode->node, &bi->idx_hash[hash]);
        return xnode;
}
