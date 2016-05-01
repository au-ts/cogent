/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include <os/linux/wrapper_pp_inferred.c>

void bilbyfs_kill_super(struct super_block *sb);
struct dentry *bilbyfs_mount(struct file_system_type *fs_type, int flags,
                             const char *name, void *data);

static struct file_system_type bilbyfs_fs_type = {
        .name    = "bilbyfs",
        .owner   = THIS_MODULE,
        .mount   = bilbyfs_mount,
        .kill_sb = bilbyfs_kill_super,
};

struct kmem_cache *node_slab;
struct kmem_cache *bilbyfs_inode_slab;
static void bilbyfs_free_inode(struct rcu_head *head)
{
        struct inode *inode = container_of(head, struct inode, i_rcu);

        bilbyfs_debug("bilbyfs_free_inode(ino = %lu)\n", inode->i_ino);
        kmem_cache_free(bilbyfs_inode_slab, inode);
}


static void bilbyfs_destroy_inode(struct inode *inode)
{
        bilbyfs_debug("bilbyfs_destroy_inode(ino=%lu)\n", inode->i_ino);
        kfree(inode->i_private);
        inode->i_private = NULL;

        call_rcu(&inode->i_rcu, bilbyfs_free_inode);
}


static struct inode *bilbyfs_alloc_inode(struct super_block *sb)
{
        return kmem_cache_alloc(bilbyfs_inode_slab, GFP_NOFS);
}

static const struct super_operations bilbyfs_super_operations =
{
        .alloc_inode    = bilbyfs_alloc_inode,
        .destroy_inode  = bilbyfs_destroy_inode,
        .put_super      = bilbyfs_put_super,
        .statfs         = bilbyfs_statfs,
        /* .remount_fs     = bilbyfs_remount_fs, */
        .evict_inode    = bilbyfs_evict_inode,
        .sync_fs        = bilbyfs_sync_fs,
};


#define NODE_SIZE max(sizeof(BilbyFsRbtIndexNode), sizeof(BilbyFsRbtGimNode))
static inline void node_slab_ctor(void *node)
{
       memset(node, 0, NODE_SIZE); 
        /* We don't initialise node */
}

static inline int allocpool_init(void)
{
        bilbyfs_debug("allocpool_init(%u)\n", NODE_SIZE);
        node_slab = kmem_cache_create("bilbyfs_node_slab",
                                NODE_SIZE, 0,
                                SLAB_MEM_SPREAD | SLAB_RECLAIM_ACCOUNT,
                                &node_slab_ctor);
        if (!node_slab)
                return -ENOMEM;
        return 0;
}

static inline void allocpool_destroy(void)
{
        if (node_slab)
                kmem_cache_destroy(node_slab);
}

/*
 * Inode slab cache constructor.
 */
static void inode_slab_ctor(void *obj)
{
        inode_init_once(obj);
}

static int __init bilbyfs_init(void)
{
        int err;

        /* Make sure node sizes are 8-byte aligned (BILBYFS_OBJ_PADDING) */
        bilbyfs_inode_slab = kmem_cache_create("bilbyfs_inode_slab",
                                sizeof(BilbyFsVfsInode), 0,
                                SLAB_MEM_SPREAD | SLAB_RECLAIM_ACCOUNT,
                                &inode_slab_ctor);
        if (!bilbyfs_inode_slab)
                return -ENOMEM;
        err = allocpool_init();
        if (!err)
                err = register_filesystem(&bilbyfs_fs_type);
        if (err) {
                bilbyfs_err("cannot register file system, error %d", err);
                kmem_cache_destroy(bilbyfs_inode_slab);
                allocpool_destroy();
                return err;
        }
        return 0;
}
module_init(bilbyfs_init);

static void __exit bilbyfs_exit(void)
{
        /* Not sure why UBIFS destroy the slab before unregistering
         * but for now we do the same. FIXME More investigation required.
         */
        rcu_barrier();
        kmem_cache_destroy(bilbyfs_inode_slab);
        unregister_filesystem(&bilbyfs_fs_type);
}
module_exit(bilbyfs_exit);

MODULE_LICENSE("GPL");
MODULE_VERSION(__stringify(BILBYFS_VERSION));
MODULE_AUTHOR("Sidney Amani");
MODULE_DESCRIPTION("BilbyFs - Bilby File System");

