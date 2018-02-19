/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include <plat/linux/wrapper_pp_inferred.c>

static int ext2fs_readpage_nolock(struct file *file, struct page *page);
static int ext2fs_writepage_nolock(struct page *page, struct writeback_control *wbc);
static int ext2fs_writepages_nolock(struct address_space *mapping, struct writeback_control *wbc);
static int ext2fs_readpages_nolock(struct file *file, struct address_space *mapping,
                                   struct list_head *pages, unsigned nr_pages);
static sector_t ext2fs_bmap_nolock(struct address_space *mapping, sector_t block);
static int ext2fs_write_begin_nolock(struct file *file, struct address_space *mapping,
                                     loff_t pos, unsigned len, unsigned flags,
                                     struct page **pagep, void **fsdata);
static int ext2fs_write_end_nolock(struct file *file, struct address_space *mapping,
                                   loff_t pos, unsigned len, unsigned copied,
                                   struct page *page, void *fsdata);

/* calls writepage directly; no lock */
static int __nolock_write_one_page(struct page *page, int wait)
{
    struct address_space *mapping = page->mapping;
    int ret = 0;
    struct writeback_control wbc = {
        .sync_mode = WB_SYNC_ALL,
        .nr_to_write = 1,
    };

    BUG_ON(!PageLocked(page));

    if (wait)
        wait_on_page_writeback(page);

    if (clear_page_dirty_for_io(page)) {
#if LINUX_VERSION_CODE < KERNEL_VERSION(4,4,0)
        page_cache_get(page);
#else
        get_page(page);
#endif
        /* ret = mapping->a_ops->writepage(page, &wbc); */
        ret = ext2fs_writepage_nolock (page, &wbc);
        if (ret == 0 && wait) {
           wait_on_page_writeback(page);
           if (PageError(page))
              ret = -EIO;
        }
#if LINUX_VERSION_CODE < KERNEL_VERSION(4,4,0)
        page_cache_release(page);
#else
        put_page(page);
#endif
    } else {
        unlock_page(page);
    }
    return ret;
}

struct kmem_cache *ext2fs_inode_slab;

static struct dentry *ext2fs_mount(struct file_system_type *fs_type,
                      int flags, const char *name, void *data)
{
    return mount_bdev(fs_type, flags, name, data, ext2fs_fill_super);
}

static int ext2fs_readpage(struct file *file, struct page *page)
{
    struct inode *inode = page->mapping->host;
    Ext2State *state = inode->i_sb->s_fs_info;

    down(&state->iop_lock); /* aop */
    take_inode_addrspace(inode);

    int res = ext2fs_readpage_nolock(file, page);

    release_inode_addrspace(inode);
    up(&state->iop_lock); /* aop */

    return res;
}

static int ext2fs_readpage_nolock(struct file *file, struct page *page)
{
    return mpage_readpage(page, ext2fs_get_block);
}

static int ext2fs_readpages(struct file *file, struct address_space *mapping,
                            struct list_head *pages, unsigned nr_pages)
{
    struct page *first_page = list_first_entry(pages, struct page, lru); /* TODO: is there a helper function to do this? */
    struct inode *inode = mapping->host;
    Ext2State *state = inode->i_sb->s_fs_info;

    down(&state->iop_lock); /* aop */
    take_inode_addrspace(inode);

    int res = ext2fs_readpages_nolock(file, mapping, pages, nr_pages);

    release_inode_addrspace(inode);
    up(&state->iop_lock); /* aop */

    return res;
}

static int ext2fs_readpages_nolock(struct file *file, struct address_space *mapping,
                                   struct list_head *pages, unsigned nr_pages)
{
    return mpage_readpages(mapping, pages, nr_pages, ext2fs_get_block);
}

static int ext2fs_writepage(struct page *page, struct writeback_control *wbc)
{
    struct inode* inode = page->mapping->host;
    Ext2State *state = inode->i_sb->s_fs_info;

    down(&state->iop_lock); /* aop */
    take_inode_addrspace(inode);

    int res = ext2fs_writepage_nolock(page, wbc);

    release_inode_addrspace(inode);
    up(&state->iop_lock); /* aop */

    return res;
}

static int ext2fs_writepage_nolock(struct page *page, struct writeback_control *wbc)
{

    return block_write_full_page(page, ext2fs_get_block, wbc);
}

static int ext2fs_writepages(struct address_space *mapping, struct writeback_control *wbc)
{
    struct inode* inode = mapping->host;
    Ext2State *state = inode->i_sb->s_fs_info;

    down(&state->iop_lock); /* aop */
    take_inode_addrspace(inode);

    int res = ext2fs_writepages_nolock(mapping, wbc);

    release_inode_addrspace(inode);
    up(&state->iop_lock); /* aop */

    return res;
}

static int ext2fs_writepages_nolock(struct address_space *mapping, struct writeback_control *wbc)
{
    return mpage_writepages(mapping, wbc, ext2fs_get_block);
}

/* CALLER MUST LOCK */
static void ext2fs_write_failed(struct address_space *mapping, loff_t to)
{
    struct inode *inode = mapping->host;
    if (to > inode->i_size) {
        truncate_pagecache(inode, inode->i_size);
        if (ext2fs_can_truncate(inode) == 0) {
            ext2fs_truncate(inode, inode->i_size);
        }
    }
}

static int ext2fs_write_begin(struct file *file, struct address_space *mapping,
                              loff_t pos, unsigned len, unsigned flags,
                              struct page **pagep, void **fsdata)
{
    int ret;
    struct inode* inode = mapping->host;
    Ext2State *state = inode->i_sb->s_fs_info;

    down(&state->iop_lock); /* aop */
    take_inode_addrspace(inode);

    ret = ext2fs_write_begin_nolock(file, mapping, pos, len, flags, pagep, fsdata);

    release_inode_addrspace(inode);
    up(&state->iop_lock); /* aop */

    return ret;
}

static int ext2fs_write_begin_nolock(struct file *file, struct address_space *mapping,
                                     loff_t pos, unsigned len, unsigned flags,
                                     struct page **pagep, void **fsdata)
{
    int ret = block_write_begin(mapping, pos, len, flags, pagep, ext2fs_get_block);
    if (ret < 0) {
        ext2fs_write_failed(mapping, pos + len);
    }

    return ret;
}

static int ext2fs_write_end(struct file *file, struct address_space *mapping,
                            loff_t pos, unsigned len, unsigned copied,
                            struct page *page, void *fsdata)
{
    struct inode* inode = mapping->host;
    Ext2State *state = inode->i_sb->s_fs_info;
    int ret;

    down(&state->iop_lock); /* aop */
    take_inode_addrspace(inode);

    ret = ext2fs_write_end_nolock(file, mapping, pos, len, copied, page, fsdata);

    release_inode_addrspace(inode);
    up(&state->iop_lock); /* aop */

    return ret;
}

static int ext2fs_write_end_nolock(struct file *file, struct address_space *mapping,
                                   loff_t pos, unsigned len, unsigned copied,
                                   struct page *page, void *fsdata)
{
    int ret = generic_write_end(file, mapping, pos, len, copied, page, fsdata);
    if (ret < len) {
        ext2fs_write_failed(mapping, pos + len);
    }

    return ret;
}

static sector_t ext2fs_bmap(struct address_space *mapping, sector_t block)
{
    struct inode* inode = mapping->host;
    Ext2State *state = inode->i_sb->s_fs_info;

    down(&state->iop_lock); /* aop */
    sector_t res = ext2fs_bmap_nolock(mapping, block);
    up (&state->iop_lock); /* aop */

    return res;
}

static sector_t ext2fs_bmap_nolock(struct address_space *mapping, sector_t block)
{
    return generic_block_bmap(mapping, block, ext2fs_get_block);
}

/* support migrate to new internal iter API */
#if LINUX_VERSION_CODE < KERNEL_VERSION(4, 7, 0)
static ssize_t ext2fs_direct_IO_nolock(int rw, struct kiocb *iocb,
                                       struct iov_iter *iter, loff_t offset)
{
    struct file *file = iocb->ki_filp;
    struct address_space *mapping = file->f_mapping;
    struct inode *inode = mapping->host;
    size_t count = iov_iter_count(iter);
    loff_t offset = iocb->ki_pos;
    ssize_t ret;

    ret = blockdev_direct_IO(rw, iocb, inode, iter, offset, ext2fs_get_block);
    if (ret < 0 && (rw & WRITE)) {
        truncate_pagecache(inode, inode->i_size);
        if (ext2fs_can_truncate(inode) == 0) {
            ext2fs_truncate(inode, inode->i_size);
        }
    }

    return ret;
}

static ssize_t ext2fs_direct_IO(int rw, struct kiocb *iocb, struct iov_iter *iter,
                                loff_t offset)
{
    ssize_t ret;
    struct file *file = iocb->ki_filp;
    struct address_space *mapping = file->f_mapping;
    struct inode *inode = mapping->host;
    Ext2State *state = inode->i_sb->s_fs_info;

    down(&state->iop_lock); /* aop */
    take_inode_addrspace(inode);

    ret = ext2fs_direct_IO_nolock(rw, iocb, iter, offset);

    release_inode_addrspace(inode);
    up(&state->iop_lock); /* aop */

    return ret;
}

#else /* KERNEL_VERSION > KERNEL_VERSION_CODE(4, 7, 0) */
static ssize_t ext2fs_direct_IO_nolock(struct kiocb *iocb, struct iov_iter *iter)
{
    struct file *file = iocb->ki_filp;
    struct address_space *mapping = file->f_mapping;
    struct inode *inode = mapping->host;
    size_t count = iov_iter_count(iter);
    loff_t offset = iocb->ki_pos;
    ssize_t ret;

    ret = blockdev_direct_IO(iocb, inode, iter, ext2fs_get_block);
    if (ret < 0 && iov_iter_rw(iter) == WRITE)
            ext2fs_write_failed(mapping, offset + count);
    return ret;
}

static ssize_t ext2fs_direct_IO(struct kiocb *iocb, struct iov_iter *iter)
{
    ssize_t ret;
    struct file *file = iocb->ki_filp;
    struct address_space *mapping = file->f_mapping;
    struct inode *inode = mapping->host;
    Ext2State *state = inode->i_sb->s_fs_info;

    down (&state->iop_lock); /* aop */
    take_inode_addrspace(inode);

    ret = ext2fs_direct_IO_nolock(iocb, iter);

    release_inode_addrspace(inode);
    up (&state->iop_lock); /* aop */

    return ret;
}
#endif

static void ext2fs_destroy_inode(struct inode *inode)
{
    call_rcu(&inode->i_rcu, ext2fs_i_callback);
}

/*
 * address space operations
 *
 * while these are top-level, then can be indirectly called by
 * COGENT from some VFS ADT functions
 *
 * to prevent deadlock, we need to swap any iops to use the nolock
 * version if we were being called from within COGENT
 */
const struct address_space_operations ext2fs_address_operations =
{
    .readpage =                 ext2fs_readpage,
    .readpages =                ext2fs_readpages,
    .direct_IO =                ext2fs_direct_IO,
    .writepage =                ext2fs_writepage,
    .write_begin =              ext2fs_write_begin,
    .write_end =                ext2fs_write_end,
    .bmap =                     ext2fs_bmap,
    .writepages =               ext2fs_writepages,

    .migratepage =              buffer_migrate_page,
    .is_partially_uptodate =    block_is_partially_uptodate,
    .error_remove_page =        generic_error_remove_page,
};

const struct address_space_operations ext2fs_address_operations_nolock =
{
    .readpage =                 ext2fs_readpage_nolock,
    .readpages =                ext2fs_readpages_nolock,
    .direct_IO =                ext2fs_direct_IO_nolock,
    .writepage =                ext2fs_writepage_nolock,
    .write_begin =              ext2fs_write_begin_nolock,
    .write_end =                ext2fs_write_end_nolock,
    .bmap =                     ext2fs_bmap_nolock,
    .writepages =               ext2fs_writepages_nolock,

    .migratepage =              buffer_migrate_page,
    .is_partially_uptodate =    block_is_partially_uptodate,
    .error_remove_page =        generic_error_remove_page,
};


/*
 * "super-block" operations
 * these are performed on a mounted instance
 *
 * these functions may also be top-level or re-entrant (in particlar, *_inode)
 */
const struct super_operations ext2fs_super_operations =
{
    .statfs =                   ext2fs_statfs,       /* FIXME: not re-entrant safe */

    .alloc_inode =              ext2fs_alloc_inode,  /* nolock */
    .destroy_inode =            ext2fs_destroy_inode,/* nolock */
    .write_inode =              ext2fs_write_inode,  /* lockok, ret? */
    .evict_inode =              ext2fs_evict_inode,  /* lockok */

    .put_super =                ext2fs_put_super,     /* lockok */
    // sync_fs
};

const struct super_operations ext2fs_super_operations_nolock =
{
    .statfs =                   ext2fs_statfs,              /* FIXME: not re-entrant safe */

    .alloc_inode =              ext2fs_alloc_inode,         /* nolock */
    .destroy_inode =            ext2fs_destroy_inode,       /* nolock */
    .write_inode =              ext2fs_write_inode_nolock,  /* lockok, ret? */
    .evict_inode =              ext2fs_evict_inode_nolock,  /* lockok */

    .put_super =                ext2fs_put_super,           /* lockok */
    // sync_fs
};

static struct file_system_type ext2fs_fs_type = {
    .name =                     "ext2fs",
    .owner =                    THIS_MODULE,
    .mount =                    ext2fs_mount,        /* no lock */
    .kill_sb =                  kill_block_super,
    .fs_flags =                 FS_REQUIRES_DEV,
};

static void inode_slab_ctor (void *obj)
{
    VfsInode *abstract_inode = obj;
    memset(abstract_inode, 0, sizeof(VfsInode));
    inode_init_once (&(abstract_inode->vfs.inode_lin));
}

static int __init ext2fs_init(void)
{
    int err;

    ext2fs_inode_slab = kmem_cache_create("ext2fs_inode_slab",
                            sizeof(VfsInode), 0,
                            SLAB_MEM_SPREAD | SLAB_RECLAIM_ACCOUNT,
                            &inode_slab_ctor);

    if (!ext2fs_inode_slab) {
        printk ("could not create slab cache\n");
        return -ENOMEM;
    }

    err = register_filesystem(&ext2fs_fs_type);
    if (err) {
        printk ("cannot register file system, error %d", err);

        kmem_cache_destroy (ext2fs_inode_slab);
        return err;
    }

    return 0;
}

static void __exit ext2fs_exit(void)
{
    /* Ensure all delayed rcu free inodes are flushed before we
     * destroy cache. */
    rcu_barrier();
    kmem_cache_destroy(ext2fs_inode_slab);

    unregister_filesystem(&ext2fs_fs_type);
}

module_init(ext2fs_init);
module_exit(ext2fs_exit);

MODULE_LICENSE("GPL");
MODULE_VERSION(__stringify(EXT2FS_VERSION));
MODULE_AUTHOR("Alex Hixon, Peter Chubb");
MODULE_DESCRIPTION("EXT2FS - ext2 File System");
