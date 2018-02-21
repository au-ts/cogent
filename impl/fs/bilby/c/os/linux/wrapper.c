/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include <linux/init.h>
#include <linux/slab.h>
#include <linux/module.h>
#include <linux/namei.h>
#include <linux/ctype.h>
#include <linux/parser.h>
#include <linux/seq_file.h>
#include <linux/mount.h>
#include <bilbyfs.h>

static int init_inode_by_type(struct backing_dev_info *bdi, struct inode *inode)
{
        int err = 0;

        /* Disable read-ahead */
#if LINUX_VERSION_CODE < KERNEL_VERSION(4,4,0)
        inode->i_mapping->backing_dev_info = bdi;
#endif

        switch (inode->i_mode & S_IFMT) {
        case S_IFREG:
                inode->i_mapping->a_ops = &bilbyfs_file_address_operations;
                inode->i_op = &bilbyfs_file_inode_operations;
                inode->i_fop = &bilbyfs_file_operations;
                break;
        case S_IFDIR:
                inode->i_op  = &bilbyfs_dir_inode_operations;
                inode->i_fop = &bilbyfs_dir_operations;
                inode->i_size = BILBYFS_INODE_SZ;
                break;
        case S_IFLNK:
                inode->i_op = &bilbyfs_symlink_inode_operations;
                break;
        case S_IFBLK:
        case S_IFCHR:
        case S_IFSOCK:
        case S_IFIFO:
                bilbyfs_err("Inode type not yet supported (%x)",
                        (unsigned int)(inode->i_mode & S_IFMT));
                err = -EINVAL;
                break;
        default:
                bilbyfs_err("Unknown inode type. This should not happen!");
                err = -EINVAL;
                break;
        }
        return err;
}

static struct inode *bilbyfs_iget(struct bilbyfs_info *bi, unsigned long inum)
{
        struct inode *inode;
        int err = 0;

        inode = iget_locked(bi->vfs_sb, inum);
        if (!inode)
                return ERR_PTR(-ENOMEM);
        if (!(inode->i_state & I_NEW))
                return inode;
        down(&bi->wd.lock);
        err = fsop_iget(bi, inum, inode);
        up(&bi->wd.lock);
        if (!err) {
                init_inode_by_type(bi->vfs_sb->s_bdi, inode);
                unlock_new_inode(inode);
                return inode;
        }
        bilbyfs_err("BilbyFsError: fsop_iget(ino=%lu) = %d\n", inum, err);
        iget_failed(inode);
        return ERR_PTR(err);
}

static struct dentry *bilbyfs_lookup(struct inode *dir, struct dentry *dentry,
                                     unsigned int flags)
{
        struct bilbyfs_info *bi = dir->i_sb->s_fs_info;
        struct inode *inode;
        ino_t inum;
        int err;

        down(&bi->wd.lock);
        err = fsop_lookup(bi, dir, dentry->d_name.name, &inum);
        up(&bi->wd.lock);
        if (err == -ENOENT) {
                return NULL;
        }
        if (!err) {
                inode = bilbyfs_iget(bi, inum);
                if (!IS_ERR(inode)) {
                        d_add(dentry, inode);
                        return NULL;
                }
                err = PTR_ERR(inode);
        }
        bilbyfs_err("BilbyError: bilbyfs_lookup(dir.ino = %lu, name=%.*s, flags=%x)=%d\n", dir->i_ino, dentry->d_name.len, dentry->d_name.name, flags, err);
        return ERR_PTR(err);
}

/* Allocates and initialises an inode.
 * @dir: pointer to the directory inode, is NULL iff we allocate root.
 * @mode: type + permissions of the inode
 *
 * The function returns a pointer to the inode or a negative error-code.
 */
static struct inode *bilbyfs_new_inode(struct super_block *sb,
                                       struct inode *dir, umode_t mode)
{
        struct inode *inode;
        int err;

        bilbyfs_debug("bilbyfs_new_inode(mode = 0x%x)\n", mode);
        inode = new_inode(sb);
        if (!inode) {
                bilbyfs_err("BilbyFsError: new_inode() = -ENOMEM");
                return ERR_PTR(-ENOMEM);
        }
        /* FIXME: UBIFS has the following line that doesn't seem
         * required, needs to be double checked
         */
        inode->i_mapping->nrpages = 0;
        inode_init_perm(inode, dir, mode);
        err = init_inode_by_type(sb->s_bdi, inode);
        if (!err)
                return inode;
        make_bad_inode(inode);
        iput(inode);
        bilbyfs_err("BilbyFsError: bilbyfs_new_inode(mode = 0x%x) = %d\n", mode, err);
        return ERR_PTR(err);
}

static int bilbyfs_link(struct dentry *old_dentry, struct inode *dir,
                 struct dentry *dentry)
{
        struct bilbyfs_info *bi = dir->i_sb->s_fs_info;
        int err;

        down(&bi->wd.lock);
        err = fsop_link(dir->i_sb->s_fs_info, old_dentry->d_inode, dir, dentry->d_name.name);
        up(&bi->wd.lock);
        if (!err) {
                ihold(old_dentry->d_inode);
                d_instantiate(dentry, old_dentry->d_inode);
        } else
          bilbyfs_err("BilbyFsError: bilbyfs_link() = %d\n", err);
        return err;
}

static int bilbyfs_create(struct inode *dir, struct dentry *dentry,
                          umode_t mode, bool excl)
{
        struct bilbyfs_info *bi = dir->i_sb->s_fs_info;
        struct inode *inode;
        int err;

        bilbyfs_debug("bilbyfs_create (dir.ino = %lu, name=%.*s, mode=%x)\n", dir->i_ino, dentry->d_name.len, dentry->d_name.name, mode);
        inode = bilbyfs_new_inode(dir->i_sb, dir, S_IFREG | mode);
        if (IS_ERR(inode))
                return PTR_ERR(inode);
        down(&bi->wd.lock);
        err = fsop_create(bi, dir, dentry->d_name.name, mode, excl, inode);
        up(&bi->wd.lock);
        if (!err) {
                insert_inode_hash(inode);
                d_instantiate(dentry, inode);
                return 0;
        } else
          bilbyfs_err("BilbyFsError: fsop_create() = %d\n", err);
        make_bad_inode(inode);
        iput(inode);
        return err;
}

static int bilbyfs_unlink(struct inode *dir, struct dentry *dentry)
{
        struct bilbyfs_info *bi = dir->i_sb->s_fs_info;
        int err;

        down(&bi->wd.lock);
        err = fsop_unlink(bi, dir, dentry->d_name.name, dentry->d_inode);
        up(&bi->wd.lock);
        if (err)
          bilbyfs_err("BilbyFsError: fsop_unlink() = %d\n", err);
        return err;
}

static int bilbyfs_rmdir(struct inode *dir, struct dentry *dentry)
{
        struct bilbyfs_info *bi = dir->i_sb->s_fs_info;
        int err;

        down(&bi->wd.lock);
        err = fsop_rmdir(bi, dir, dentry->d_name.name, dentry->d_inode);
        up(&bi->wd.lock);
        if (err)
          bilbyfs_err("BilbyFsError: fsop_rmdir() = %d\n", err);
                
        return err;
}

static int bilbyfs_mkdir(struct inode *dir, struct dentry *dentry, umode_t mode)
{
        struct bilbyfs_info *bi = dir->i_sb->s_fs_info;
        struct inode *inode;
        int err;

        bilbyfs_debug("bilbyfs_mkdir (dir.ino = %lu, name=%.*s, mode=%x)\n", dir->i_ino, dentry->d_name.len, dentry->d_name.name, mode);
        inode = bilbyfs_new_inode(dir->i_sb, dir, S_IFDIR | mode);
        if (IS_ERR(inode))
                return PTR_ERR(inode);
        down(&bi->wd.lock);
        err = fsop_mkdir(bi, dir, dentry->d_name.name, mode, inode);
        up(&bi->wd.lock);
        if (!err) {
                insert_inode_hash(inode);
                d_instantiate(dentry, inode);
                return 0;
        } else
          bilbyfs_err("BilbyFsError: bilbyfs_mkdir() = %d\n", err);
        make_bad_inode(inode);
        iput(inode);
        return err;
}

static int bilbyfs_readdir(struct file *file, struct dir_context *ctx)
{
        struct dentry *dentry = file->f_path.dentry;
        struct inode *dir = dentry->d_inode;
        struct bilbyfs_info *bi = dir->i_sb->s_fs_info;
        int err;

        bilbyfs_debug("bilbyfs_readdir (dir.ino = %lu, name=%.*s, pos=%lld)\n",
                        dir->i_ino, dentry->d_name.len, dentry->d_name.name, ctx->pos);
        if (ctx->pos == 2) /* pos == 2 means an error occured */
                return 0;
        if (ctx->pos < 2) {
                if (!dir_emit_dots(file, ctx))
                        return 0;
                ctx->pos = 3;
        }
        down(&bi->wd.lock);
        err = fsop_readdir(bi, dir, ctx, (struct fsop_readdir_ctx **) &file->private_data);
        up(&bi->wd.lock);
        if (err) {
                bilbyfs_err("BilbyFsError: bilbyfs_readdir() = %d\n", err);
                ctx->pos = 2;
                return err;
        }
        return 0;
}

static int bilbyfs_dir_release(struct inode *dir, struct file *file)
{
        struct bilbyfs_info *bi = dir->i_sb->s_fs_info;
        bilbyfs_debug("bilbyfs_dir_release()\n");
        down(&bi->wd.lock);
        fsop_dir_release((struct fsop_readdir_ctx *)file->private_data);
        up(&bi->wd.lock);
        file->private_data = NULL;
        return 0;
}

static loff_t bilbyfs_dir_llseek(struct file *file, loff_t offset, int origin)
{
        struct inode *inode = file->f_path.dentry->d_inode;
        struct bilbyfs_info *bi = inode->i_sb->s_fs_info;
        int err;
        /* When a directory is seeked 2 thing:
         * - The current bri becomes useless
         * - Seeking a directory is moronic, we do not support
         * FIXME: Check whether not supporting is acceptable
         * The alternative is to ignore, worst case hack something
         * around to emulate.
         */
        bilbyfs_err("Warning: bilbyfs_dir_llseek(), this function is deprecated!");
        down(&bi->wd.lock);
        err = bilbyfs_dir_release(inode, file);
        up(&bi->wd.lock);
        return err;
}

static int bilbyfs_symlink(struct inode *dir, struct dentry *dentry,
                    const char *symname)
{
        struct bilbyfs_info *bi = dir->i_sb->s_fs_info;
        struct inode *inode;
        int err;

        bilbyfs_debug("bilbyfs_symlink (dir.ino = %lu, name=%.*s, symname=%s)\n", dir->i_ino, dentry->d_name.len, dentry->d_name.name, symname);
        inode = bilbyfs_new_inode(dir->i_sb, dir, S_IFLNK | S_IRWXUGO);
        if (IS_ERR(inode))
                return PTR_ERR(inode);
        down(&bi->wd.lock);
        err = fsop_symlink(bi, dir, dentry->d_name.name, symname, inode);
        up(&bi->wd.lock);
        if (!err) {
                insert_inode_hash(inode);
                d_instantiate(dentry, inode);
                return 0;
        } else
          bilbyfs_err("BilbyFsError: bilbyfs_symlink() = %d\n", err);
        make_bad_inode(inode);
        iput(inode);
        return err;
}

static int bilbyfs_rename(struct inode *old_dir, struct dentry *old_dentry,
                          struct inode *new_dir, struct dentry *new_dentry)
{
        struct bilbyfs_info *bi = old_dir->i_sb->s_fs_info;
        int err;

        down(&bi->wd.lock);
        err = fsop_rename(bi, old_dir, old_dentry->d_name.name,
                          old_dentry->d_inode, new_dir, new_dentry->d_name.name,
                          new_dentry->d_inode);
        up(&bi->wd.lock);
        if (err)
          bilbyfs_err("BilbyFsError: bilbyfs_rename() = %d\n", err);
        return err;
}

static int bilbyfs_fsync(struct file *filp, loff_t start, loff_t end, int datasync)
{
        struct inode *inode = filp->f_mapping->host;
        struct bilbyfs_info *bi = inode->i_sb->s_fs_info;
        int err;

        err = filemap_write_and_wait_range(inode->i_mapping, start, end);
        if (!err) {
                down(&bi->wd.lock);
                err = fsop_sync_fs(bi, inode->i_sb, 1);
                up(&bi->wd.lock);
                if (err)
                        bilbyfs_err("BilbyFsError: bilbyfs_fsync() = %d\n", err);
        } else {
                bilbyfs_err("BilbyFsError: filemap_and_wait_range() = %d\n", err);
        }
        return err;
}

static int bilbyfs_readpage(struct file *filp, struct page *page)
{
        struct inode *inode = page->mapping->host;
        struct bilbyfs_info *bi = inode->i_sb->s_fs_info;
        void *addr;
        int err;

        bilbyfs_debug("[0] bilbyfs_readpage(page = %p)\n", page);
        addr = kmap(page);
        down(&bi->wd.lock);
        err = fsop_readpage(bi, inode, page->index, addr);
        up(&bi->wd.lock);
        if (err == -ENOENT) {
                 SetPageChecked(page);
                 err = 0;
        }
        if (err) {
                ClearPageUptodate(page);
                SetPageError(page);
                flush_dcache_page(page);
                kunmap(page);
                unlock_page(page);
                bilbyfs_err("BilbyFsError: bilbyfs_readpage() = %d\n", err);
                return err;
        }
        SetPageUptodate(page);
        ClearPageError(page);
        flush_dcache_page(page);
        kunmap(page);
        unlock_page(page);
        bilbyfs_debug("[2] bilbyfs_readpage() = %d\n", 0);
        return 0;
}

static int bilbyfs_write_begin(struct file *filp, struct address_space *mapping,
                               loff_t pos, unsigned len, unsigned flags,
                               struct page **pagep, void **fsdata)
{
        struct page *page;
        struct inode *inode = mapping->host;
        struct bilbyfs_info *bi = inode->i_sb->s_fs_info;
        pgoff_t block = pos >> BILBYFS_BLOCK_SHIFT;
        void *addr;
        int err = 0;

        bilbyfs_debug("[0] bilbyfs_write_begin()\n");
        page = grab_cache_page_write_begin(mapping, block, flags);
        if (!page)
                return -ENOMEM;

        addr = kmap(page);

        if (!PageUptodate(page)) { /* overwriting data */
                /* FIXME: optimisation, check whether the entire page is gonna be
                 * overwritten and set PageChecked accordingly
                 */
                down(&bi->wd.lock);
                err = fsop_write_begin(bi, inode, pos, len, addr);
                up(&bi->wd.lock);
                if (err) {
                        ClearPageUptodate(page);
                        SetPageError(page);
                        kunmap(page);
                        unlock_page(page);
                        page_cache_release(page);
                        bilbyfs_err("BilbyFsError: bilbyfs_write_begin() = %d\n", err);
                        return err;
                }
        }
        SetPageUptodate(page);
        ClearPageError(page);
        kunmap(page);
        *pagep = page;
        bilbyfs_debug("[2] bilbyfs_write_begin() = 0\n");
        return 0;
}

static int bilbyfs_write_end(struct file *filp, struct address_space *mapping,
                             loff_t pos, unsigned len, unsigned copied,
                             struct page *page, void *fsdata)
{
        struct inode *inode = mapping->host;
        struct bilbyfs_info *bi = inode->i_sb->s_fs_info;
        void *addr;
        int err;

        bilbyfs_debug("[S] bilbyfs_write_end()\n");
        BUG_ON(!PageUptodate(page));
        /* if len > PAGE_CACHE_SIZE then some data hasn't been copied by
         * bilbyfs
         */
        if (copied < len) {
                /* Something went wrong VFS did not copy all data initially
                 * announced in write_begin.
                 * FIXME Is returning 0 really asking VFS to retry?
                 * FIXME Or should we just write the provided data ?
                 */
                /* 23/10/2013: This can safely be ignored because BilbyFs
                 * always read a PAGE_CACHE_SIZE data block in write_begin
                 * which means that as long as @len is < PAGE_CACHE_SIZE
                 * we have read enough data.
                 * FIXME: Can this ever happen without concurrency?
                 */
                bilbyfs_debug("copied < len : %u < %u. But it's safe to ignore as write_begin read %lu bytes.\n",
                              copied, len, PAGE_CACHE_SIZE);
                /* return 0; */
        }
        addr = kmap(page);
        down(&bi->wd.lock);
        err = fsop_write_end(bi, inode, pos, copied, addr);
        up(&bi->wd.lock);
        if (!err) {
                kunmap(page);
                unlock_page(page);
                page_cache_release(page);
                bilbyfs_debug("[1] bilbyfs_write_end() = %d\n", copied);
                return copied;
        }
        SetPageError(page);
        kunmap(page);
        unlock_page(page);
        page_cache_release(page);
        bilbyfs_err("BilbyFsError: bilbyfs_write_end() = %d\n", err);
        return err;
}

static int bilbyfs_write_end_writeback(struct file *filp, struct address_space *mapping,
                                       loff_t pos, unsigned len, unsigned copied,
                                       struct page *page, void *fsdata)
{
        struct inode *inode = mapping->host;
        loff_t end_pos = pos + len;
        int appending = !!(end_pos > inode->i_size);

        bilbyfs_assert(PAGE_CACHE_SIZE == BILBYFS_BLOCK_SIZE);
        bilbyfs_debug("[S] bilbyfs_write_end_writeback(pos = %llu, len =%u, copied = %u)\n",pos, len, copied);
        BUG_ON(!PageUptodate(page));
        bilbyfs_assert(len <= PAGE_CACHE_SIZE);
        if (copied < len) {
                /* 23/10/2013: This can safely be ignored because BilbyFs
                 * always read a PAGE_CACHE_SIZE data block in write_begin
                 * which means that as long as @len is < PAGE_CACHE_SIZE
                 * we have read enough data.
                 * FIXME: Can this ever happen without concurrency?
                 */
                bilbyfs_debug("copied < len : %u < %u. But it's safe to ignore as write_begin read %lu bytes.\n",
                              copied, len, PAGE_CACHE_SIZE);
        }
        __set_page_dirty_nobuffers(page);
        if (appending) {
                i_size_write(inode, end_pos);
                /*
                 * Note, we do not set @I_DIRTY_PAGES (which means that the
                 * inode has dirty pages), this has been done in
                 * '__set_page_dirty_nobuffers()'.
                 */
                __mark_inode_dirty(inode, I_DIRTY_DATASYNC);
        }
        unlock_page(page);
        page_cache_release(page);
        bilbyfs_debug("[1] bilbyfs_write_end_writeback() = %d (nb bytes copied)\n", copied);
        return copied;
}

static int bilbyfs_writepage(struct page *page, struct writeback_control *wbc)
{
        struct inode *inode = page->mapping->host;
        struct bilbyfs_info *bi = inode->i_sb->s_fs_info;
        loff_t i_size =  i_size_read(inode);
        pgoff_t end_index = i_size >> PAGE_CACHE_SHIFT;
        loff_t pos = page->index << PAGE_CACHE_SHIFT;
        int err, len = i_size & (PAGE_CACHE_SIZE - 1);
        void *kaddr;

        bilbyfs_debug("bilbyfs_writepage()\n");

        /* Is the page fully outside @i_size? (truncate in progress) */
        if (page->index > end_index || (page->index == end_index && !len)) {
                unlock_page(page);
                return 0;
        }
        bilbyfs_debug("write-to-disk\n");
        if (page->index != end_index)
                len = PAGE_CACHE_SIZE;
        set_page_writeback(page);
        kaddr = kmap_atomic(page);
        memset(kaddr + len, 0, PAGE_CACHE_SIZE - len);
        flush_dcache_page(page);
        kunmap_atomic(kaddr);

        kaddr = kmap(page);
        down(&bi->wd.lock);
        err = fsop_write_end(bi, inode, pos, len, kaddr);
        up(&bi->wd.lock);
        kunmap(page);
        unlock_page(page);
        end_page_writeback(page);

        if (err)
                bilbyfs_err("BilbyFsError: bilbyfs_writepage() = %d\n", err);
        return err;
}

#if LINUX_VERSION_CODE < KERNEL_VERSION(4,2,0)
static void *bilbyfs_follow_link(struct dentry *dentry, struct nameidata *nd)
{
        struct bilbyfs_info *bi = dentry->d_inode->i_sb->s_fs_info;
        struct inode *inode = dentry->d_inode;
        int err;

        bilbyfs_debug("bilbyfs_follow_link() \n");
        if (!inode->i_private) {
                inode->i_private = kmalloc(PATH_MAX);
                if (!inode->i_private)
                        return ERR_PTR(-ENOMEM);

                down(&bi->wd.lock);
                err = fsop_follow_link(bi, dentry->d_inode, inode->i_private);
                up(&bi->wd.lock);
                if (err) {
                        bilbyfs_err("BilbyFsError: bilbyfs_follow_link() = %d\n", err);
                        kfree(inode->i_private);
                        return ERR_PTR(err);
                }
        }
        nd_set_link(nd, inode->i_private);
        return NULL;
}
#else
const char *bilbyfs_get_link(struct dentry *dentry, struct inode *inode,
                             struct delayed_call *done)
{
        struct wrapper_data *wd = dentry->d_inode->i_sb->s_fs_info;
        int err;
        const char *link = page_get_link(dentry, inode, done);

        bilbyfs_debug("bilbyfs_get_link() \n");
        if (!IS_ERR(link) && !*link) {
                do_delayed_call(done);
                clear_delayed_call(done);
                link = ERR_PTR(-ENOENT);
        }

        return link;
}
#endif

static int bilbyfs_setattr(struct dentry *dentry, struct iattr *attr)
{
        struct inode *inode = dentry->d_inode;
        struct bilbyfs_info *bi = inode->i_sb->s_fs_info;
        int err;

        bilbyfs_debug("bilbyfs_setattr(ino %lu, mode %#x, ia_valid %#x)\n",
                inode->i_ino, inode->i_mode, attr->ia_valid);
#if LINUX_VERSION_CODE > KERNEL_VERSION(3,16,0)
        err = setattr_prepare(dentry, attr);
#else
        err = inode_change_ok(inode, attr);
#endif

        if (err)
                return err;

        if (attr->ia_valid & ATTR_MODE) {
                if (!in_group_p(inode->i_gid) && !capable(CAP_FSETID))
                        attr->ia_mode &= ~S_ISGID;
        }

        down(&bi->wd.lock);
        err = fsop_setattr(bi, inode, attr);
        up(&bi->wd.lock);
        if (err) {
                bilbyfs_err("BilbyFsError: fsop_setattr() = %d\n", err);
                return err;
        }
        /* truncate_setsize calls i_size_write and frees pages in the
         * page cache */
        if (attr->ia_valid & ATTR_SIZE)
                truncate_setsize(inode, inode->i_size);
        if (attr->ia_valid & ATTR_ATIME)
                inode->i_atime = timespec_trunc(inode->i_atime,
                                                inode->i_sb->s_time_gran);
        if (attr->ia_valid & ATTR_MTIME)
                inode->i_mtime = timespec_trunc(inode->i_mtime,
                                                inode->i_sb->s_time_gran);
        if (attr->ia_valid & ATTR_CTIME)
                inode->i_ctime = timespec_trunc(inode->i_ctime,
                                                inode->i_sb->s_time_gran);
        return 0;
}


#if LINUX_VERSION_CODE < KERNEL_VERSION(4,4,0)
static int bilbyfs_getattr(struct vfsmount *mnt, struct dentry *dentry,
                           struct kstat *stat)
{
       struct inode *inode = dentry->d_inode;
       struct bilbyfs_info *bi = inode->i_sb->s_fs_info;
       int err; 

       down(&bi->wd.lock);
       err = fsop_getattr(bi, inode, stat);
       up(&bi->wd.lock);
       if (!err) {
               stat->dev = dentry->d_sb->s_dev;
               stat->rdev = inode->i_rdev;
       } else {
               bilbyfs_err("BilbyFsError: fsop_getattr = %d", err);
       }
       return err;
}
#else
int bilbyfs_getattr(const struct path *path, struct kstat *stat,
                    u32 mask, unsigned int flags)
{
        struct dentry *dentry = path->dentry;
        struct inode *inode = d_inode(dentry);
        int err;
       down(&bi->wd.lock);
       err = fsop_getattr(bi, inode, stat);
       up(&bi->wd.lock);
       if (!err) {
               stat->dev = dentry->d_sb->s_dev;
               stat->rdev = inode->i_rdev;
       } else {
               bilbyfs_err("BilbyFsError: fsop_getattr = %d", err);
       }
       return err;
}
#endif

const struct file_operations bilbyfs_file_operations =
{
        .llseek =       generic_file_llseek,
        .open =         generic_file_open,
#if LINUX_VERSION_CODE < KERNEL_VERSION(4,0,0)
        .read =         new_sync_read,
        .write =        new_sync_write,
#endif
        .read_iter =    generic_file_read_iter,
        .write_iter =   generic_file_write_iter,
        .mmap =         generic_file_readonly_mmap,
        .fsync =        bilbyfs_fsync,
        .splice_read =  generic_file_splice_read,
};

const struct inode_operations bilby_file_inode_operations =
{
        .setattr =      bilbyfs_setattr,
};

const struct inode_operations bilbyfs_symlink_inode_operations = {
#if LINUX_VERSION_CODE < KERNEL_VERSION(4,4,0)
        .readlink    = generic_readlink,
        .follow_link = bilbyfs_follow_link,
#else
        .get_link = bilbyfs_get_link,
#endif
        .setattr     = bilbyfs_setattr,
        .getattr     = bilbyfs_getattr,
};


const struct inode_operations bilbyfs_file_inode_operations = {
        .setattr     = bilbyfs_setattr,
        .getattr     = bilbyfs_getattr,
};

const struct inode_operations bilbyfs_dir_inode_operations = {
        .lookup      = bilbyfs_lookup,
        .create      = bilbyfs_create,
        .link        = bilbyfs_link,
        .symlink     = bilbyfs_symlink,
        .unlink      = bilbyfs_unlink,
        .mkdir       = bilbyfs_mkdir,
        .rmdir       = bilbyfs_rmdir,
        .rename      = bilbyfs_rename,
        .setattr     = bilbyfs_setattr,
/*
        .mknod       = bilbyfs_mknod,
*/
        .getattr     = bilbyfs_getattr,
};

const struct file_operations bilbyfs_dir_operations = {
        .llseek         = bilbyfs_dir_llseek,
        .release        = bilbyfs_dir_release,
        .fsync          = bilbyfs_fsync,
        .read           = generic_read_dir,
        .iterate        = bilbyfs_readdir,
};

const struct address_space_operations bilbyfs_file_address_operations =
{
        .readpage =     bilbyfs_readpage,
        .write_begin =  bilbyfs_write_begin,
#ifdef NOWRITEBACK
        .write_end =    bilbyfs_write_end,
#else
        .writepage  =   bilbyfs_writepage,
        .write_end  =   bilbyfs_write_end_writeback,
#endif
};

static int bilbyfs_statfs(struct dentry *dentry, struct kstatfs *kstat)
{
        struct bilbyfs_info *bi = dentry->d_inode->i_sb->s_fs_info;
        int err;

        down(&bi->wd.lock);
        err = fsop_statfs(bi, kstat);
        up(&bi->wd.lock);
        return err;
}

static int bilbyfs_sync_fs(struct super_block *sb, int wait)
{
        struct bilbyfs_info *bi = sb->s_fs_info;
        int err;

        down(&bi->wd.lock);
        err = fsop_sync_fs(bi, sb, wait);
        up(&bi->wd.lock);
        if (err)
          bilbyfs_err("BilbyFsError: bilbyfs_link() = %d\n", err);
        return err;
}

/**
 * bilbyfs_unmount - unmount BilbyFs
 * @bi: global fs info
 *
 */
static void bilbyfs_unmount(struct bilbyfs_info *bi)
{
        bilbyfs_debug("bilbyfs_unmount()\n");
        down(&bi->wd.lock);
        fsop_unmount(bi);
        up(&bi->wd.lock);
}

static void bilbyfs_put_super(struct super_block *sb)
{
        struct bilbyfs_info *bi = sb->s_fs_info;

        bilbyfs_msg("unmount UBI device %d, volume %d", bi->vi.ubi_num,
                  bi->vi.vol_id);

        bilbyfs_debug("bilbyfs_put_super()\n");
        bilbyfs_unmount(bi);
#if LINUX_VERSION_CODE < KERNEL_VERSION(4,4,0)
        bdi_destroy(sb->s_bdi);
#endif
        ubi_close_volume(bi->ubi); /* FIXME: This should be in umount */
}

/**
 * open_ubi - parse UBI device name string and open the UBI device.
 * @name: UBI volume name
 * @mode: UBI volume open mode
 *
 * The primary method of mounting BilbyFs is by specifying the UBI volume
 * character device node path. However, BilbyFs may also be mounted withoug any
 * character device node using one of the following methods:
 *
 * o ubiX_Y    - mount UBI device number X, volume Y;
 * o ubiY      - mount UBI device number 0, volume Y;
 * o ubiX:NAME - mount UBI device X, volume with name NAME;
 * o ubi:NAME  - mount UBI device 0, volume with name NAME.
 *
 * Alternative '!' separator may be used instead of ':' (because some shells
 * like busybox may interpret ':' as an NFS host name separator). This function
 * returns UBI volume description object in case of success and a negative
 * error code in case of failure.
 */
struct ubi_volume_desc *open_ubi(const char *name, int mode)
{
        struct ubi_volume_desc *ubi;
        int dev, vol;
        char *endptr;

        /* First, try to open using the device node path method */
        ubi = ubi_open_volume_path(name, mode);
        if (!IS_ERR(ubi))
                return ubi;

        /* Try the "nodev" method */
        if (name[0] != 'u' || name[1] != 'b' || name[2] != 'i')
                return ERR_PTR(-EINVAL);

        /* ubi:NAME method */
        if ((name[3] == ':' || name[3] == '!') && name[4] != '\0')
                return ubi_open_volume_nm(0, name + 4, mode);

        if (!isdigit(name[3]))
                return ERR_PTR(-EINVAL);

        dev = simple_strtoul(name + 3, &endptr, 0);

        /* ubiY method */
        if (*endptr == '\0')
                return ubi_open_volume(0, dev, mode);

        /* ubiX_Y method */
        if (*endptr == '_' && isdigit(endptr[1])) {
                vol = simple_strtoul(endptr + 1, &endptr, 0);
                if (*endptr != '\0')
                        return ERR_PTR(-EINVAL);
                return ubi_open_volume(dev, vol, mode);
        }

        /* ubiX:NAME method */
        if ((*endptr == ':' || *endptr == '!') && endptr[1] != '\0')
                return ubi_open_volume_nm(dev, ++endptr, mode);

        return ERR_PTR(-EINVAL);
}

enum {
        BilbyFs_Opt_no_summary,
        BilbyFs_Opt_compr,
        BilbyFs_Opt_end,
};

static const match_table_t bilbyfs_options = {
        {BilbyFs_Opt_no_summary, "no_summary"},
        {BilbyFs_Opt_compr, "compr=%s"},
        {BilbyFs_Opt_end, NULL},
};

static int bilbyfs_parse_options(struct bilbyfs_info *bi, char *options)
{
        char *s;
        substring_t args[MAX_OPT_ARGS];

        if (!options)
                return 0;

        while ((s = strsep(&options, ",")) && *s) {
                int opt;

                opt = match_token(s, bilbyfs_options, args);
                switch (opt) {
                case BilbyFs_Opt_no_summary:
                        bi->no_summary = 1;
                        bilbyfs_err("BilbyFs option: no_summary\n");
                        break;
                case BilbyFs_Opt_compr:
                        bilbyfs_err("BilbyFs option: compr=%%s ignored (No compression)\n");
                        break;
                default:
                {
                        bilbyfs_err("unreconized mount option \"%s\"\n", s);
                        return -EINVAL;
                }
                }
        }
        return 0;
}


static int bilbyfs_fill_super(struct super_block *sb, void *options, int silent, char *bd_name)
{
        struct bilbyfs_info *bi = sb->s_fs_info;
        struct inode *root;
        ino_t rootino;
        int err;

        err = bilbyfs_parse_options(bi, options);
        if (err)
                return err;
        /*
         * Disabling VFS's read-ahead feature.
         * Read-ahead will be disabled because bdi->ra_pages is 0.
         */
#if LINUX_VERSION_CODE < KERNEL_VERSION(4,12,0)
        sb->s_bdi = &bi->wd.bdi;
        sb->s_bdi->name = "bilbyfs";
        sb->s_bdi->capabilities = BDI_CAP_MAP_COPY;
        err = bdi_init(sb->s_bdi);
        if (!err) {
                err = bdi_register(sb->s_bdi, NULL, bd_name);
                if (!err) {
                        sb->s_fs_info = bi;
                        root = bilbyfs_new_inode(sb, NULL, S_IFDIR | S_IRUGO | S_IWUSR | S_IXUGO);
                        if (root) {
                                set_nlink(root, 2);
                                down(&bi->wd.lock);
                                err = fsop_fill_super(bi, sb, silent, &rootino, root);
                                up(&bi->wd.lock);
                                iput(root);
                        } else {
                                err = PTR_ERR(root);
                        }

                        if (!err) {
                                /* Reads the root inode */
                                root = bilbyfs_iget(bi, rootino);
                                if (!IS_ERR(root)) {
                                        sb->s_root = d_make_root(root);
                                        if (sb->s_root)
                                                return 0;
                                        err = -EINVAL;
                                } else {
                                        err = PTR_ERR(root);
                                }
                                bilbyfs_unmount(bi);
                        }
                        bdi_destroy(sb->s_bdi);
                }
        }
#else
        super_setup_bdi(sb);
        sb->s_fs_info = wd;
        root = bilbyfs_new_inode(sb, NULL, S_IFDIR | S_IRUGO | S_IWUSR | S_IXUGO);
        if (root) {
                set_nlink(root, 2);
                err = ffsop_fill_super(wd, sb, silent, root);
                iput(root);
        } else {
                err = PTR_ERR(root);
        }

        if (!err) {
                /* Reads the root inode */
                root = bilbyfs_iget(wd, root->i_ino);
                if (!IS_ERR(root)) {
                        sb->s_root = d_make_root(root);
                        if (sb->s_root)
                                return 0;
                        err = -EINVAL;
                } else {
                        err = PTR_ERR(root);
                }
                bilbyfs_unmount(wd);
        }
#endif
        sb->s_bdi = NULL;
        return err;
}

static int sb_test(struct super_block *sb, void *data)
{
        struct bilbyfs_info *bi = sb->s_fs_info;
        int err;

        down(&bi->wd.lock);
        err = fsop_test_is_mount(data, bi);
        up(&bi->wd.lock);
        return err;
}

static int sb_set(struct super_block *sb, void *data)
{
        sb->s_fs_info = data;
        return set_anon_super(sb, NULL);
}

static const struct super_operations bilbyfs_super_operations;

/**
 * bilbyfs_mount: mount the file system
 * @fs_type: Linux file system type reference
 * @flags: MS_* flags (MS_RDONLY, MS_NOATIME, ...)
 * @name: name of the ubi volume to mount
 * @data: private pointer to store some fs specific data
 */
struct dentry *bilbyfs_mount(struct file_system_type *fs_type, int flags,
                             const char *name, void *data)
{
        struct bilbyfs_info *bi;
        struct super_block *sb;
        char bd_name[BILBYFS_BD_MAX_NLEN];
        int err;

        bilbyfs_err("Mounting BilbyFs %s, flags %#x\n", name, flags);
        bi = kzalloc(sizeof(struct bilbyfs_info));
        if (bi) {
                wrapper_init(&bi->wd);
                down(&bi->wd.lock);
                err = fsop_init(bi, name, bd_name);
                up(&bi->wd.lock);
                if (!err) {
                        sb = sget(fs_type, sb_test, sb_set, flags, bi);
                        if (!IS_ERR(sb)) {
                                /* 'fill_super()' opens ubi again so we must close it here */
                                if (sb->s_root) {
                                        kfree(bi);
                                        /* A new mount point for already mounted BilbyFs */
                                        return dget(sb->s_root);
                                } else {
                                        sb->s_flags = flags;
                                        sb->s_op = &bilbyfs_super_operations;
                                        err = bilbyfs_fill_super(sb, data,
                                                !!(flags & MS_SILENT), bd_name);
                                        if (!err) {
                                                /* We do not support atime */
                                                sb->s_flags |= MS_ACTIVE | MS_NOATIME;
                                                bilbyfs_debug("bilbyfs_mount() = %d\n", err);
                                                return dget(sb->s_root);
                                        }
                                        deactivate_locked_super(sb);
                                }
                        } else {
                                err = PTR_ERR(sb);
                                kfree(bi);
                        }
                }
        } else {
                err = -ENOMEM;
        }
        bilbyfs_debug("bilbyfs_mount() = %d\n", err);
        return ERR_PTR(err);
}

/**
 * bilbyfs_kill_super: free linux super block instance.
 * @sb: Linux super block reference
 */
void bilbyfs_kill_super(struct super_block *sb)
{
        struct bilbyfs_info *bi = sb->s_fs_info;

        bilbyfs_debug("bilbyfs_kill_super()\n");
        kill_anon_super(sb);
        down(&bi->wd.lock);
        fsop_clean(bi);
        up(&bi->wd.lock);
        kfree(bi);
}

struct kmem_cache *bilbyfs_inode_slab;

static struct inode *bilbyfs_alloc_inode(struct super_block *sb)
{
        struct bilbyfs_inode *binode;

        binode = kmem_cache_alloc(bilbyfs_inode_slab, GFP_NOFS);
        if (!binode)
                return NULL;

        memset((void *)binode + sizeof(struct inode), 0,
               sizeof(struct bilbyfs_inode) - sizeof(struct inode));
        return &binode->vfs_inode;
}

static void bilbyfs_free_inode(struct rcu_head *head)
{
        struct inode *inode = container_of(head, struct inode, i_rcu);
        struct bilbyfs_inode *binode = inode_to_binode(inode);

        bilbyfs_debug("bilbyfs_free_inode(ino = %lu)\n", inode->i_ino);
        kmem_cache_free(bilbyfs_inode_slab, binode);
}

static void bilbyfs_destroy_inode(struct inode *inode)
{
        bilbyfs_debug("bilbyfs_destroy_inode(ino=%lu)\n", inode->i_ino);
        kfree(inode->i_private);
        inode->i_private = NULL;

        call_rcu(&inode->i_rcu, bilbyfs_free_inode);
}

static void bilbyfs_evict_inode(struct inode *inode)
{
        struct bilbyfs_info *bi = inode->i_sb->s_fs_info;

        bilbyfs_debug("bilbyfs_evict_inode(ino = %lu)\n", inode->i_ino);
        bilbyfs_assert(!atomic_read(&inode->i_count));

        truncate_inode_pages(&inode->i_data, 0);
        if (!is_bad_inode(inode)) {
                down(&bi->wd.lock);
                fsop_evict_inode(bi, inode);
                up(&bi->wd.lock);
        }
        clear_inode(inode);
}

struct timespec inode_current_time(struct inode *inode)
{
        return current_time(inode);
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

static struct file_system_type bilbyfs_fs_type = {
        .name    = "bilbyfs",
        .owner   = THIS_MODULE,
        .mount   = bilbyfs_mount,
        .kill_sb = bilbyfs_kill_super,
};

/*
 * Inode slab cache constructor.
 */
static void inode_slab_ctor(void *obj)
{
        struct bilbyfs_inode *bi = obj;
        inode_init_once(&bi->vfs_inode);
}

static int __init bilbyfs_init(void)
{
        int err;

        /* Make sure node sizes are 8-byte aligned (BILBYFS_OBJ_PADDING) */
        BUILD_BUG_ON((BILBYFS_OBJ_PADDING - 1) != 7);
        BUILD_BUG_ON(BILBYFS_CH_SZ      & 7);
        BUILD_BUG_ON(BILBYFS_INODE_SZ   & 7);
        BUILD_BUG_ON(BILBYFS_DENTARR_SZ & 7);
        BUILD_BUG_ON(BILBYFS_DATA_SZ    & 7);
        BUILD_BUG_ON(BILBYFS_DATA_SZ    & 7);
        BUILD_BUG_ON(BILBYFS_MAX_DATA_SZ & 7);
        BUILD_BUG_ON(BILBYFS_MAX_DENTARR_SZ & 7);
        BUILD_BUG_ON(BILBYFS_SUPER_SZ    & 7);

        BUILD_BUG_ON(BILBYFS_FIRST_SQNUM <= 0);
        BUILD_BUG_ON(BILBYFS_FIRST_INO <= 0);
        BUILD_BUG_ON(BILBYFS_ROOT_INO >= BILBYFS_FIRST_INO);

        /* Ensuring SUP_LNUM < LOG_FST_LNUM */
        BUILD_BUG_ON(BILBYFS_SUP_LNUM >= BILBYFS_LOG_FST_LNUM);

        /* All obj types fit in 3 bits */
        BUILD_BUG_ON(BILBYFS_OBJ_TYPES_CNT > 7);

        BUILD_BUG_ON(PAGE_CACHE_SIZE != BILBYFS_BLOCK_SIZE);
        BUILD_BUG_ON(PAGE_CACHE_SHIFT != BILBYFS_BLOCK_SHIFT);

        bilbyfs_inode_slab = kmem_cache_create("bilbyfs_inode_slab",
                                sizeof(struct bilbyfs_inode), 0,
                                SLAB_MEM_SPREAD | SLAB_RECLAIM_ACCOUNT,
                                &inode_slab_ctor);
        if (!bilbyfs_inode_slab)
                return -ENOMEM;

        err = register_filesystem(&bilbyfs_fs_type);
        if (err) {
                bilbyfs_err("cannot register file system, error %d", err);
                kmem_cache_destroy(bilbyfs_inode_slab);
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

