/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include <linux/version.h>
#include <bilbyfs.h>

#if LINUX_VERSION_CODE >= KERNEL_VERSION(5,0,0)
#include <uapi/linux/mount.h>
#endif

/**
 * bilbyfs_set_inode_flags - set VFS inode flags.
 * @inode: VFS inode to set flags for
 *
 * This function propagates flags from BilbyFs inode object to VFS inode object.
 */
static void bilbyfs_set_inode_flags(struct inode *inode)
{
        unsigned int flags = inode_to_binode(inode)->flags;

        /* The orphan flag is only for BilbyFs internal behaviour */
        inode->i_flags &= ~(S_APPEND | S_IMMUTABLE);
        if (flags & BILBYFS_APPEND_FL)
                inode->i_flags |= S_APPEND;
        if (flags & BILBYFS_IMMUTABLE_FL)
                inode->i_flags |= S_IMMUTABLE;
}

/**
 * bilbyfs_ro_mode - set read-only flag to prevent further damage to an inconsistent
 * medium.
 *
 * @bi: global fs info
 *
 */
void bilbyfs_ro_mode(struct bilbyfs_info *bi)
{
        bi->is_ro = 1;
}

/**
 * validate_inode - validate inode.
 * @bi: global fs info
 * @inode: the inode to validate
 *
 * This is a helper function for 'bilbyfs_iget()' which validates various fields
 * of a newly built inode to make sure they contain sane values and prevent
 * possible vulnerabilities. Returns zero if the inode is all right and
 * a non-zero error code if not.
 */
static int validate_inode(struct bilbyfs_info *bi, const struct inode *inode)
{
        if (inode->i_size > BILBYFS_MAX_FILE_SZ) {
                bilbyfs_err("inode is too large (%lld)",
                          (long long)inode->i_size);
                return -EINVAL;
        }
        /* FIXME: presumably we need a lot more checks than that */
        return 0;
}

int fsop_iget(struct bilbyfs_info *bi, unsigned long inum, struct inode *inode)
{
        struct bilbyfs_inode *binode;
        struct obj_inode ino;
        obj_id id;
        int err;

        bilbyfs_debug("fsop_iget()\n");
        binode = inode_to_binode(inode);

        id = inode_id_init(inum);
        err = ostore_read_obj(bi, id, &ino, BILBYFS_INODE_SZ);
        if (!err) {
                unpack_obj_inode(inode, &ino);
                err = validate_inode(bi, inode);
                if (!err)
                        bilbyfs_set_inode_flags(inode);
        } else {
                bilbyfs_err("Failed to read inode %lu, error %d, activate read-only mode\n", inum, err);
                bilbyfs_ro_mode(bi);
                return err;
        }
        return err;
}

/* dir_lookup_nm: lookup a name in a directory inode
 * @dir: directory inode
 * @name: name to lookup
 * @dent: directory entry object to store the result in
 *
 * The function uses dentarr_lookup_nm to find a name in a directory and stores
 * the directory entry in @dent. It returns 0, if the name was found, %-ENOENT
 * if the name was not found and a negative error code otherwise.
 */
static int dir_lookup_nm(struct bilbyfs_info *bi, struct inode *dir,
                         const char *name, struct obj_dentry *dent)
{
        struct obj_dentarr *dentarr;
        struct obj_dentry *de;
        obj_id id;
        int err = 0;

        id = dentarr_id_init(dir->i_ino, name);
        dentarr = dentarr_read(bi, id);
        if (IS_ERR(dentarr))
                return PTR_ERR(dentarr);
        de = dentarr_lookup_nm(bi, dentarr, name);
        if (!IS_ERR(de))
                memcpy(dent, de, obj_dentry_size(de));
        else
                err = PTR_ERR(de);
        kfree(dentarr);
        return err;
}

int fsop_lookup(struct bilbyfs_info *bi, struct inode *dir,
                const char *name, ino_t *ino)
{
        struct obj_dentry *dent;
        int err;

        bilbyfs_debug("bilbyfs_lookup(dir.i_ino=%lu, name=%s)\n", dir->i_ino, name);
        if (strlen(name) > BILBYFS_MAX_NLEN)
                return -ENAMETOOLONG;

        dent = kmalloc(BILBYFS_MAX_DENTRY_SZ);
        if (!dent)
                return -ENOMEM;

        err = dir_lookup_nm(bi, dir, name, dent);
        if (!err)
                *ino = dent->ino;
        kfree(dent);
        return err;
}

static int trans_commit_inodes(struct bilbyfs_info *bi, struct inode *dir,
                               struct inode *inode, void **obj_list, int count,
                               int osw_flag)
{
        struct obj_inode inode_obj, dir_obj;

        pack_obj_inode(&inode_obj, inode);
        obj_list[count] = &inode_obj;
        count++;

        pack_obj_inode(&dir_obj, dir);
        obj_list[count] = &dir_obj;
        count++;

        return ostore_write_obj_list(bi, obj_list, count, osw_flag);
}


int fsop_link(struct bilbyfs_info *bi, struct inode *inode, struct inode *dir,
              const char *name)
{
        struct timespec64 mtime, ctime;
        struct obj_dentarr *dentarr;
        obj_id id;
        int sz_change;
        int err;
        void *obj_list[3];

        bilbyfs_debug("fsop_link()\n");
        if (bi->is_ro)
                return -EROFS;

        id = dentarr_id_init(dir->i_ino, name);
        dentarr = dentarr_read_or_create(bi, id);
        if (IS_ERR(dentarr))
                return PTR_ERR(dentarr);

        sz_change = dentarr_add_dentry(bi, dentarr, inode, name);
        if (sz_change >= 0) {
                obj_list[0] = dentarr;

                inc_nlink(inode);
                inode->i_ctime = inode_current_time(inode);

                mtime = dir->i_mtime;
                ctime = dir->i_ctime;
                dir->i_size += sz_change;
                dir->i_ctime = inode->i_ctime;
                dir->i_mtime = inode->i_ctime;

                err = trans_commit_inodes(bi, dir, inode, obj_list, 1, OSW_NONE);
                if (err) {
                        if (err == -ENOSPC)
                                bilbyfs_err("Not enough space");
                        dir->i_size -= sz_change;
                        dir->i_mtime = mtime;
                        dir->i_ctime = ctime;
                        drop_nlink(inode);
                }
        } else {
                err = sz_change;
        }
        kfree(dentarr);
        return err;
}


/* Initialises an inode.
 * @dir: pointer to the directory inode, is NULL iff we allocate root.
 * @mode: type + permissions of the inode
 *
 * The function returns zero or a negative error-code.
 */
static int init_inode(struct bilbyfs_info *bi, struct inode *dir,
                      struct inode *inode, umode_t mode)
{
        struct bilbyfs_inode *binode = inode_to_binode(inode);

        bilbyfs_debug("bilbyfs_init_inode(mode = 0x%x)\n", mode);
        binode->flags = 0;

        /*
         * Set 'S_NOCMTIME' to prevent VFS form updating [mc]time of inodes and
         * marking them dirty in file write path (see 'file_update_time()').
         * BilbyFs has to fully control "clean <-> dirty" transitions of inodes
         * to make budgeting work.
         */
        inode->i_flags |= S_NOCMTIME;

        inode_init_perm(inode, dir, mode);
        inode->i_ctime = inode_current_time(inode);
        inode->i_atime = inode->i_ctime;
        inode->i_mtime = inode->i_ctime;

        set_nlink(inode, 1);
        bilbyfs_set_inode_flags(inode);
        if (dir == NULL) { /* Only root doesn't have a parent */
                inode->i_ino = BILBYFS_ROOT_INO;
                binode->creat_sqnum = next_sqnum(bi);
                set_nlink(inode, 2);
                return 0;
        } else if (bi->next_inum < BILBYFS_LAST_INUM) {
                inode->i_ino = next_inum(bi);
                binode->creat_sqnum = next_sqnum(bi);
                return 0;
        }
        bilbyfs_err("Running out of inode numbers\n");
        return -ENFILE;
}

int fsop_create(struct bilbyfs_info *bi, struct inode *dir, const char *name,
                umode_t mode, int excl, struct inode *inode)
{
        struct timespec64 mtime, ctime;
        struct obj_dentarr *dentarr;
        obj_id id;
        int sz_change;
        int err;
        void *obj_list[3];

        bilbyfs_debug("fsop_create (dir.ino = %lu, name=%s, mode=%x)\n", dir->i_ino, name, mode);
        if (bi->is_ro)
                return -EROFS;

        err = init_inode(bi, dir, inode, S_IFREG | mode);
        if (err)
                return err;
        id = dentarr_id_init(dir->i_ino, name);
        dentarr = dentarr_read_or_create(bi, id);
        if (IS_ERR(dentarr))
                return PTR_ERR(dentarr);

        sz_change = dentarr_add_dentry(bi, dentarr, inode, name);
        if (sz_change >= 0) {
                obj_list[0] = dentarr;

                mtime = dir->i_mtime;
                ctime = dir->i_ctime;
                dir->i_size += sz_change;
                dir->i_mtime = inode->i_ctime;
                dir->i_ctime = inode->i_ctime;

                err = trans_commit_inodes(bi, dir, inode, obj_list, 1, OSW_NONE);
                if (err) {
                        if (err == -ENOSPC)
                                bilbyfs_err("Not enough space to create the file %s\n", name);
                        dir->i_size -= sz_change;
                        dir->i_mtime = mtime;
                        dir->i_ctime = ctime;
                }
        } else {
                err = sz_change;
        }
        kfree(dentarr);
        return err;
}

int fsop_unlink(struct bilbyfs_info *bi, struct inode *dir, const char *name,
                struct inode *inode)
{
        struct bilbyfs_inode *binode = inode_to_binode(inode);
        struct obj_dentarr *dentarr;
        obj_id id;
        int sz_change;
        int err;
        unsigned int saved_nlink = inode->i_nlink;
        void *obj_list[3];

        bilbyfs_debug("fsop_unlink(%s)\n", name);
        if (bi->is_ro)
                return -EROFS;

        id = dentarr_id_init(dir->i_ino, name);
        dentarr = dentarr_read(bi, id);
        if (IS_ERR(dentarr))
                return PTR_ERR(dentarr);

        sz_change = dentarr_del_dentry(bi, dentarr, name);
        if (sz_change >= 0) {
                obj_list[0] = dentarr;

                inode->i_ctime = inode_current_time(dir);
                drop_nlink(inode);
                /* Every inode is an orphan in time window between
                 * unlink and evict_inode */
                if (inode->i_nlink == 0)
                        binode->flags |= BILBYFS_ORPHAN_FL;
                dir->i_size -= sz_change;
                dir->i_ctime = inode->i_ctime;
                dir->i_mtime = inode->i_ctime;

                err = trans_commit_inodes(bi, dir, inode, obj_list, 1, OSW_DEL);
                if (err) {
                        dir->i_size += sz_change;
                        set_nlink(inode, saved_nlink);
                }
        } else {
                err = sz_change;
        }
        kfree(dentarr);
        return err;
}

/* check_dir_empty: checks whether a directory is empty
 * @bi: global fs info
 * @dir: inode of the directory to check
 *
 * This function returns 0 if the directory is empty.
 * Otherwise a negative error-code is returned.
 */
static int check_dir_empty(struct bilbyfs_info *bi, struct inode *dir)
{
        struct fsop_readdir_ctx rdx;
        int err = 0;

        rdx_init(bi, &rdx, dir->i_ino);
        if (rdx_next_dentry(bi, &rdx) != ERR_PTR(-ENOENT))
                 err = -ENOTEMPTY;
        rdx_clean(&rdx);
        return err;
}

int fsop_rmdir(struct bilbyfs_info *bi, struct inode *dir, const char *name,
               struct inode *inode)
{
        struct bilbyfs_inode *binode = inode_to_binode(inode);
        struct timespec64 mtime, ctime;
        struct obj_dentarr *dentarr;
        obj_id id;
        int sz_change;
        int err;
        void *obj_list[3];

        bilbyfs_debug("fsop_rmdir()\n");
        if (bi->is_ro)
                return -EROFS;

        err = check_dir_empty(bi, inode);
        if (err)
                return err;

        id = dentarr_id_init(dir->i_ino, name);
        dentarr = dentarr_read(bi, id);
        if (IS_ERR(dentarr))
                return PTR_ERR(dentarr);

        sz_change = dentarr_del_dentry(bi, dentarr, name);
        if (sz_change >= 0) {
                obj_list[0] = dentarr;

                inode->i_ctime = inode_current_time(dir);
                clear_nlink(inode);
                /* the inode is orphan until it gets evicted by the VFS layer */
                binode->flags |= BILBYFS_ORPHAN_FL;
                drop_nlink(dir);
                dir->i_size -= sz_change;
                mtime = dir->i_mtime;
                ctime = dir->i_ctime;
                dir->i_ctime = inode->i_ctime;
                dir->i_mtime = inode->i_ctime;

                err = trans_commit_inodes(bi, dir, inode, obj_list, 1, OSW_DEL);
                if (err) { 
                        dir->i_size += sz_change;
                        dir->i_mtime = mtime;
                        dir->i_ctime = ctime;
                        inc_nlink(dir);
                        set_nlink(inode, 2);
                }
        } else {
                err = sz_change;
        }
        kfree(dentarr);
        return err;
}

int fsop_mkdir(struct bilbyfs_info *bi, struct inode *dir, const char *name,
               umode_t mode, struct inode *inode)
{
        struct timespec64 mtime, ctime;
        struct obj_dentarr *dentarr;
        obj_id id;
        int sz_change;
        int err;
        void *obj_list[3];

        bilbyfs_debug("fsop_mkdir (dir.ino = %lu, name=%s, mode=%x)\n", dir->i_ino, name, mode);
        if (bi->is_ro)
                return -EROFS;

        err = init_inode(bi, dir, inode, S_IFDIR | mode);
        if (err)
                return err;
        id = dentarr_id_init(dir->i_ino, name);
        dentarr = dentarr_read_or_create(bi, id);
        if (IS_ERR(dentarr))
                return PTR_ERR(dentarr);
        sz_change = dentarr_add_dentry(bi, dentarr, inode, name);
        if (sz_change >= 0) {
                obj_list[0] = dentarr;
                
                inc_nlink(inode);
                inc_nlink(dir);
                dir->i_size += sz_change;
                mtime = dir->i_mtime;
                ctime = dir->i_ctime;
                dir->i_mtime = inode->i_ctime;
                dir->i_ctime = inode->i_ctime;
                
                err = trans_commit_inodes(bi, dir, inode, obj_list, 1, OSW_NONE);
                if (err) {
                        if (err == -ENOSPC)
                                bilbyfs_err("Not enough space\n");
                        dir->i_size -= sz_change;
                        dir->i_mtime = mtime;
                        dir->i_ctime = ctime;
                        drop_nlink(dir);
                }
        } else {
                err = sz_change;
        }
        kfree(dentarr);
        return err;
}

/**
 * vfs_dent_type - get VFS directory entry type.
 * @type: BilbyFs directory entry type
 *
 * This function converts BilbyFs directory entry type into VFS directory entry
 * type.
 */
static unsigned int vfs_dent_type(uint8_t type)
{
        switch (type) {
        case BILBYFS_ITYPE_REG:
                return DT_REG;
        case BILBYFS_ITYPE_DIR:
                return DT_DIR;
        case BILBYFS_ITYPE_LNK:
                return DT_LNK;
        case BILBYFS_ITYPE_BLK:
                return DT_BLK;
        case BILBYFS_ITYPE_CHR:
                return DT_CHR;
        case BILBYFS_ITYPE_FIFO:
                return DT_FIFO;
        case BILBYFS_ITYPE_SOCK:
                return DT_SOCK;
        default:
                bilbyfs_assert(0);
        }
        return 0;
}

int fsop_readdir(struct bilbyfs_info *bi, struct inode *dir, struct dir_context *ctx, struct fsop_readdir_ctx **rdx)
{
        struct obj_dentry *dent;
        int len, err;

        if (!*rdx) {
                *rdx = kmalloc(BILBYFS_MAX_READDIR_DATA_SIZE);
                if (!*rdx)
                        return -ENOMEM;
                rdx_init(bi, *rdx, dir->i_ino);
        }
        /*
        if (ctx->pos == 2) {
                bilbyfs_debug("fsop_gc()\n");
                err = gc_garbage_collect(bi);
                bilbyfs_debug("gc err=%d\n", err);
        } */

        bilbyfs_debug("fsop_readdir (dir.ino = %lu, pos=%llu)\n", dir->i_ino, ctx->pos);
        for (dent = rdx_next_dentry(bi, *rdx); !IS_ERR(dent); dent = rdx_next_dentry(bi, *rdx)) {
                ctx->pos += 1;
                len = le16_to_cpu(dent->nlen);
                bilbyfs_debug("fsop_readdir (%s, pos=%llu)\n", dent->name, ctx->pos);
                if (!dir_emit(ctx, dent->name, len, le64_to_cpu(dent->ino), vfs_dent_type(dent->type)))
                        return 0;
        }
        err = PTR_ERR(dent);
        if (err == -ENOENT) {
                ctx->pos = 2;
                return 0;
        }
        return err;
}

void fsop_dir_release(struct fsop_readdir_ctx *rdx)
{
        if (rdx)
                rdx_clean(rdx);
        kfree(rdx);
}

int fsop_symlink(struct bilbyfs_info *bi, struct inode *dir, const char *name,
                 const char *symname, struct inode *inode)
{
        struct timespec64 mtime, ctime;
        struct obj_dentarr *dentarr;
        obj_id id;
        struct obj_data *data;
        int sz_data = strlen(symname);
        int sz_obj_data = obj_data_size_with_data(sz_data);
        int sz_change;
        int err;
        void *obj_list[4];

        bilbyfs_debug("fsop_symlink()\n");

        if (bi->is_ro)
                return -EROFS;

        if (sz_obj_data > BILBYFS_MAX_DATA_SZ)
                return -ENAMETOOLONG;
        err = init_inode(bi, dir, inode,  S_IFLNK | S_IRWXUGO);
        if (err)
                return err;

        id = dentarr_id_init(dir->i_ino, name);
        dentarr = dentarr_read_or_create(bi, id);
        if (IS_ERR(dentarr))
                return PTR_ERR(dentarr);
        sz_change = dentarr_add_dentry(bi, dentarr, inode, name);
        if (sz_change >= 0) {
                obj_list[0] = dentarr;

                data = kmalloc(BILBYFS_MAX_DATA_SZ);
                if (data) {
                        id = data_id_init(inode->i_ino, 0);
                        pack_obj_data(data, id, sz_data, symname);
                        obj_list[1] = data;
			inode->i_link = NULL;
                        inode->i_size = sz_obj_data;
                        dir->i_size += sz_change;
                        /* We don't undo the next line??? */
                        mtime = dir->i_mtime;
                        ctime = dir->i_ctime;
                        dir->i_mtime = inode->i_ctime;
                        dir->i_ctime = inode->i_ctime;
                        err = trans_commit_inodes(bi, dir, inode, obj_list, 2, OSW_NONE);
                        if (err) {
                                dir->i_size -= sz_change;
                                dir->i_mtime = mtime;
                                dir->i_ctime = ctime;
                        }
                        kfree(data);
                } else {
                        err = -ENOMEM;
                }
        } else {
                err = sz_change;
        }
        kfree(dentarr);
        return err;
}

#define DENTARR_CACHE_SZ 2
static struct obj_dentarr *get_dentarr_cache(struct bilbyfs_info *bi, obj_id id,
                                             struct obj_dentarr **cache)
{
        int i;

        for (i = 0; i < DENTARR_CACHE_SZ; i++)
                if (cache[i] && le64_to_cpu(cache[i]->id) == id)
                        return cache[i];
        for (i = 0; i < DENTARR_CACHE_SZ; i++)
                if (!cache[i]) {
                        cache[i] = dentarr_read_or_create(bi, id);
                        return cache[i];
                }
        bilbyfs_assert(0);
        return NULL;
}

static void free_dentarr_cache(struct bilbyfs_info *bi, struct obj_dentarr **cache)
{
        int i;

        for (i = 0; i < DENTARR_CACHE_SZ; i++)
               kfree(cache[i]);
}

static int bilbyfs_do_rename(struct bilbyfs_info *bi, struct inode *old_dir,
                             const char *old_name, struct inode *old_inode,
                             struct inode *new_dir, const char *new_name,
                             struct inode *new_inode)
{

        struct obj_dentarr *old_dentarr, *new_dentarr, *cache[DENTARR_CACHE_SZ] = {0};
        obj_id old_dentarr_id, new_dentarr_id;
        int old_sz_change, new_sz_change = 0;
        struct obj_inode old_dir_obj, new_dir_obj, old_inode_obj, new_inode_obj;
        struct bilbyfs_inode *binode;
        int err;
        void *obj_list[6];
        int count = 0;

        // Delete the old dentry and create new dentry
        old_dentarr_id = dentarr_id_init(old_dir->i_ino, old_name);
        new_dentarr_id = dentarr_id_init(new_dir->i_ino, new_name);

        old_dentarr = get_dentarr_cache(bi, old_dentarr_id, cache);
        new_dentarr = get_dentarr_cache(bi, new_dentarr_id, cache);
        if (IS_ERR(old_dentarr) || IS_ERR(new_dentarr)) {
                free_dentarr_cache(bi, cache);
                if (IS_ERR(old_dentarr))
                        return PTR_ERR(old_dentarr);
                return PTR_ERR(new_dentarr);
        }

        old_sz_change = dentarr_del_dentry(bi, old_dentarr, old_name);
        if (new_inode)
                new_sz_change = dentarr_del_dentry(bi, new_dentarr, new_name);
        err = dentarr_add_dentry(bi, new_dentarr, old_inode, new_name);
        if (old_sz_change < 0 || new_sz_change < 0 || err < 0) {
                free_dentarr_cache(bi, cache);
                if (old_sz_change < 0)
                        return old_sz_change;
                else if (new_sz_change < 0)
                        return new_sz_change;
                else
                        return err;
        }
        new_sz_change = err - new_sz_change;

        // Update inode info
        old_dir->i_size -= old_sz_change;
        new_dir->i_size += new_sz_change;

        // Write objects into disk
        obj_list[count] = old_dentarr;
        count++;
        if (le64_to_cpu(old_dentarr->id) != le64_to_cpu(new_dentarr->id)) {
                obj_list[count] = new_dentarr;
                count++;
        }

        pack_obj_inode(&old_dir_obj, old_dir);
        obj_list[count] = &old_dir_obj;
        count++;
        if (new_inode) {
                binode = inode_to_binode(new_inode);
                binode->flags |= BILBYFS_ORPHAN_FL;
                pack_obj_inode(&new_inode_obj, new_inode);
                obj_list[count] = &new_inode_obj;
                count++;
        }

        pack_obj_inode(&new_dir_obj, new_dir);
        obj_list[count] = &new_dir_obj;
        count++;
        pack_obj_inode(&old_inode_obj, old_inode);
        obj_list[count] = &old_inode_obj;
        count++;

        err = ostore_write_obj_list(bi, obj_list, count, OSW_NONE);

        free_dentarr_cache(bi, cache);
        return err;
}

int fsop_rename(struct bilbyfs_info *bi, struct inode *old_dir,
                const char *old_name, struct inode *old_inode,
                struct inode *new_dir, const char *new_name,
                struct inode *new_inode)
{
        int old_inode_is_dir = S_ISDIR(old_inode->i_mode);
        int new_inode_is_dir = new_inode && S_ISDIR(new_inode->i_mode);
        int unlink_new = !!new_inode;
        struct inode *bak;
        int err;

        bilbyfs_debug("bilbyfs_rename(%s -> %s)\n", old_name, new_name);

        if (bi->is_ro)
                return -EROFS;

        if (new_inode_is_dir) {
                err = check_dir_empty(bi, new_inode);
                if (err)
                        return err;
        }

        bak = kmalloc(sizeof(*bak) * 4);
        if (!bak)
                return -ENOMEM;
        memcpy(&bak[0], old_dir, sizeof(*bak));
        memcpy(&bak[1], old_inode, sizeof(*bak));
        memcpy(&bak[2], new_dir, sizeof(*bak));
        if (unlink_new)
                memcpy(&bak[3], new_inode, sizeof(*bak));

        if (unlink_new) {
                if (new_inode_is_dir) {
                        clear_nlink(new_inode);
                        drop_nlink(new_dir);
                } else {
                        drop_nlink(new_inode);
                }
        }
        if (old_inode_is_dir) {
                drop_nlink(old_dir);
                inc_nlink(new_dir);
        }
        old_inode->i_ctime = inode_current_time(old_inode);
        old_dir->i_mtime = old_inode->i_ctime;
        old_dir->i_ctime = old_inode->i_ctime;

        err = bilbyfs_do_rename(bi, old_dir, old_name, old_inode, new_dir,
                                new_name, new_inode);
        if (err) {
                memcpy(old_dir, &bak[0], sizeof(*bak));
                memcpy(old_inode, &bak[1], sizeof(*bak));
                memcpy(new_dir, &bak[2], sizeof(*bak));
                if (unlink_new)
                        memcpy(new_inode, &bak[3], sizeof(*bak));
        }
        kfree(bak);
        return err;
}

static int read_block(struct bilbyfs_info *bi, struct inode *inode, void *addr,
                      int block)
{
        struct obj_data *odata = bi->odata;
        obj_id id;
        int size;
        int err;

        id = data_id_init(inode->i_ino, block);
        err = ostore_read_obj(bi, id, odata, BILBYFS_MAX_DATA_SZ);
        if (err) {
                if (err != -ENOENT)
                        return err;
                /* We are hitting a hole */
                memset(addr, 0, BILBYFS_BLOCK_SIZE);
                return 0;
        }
        size = le32_to_cpu(odata->size);
        if (size < 0 || size > BILBYFS_BLOCK_SIZE) {
                bilbyfs_err("bad data object (block %d, inode %lu)",
                            block, inode->i_ino);
                return -EINVAL;
        }
        memcpy(addr, odata->data, size);
        memset(addr + size, 0, BILBYFS_BLOCK_SIZE - size);
        return 0;
}

int fsop_readpage(struct bilbyfs_info *bi, struct inode *inode, pgoff_t block, void *addr)
{
        pgoff_t limit = i_size_read(inode) >> BILBYFS_BLOCK_SHIFT;
        int err;

        bilbyfs_assert(PAGE_SIZE == BILBYFS_BLOCK_SIZE);
        bilbyfs_assert(PAGE_SHIFT == BILBYFS_BLOCK_SHIFT);
        bilbyfs_debug("[S] bilbyfs_readpage(block=%lu, limit=%lu)\n", block, limit);
        if (block > limit) {
                memset(addr, 0, PAGE_SIZE);
                return -ENOENT;
        }
        if (block == limit && (i_size_read(inode) % BILBYFS_BLOCK_SIZE == 0))
          /* FIXME Not sure if the condition above is possible with VFS interface. */
                return 0;
        err = read_block(bi, inode, addr, block);
        if (err) {
                bilbyfs_err("fsop_readpage() = %d, (block=%lu,limit=%lu,ino.size=%llu)\n",
                            err, block, limit, i_size_read(inode));
        }
        return err;
}

int fsop_write_begin(struct bilbyfs_info *bi, struct inode *inode, int pos,
                     int len, void *addr)
{
        int err;

        if (bi->is_ro)
                return -EROFS;

        bilbyfs_assert(len <= PAGE_SIZE);
        bilbyfs_debug("[S] fsop_write_begin()\n");
        err = fsop_readpage(bi, inode, pos >> BILBYFS_BLOCK_SHIFT, addr);
        if (err == -ENOENT)
                 err = 0;
        return err;
}

int fsop_write_end(struct bilbyfs_info *bi, struct inode *inode, int pos,
                   int len, void *addr)
{
        pgoff_t block = pos >> BILBYFS_BLOCK_SHIFT;
        uint32_t start = pos & (PAGE_SIZE - 1);
        unsigned int end = start + len;
        unsigned int inode_size;
        struct timespec64 mtime;
        struct obj_inode ino;
        obj_id id;
        int err;
        void *obj_list[2];

        if (bi->is_ro)
                return -EROFS;

        bilbyfs_debug("[S] fsop_write_end()\n");
        inode_size = i_size_read(inode);
        if (pos + len > inode_size) /* appending data: update inode.size */
                i_size_write(inode, pos + len);
        mtime = inode->i_mtime;
        inode->i_mtime = inode_current_time(inode);
        pack_obj_inode(&ino, inode);
        obj_list[0] = &ino;

        id = data_id_init(inode->i_ino, block);
        pack_obj_data(bi->odata, id, end, addr);
        obj_list[1] = bi->odata;
        err = ostore_write_obj_list(bi, obj_list, 2, OSW_NONE);
        if (err) {
                inode->i_mtime = mtime;
                i_size_write(inode, inode_size);
        }
        return err;
}

int fsop_follow_link(struct bilbyfs_info *bi, struct inode *inode, char *path)
{
        bilbyfs_debug("fsop_follow_link()\n");
        bilbyfs_assert(PATH_MAX >= BILBYFS_BLOCK_SIZE);
        return read_block(bi, inode, path, 0);
}

static int fsop_write_inode(struct bilbyfs_info *bi, struct inode *inode)
{
        struct obj_inode ino;
        void *obj_list[1];

        pack_obj_inode(&ino, inode);
        obj_list[0] = &ino;

        return ostore_write_obj_list(bi, obj_list, 1, OSW_NONE);
}

static int fsop_truncate(struct bilbyfs_info *bi, struct inode *inode,
                         struct iattr *attr)
{
        loff_t old_size, new_size, new_aligned_size;
        struct timespec64 ctime, mtime;
        struct obj_inode ino;
        struct obj_del del;
        void *data;
        pgoff_t block;
        obj_id id;
        void *obj_list[3];
        int count = 0;
        int err;
        int osw_flag = 0;

        // Update inode info
        old_size = i_size_read(inode);
        new_size = attr->ia_size;
        mtime = inode->i_mtime;
        ctime = inode->i_ctime;
        inode->i_ctime = inode_current_time(inode);
        inode->i_mtime = inode->i_ctime;
        inode->i_size = new_size;

        // Rewrite the last partially written block to disk
        new_aligned_size = ALIGN(new_size, BILBYFS_BLOCK_SIZE);
        if (new_size != new_aligned_size && new_size < old_size) {
                data = kmalloc(BILBYFS_BLOCK_SIZE);
                if (!data)
                        return -ENOMEM;
                block = new_size >> BILBYFS_BLOCK_SHIFT;
                err = fsop_readpage(bi, inode, block, data);
                if (err) {
                        kfree(data);
                        return err;
                }
                id = data_id_init(inode->i_ino, block);
                pack_obj_data(bi->odata, id, new_size - (new_aligned_size - BILBYFS_BLOCK_SIZE), data);
                obj_list[count] = bi->odata;
                count++;
                kfree(data);
        }

        // Deletion object
        if (new_aligned_size < old_size) {
                block = new_aligned_size >> BILBYFS_BLOCK_SHIFT;
                id = data_id_init(inode->i_ino, block);
                pack_obj_del(&del, id);
                obj_list[count] = &del;
                count++;
                osw_flag = OSW_DEL;
        }

        // Write objects
        pack_obj_inode(&ino, inode);
        obj_list[count] = &ino;
        count++;

        err = ostore_write_obj_list(bi, obj_list, count, osw_flag);
        if (err) {
                i_size_write(inode, old_size);
                inode->i_mtime = mtime;
                inode->i_ctime = ctime;
                return err;
        }
        return 0;
}

/**
 * FIXME:
 * Here again UBIFS does not do an immediate rollback
 * I wouldn't be surprise if their trick is to evict the
 * inode from the cache when there is an error.
 */
static int fsop_do_setattr(struct bilbyfs_info *bi, struct inode *inode,
                           struct iattr *attr)
{
        struct inode ibackup;
        umode_t mode = attr->ia_mode;
        int err;

        memcpy(&ibackup, inode, sizeof(ibackup));
        if (attr->ia_valid & ATTR_UID)
                inode->i_uid = attr->ia_uid;
        if (attr->ia_valid & ATTR_GID)
                inode->i_gid = attr->ia_gid;
        if (attr->ia_valid & ATTR_ATIME)
                inode->i_atime = attr->ia_atime;
        if (attr->ia_valid & ATTR_MTIME)
                inode->i_mtime = attr->ia_mtime;
        if (attr->ia_valid & ATTR_CTIME)
                inode->i_ctime = attr->ia_ctime;
        if (attr->ia_valid & ATTR_MODE)
                inode->i_mode = mode;

        err = fsop_write_inode(bi, inode);
        if (err)
                memcpy(inode, &ibackup, sizeof(ibackup));
        return err;
}

int fsop_setattr(struct bilbyfs_info *bi, struct inode *inode, struct iattr *attr)
{
        int err;

        bilbyfs_debug("fsop_setattr(ino %lu, mode %#x, ia_valid %#x)\n",
                inode->i_ino, inode->i_mode, attr->ia_valid);
        if (bi->is_ro)
                return -EROFS;
        if ((attr->ia_valid & ATTR_SIZE))
                err = fsop_truncate(bi, inode, attr);
        else
                err = fsop_do_setattr(bi, inode, attr);
        bilbyfs_debug("fsop_setattr() = %d\n", err);
        return err;
}

int fsop_getattr(struct bilbyfs_info *bi, struct inode *inode,
                 struct kstat *stat)
{
        loff_t size;
 
        bilbyfs_debug("fsop_getattr()\n");
        
        stat->ino = inode->i_ino;
        stat->mode = inode->i_mode;
        stat->nlink = inode->i_nlink;
        stat->uid = inode->i_uid;
        stat->gid = inode->i_gid;
        stat->size = inode->i_size;
        stat->atime = inode->i_atime;
        stat->mtime = inode->i_mtime;
        stat->ctime = inode->i_ctime;
        stat->blksize = BILBYFS_BLOCK_SIZE;

        /*
         * Unfortunately, the 'stat()' system call was designed for block
         * device based file systems, and it is not appropriate for BilbyFs,
         * because BilbyFs does not have notion of "block". For example, it is
         * difficult to tell how many block a directory takes - it actually
         * takes less than 300 bytes, but we have to round it to block size,
         * which introduces large mistake. This makes utilities like 'du'
         * report completely senseless numbers. This is the reason why BilbyFs
         * goes the same way as UBIFS and JFFS2 - it reports zero blocks for
         * everything but regular files, which makes more sense than reporting
         * completely wrong sizes.
         */
        if (S_ISREG(inode->i_mode)) {
                size = ALIGN(stat->size, BILBYFS_BLOCK_SIZE);
                /* stat->blocks assumes a block size of 512 bytes */
                stat->blocks = size / 512;
        } else
                stat->blocks = 0;
        return 0;
}

void fsop_evict_inode(struct bilbyfs_info *bi, struct inode *inode)
{
        int err;
        obj_id id;
        struct obj_del del;
        void *obj_list[1];

        bilbyfs_debug("fsop_evict_inode()\n");
        if (bi->is_ro) {
                bilbyfs_debug("Cannot evit inode, FS mounted read-only\n");
                return ;
        }

        if (!inode->i_nlink) {
                /* Delete inode + children objects */
                id = inode_id_init(inode->i_ino);
                pack_obj_del(&del, id);
                obj_list[0] = &del;
                err = ostore_write_obj_list(bi, obj_list, 1, OSW_NONE);

                if (err)
                        /*
                         * Worst case we did not let FSM know that an orphan
                         * is now completely deleted, we simly print an error msg
                         * as it only prevents GC from using the dirty space
                         * left by the orphan inode.
                         * This space will be available again next time we scan
                         * the disk to build FSM data.
                         * FIXME: Can we return an error?
                         */
                        bilbyfs_err("fsop_evict_inode(): can't delete inode %lu, error %d",
                                    inode->i_ino, err);
        }
}

int fsop_statfs(struct bilbyfs_info *bi, struct kstatfs *kstat)
{
        unsigned long long free;
        unsigned long long avail;
        __le32 *uuid = (__le32 *)bi->super.uuid;

        free = ostore_get_free_space(bi);
        avail = ostore_get_available_space(bi);
        bilbyfs_debug("fsop_statfs(): free space %llu bytes (%llu blocks), available space %llu bytes (%llu blocks)",
                free, free >> BILBYFS_BLOCK_SHIFT, avail, avail >> BILBYFS_BLOCK_SHIFT);

        kstat->f_type = BILBYFS_SUPER_MAGIC;
        kstat->f_bsize = BILBYFS_BLOCK_SIZE;
        kstat->f_blocks = bi->super.leb_size * bi->super.leb_cnt;
        kstat->f_blocks /= BILBYFS_BLOCK_SIZE;
        bilbyfs_debug("leb_cnt = %llu, bytes = %llu, blocks = %llu\n", (u64) bi->super.leb_cnt, (u64) (bi->super.leb_size * bi->super.leb_cnt),
                      kstat->f_blocks);
        kstat->f_bfree = free >> BILBYFS_BLOCK_SHIFT;
        kstat->f_bavail = avail >> BILBYFS_BLOCK_SHIFT;
        bilbyfs_debug("freeblocks = %llu, availblocks = %llu\n", (u64) kstat->f_bfree, (u64) kstat->f_bavail);
        kstat->f_files = 0;
        kstat->f_ffree = 0;
        kstat->f_namelen = BILBYFS_MAX_NLEN;
        kstat->f_fsid.val[0] = le32_to_cpu(uuid[0]) ^ le32_to_cpu(uuid[2]);
        kstat->f_fsid.val[1] = le32_to_cpu(uuid[1]) ^ le32_to_cpu(uuid[3]);
        bilbyfs_assert(kstat->f_bfree <= kstat->f_blocks);
        bilbyfs_assert(kstat->f_bavail <= kstat->f_bfree);
        return 0;
}

int fsop_sync_fs(struct bilbyfs_info *bi, struct super_block *sb, int wait)
{
        int err;
        /*
         * Zero @wait is just an advisory thing to help the file system shove
         * lots of data into the queues, and there will be the second
         * '->sync_fs()' call, with non-zero @wait.
         */
        if (!wait)
                return 0;
        bilbyfs_debug("BilbyFs fsop_sync\n");
        err = ostore_sync(bi, false);
        if (err)
                return err;
        /* FIXME: BTW what is ubi_sync? */
        return ubi_sync(bi->vi.ubi_num);
}

static int fsop_format_default(struct bilbyfs_info *bi, struct inode *root)
{
        int err;

        bilbyfs_err("Empty flash memory detected, we format it with BilbyFs\n");
        if (bi->is_ro)
                return -EROFS;
        err = init_inode(bi, NULL, root, S_IFDIR | S_IRUGO | S_IWUSR | S_IXUGO);
        if (err)
                return err;

        err = ostore_write_super(bi);
        if (!err)
                err = fsop_write_inode(bi, root);
        return err;
}

int fsop_fill_super(struct bilbyfs_info *bi, struct super_block *sb, int silent,
                    ino_t *rootino, struct inode *root)
{
        int err;

        bi->vfs_sb = sb; /* FIXME remove vfs_sb ? */
        /* Re-open the UBI device in read-write mode */
        bi->ubi = ubi_open_volume(bi->vi.ubi_num, bi->vi.vol_id, UBI_READWRITE);
        if (!IS_ERR(bi->ubi)) {
                sb->s_magic = BILBYFS_SUPER_MAGIC;
                sb->s_blocksize = BILBYFS_BLOCK_SIZE;
                sb->s_blocksize_bits = BILBYFS_BLOCK_SHIFT;
                sb->s_maxbytes = MAX_LFS_FILESIZE;

                /* FIXME Kill this max_io_size for max_write_size...
                 * See UBI doc. */
                bi->super.leb_cnt = bi->vi.size;
                bi->super.nb_reserved_gc = BILBYFS_DEFAULT_NB_RESERVED_GC;
                bi->super.nb_reserved_del = BILBYFS_DEFAULT_NB_RESERVED_DEL;
                bi->super.leb_size = bi->vi.usable_leb_size;
                bi->super.min_io_size = bi->di.min_io_size;
                bi->super.max_io_size = bi->di.max_write_size;
                bi->super.sqnum = 0;
                bi->super.lowest_sqnum = 0;
                bi->is_ro = sb->s_flags & MS_RDONLY;

                bi->super_offs = 0;
                err = ostore_init(bi);
                if (!err) {
                        err = ostore_mount(bi);
                        if (err == -ENODATA) { /* Flash was empty let format */
                                err = fsop_format_default(bi, root);
                        }
                        if (!err) {
                                if (!silent) {
                                        bilbyfs_msg("mounted UBI device %d, volume %d, "
                                                    "name \"%s\"", bi->vi.ubi_num,
                                                    bi->vi.vol_id, bi->vi.name);
                                }
                                *rootino = BILBYFS_ROOT_INO;
                                return 0;
                        }
                }
                ubi_close_volume(bi->ubi);
        } else {
                err = PTR_ERR(bi->ubi);
                bilbyfs_err("Could not open UBI device %d volume %d.",
                            bi->vi.ubi_num, bi->vi.vol_id);
        }
        return err;
}

int fsop_test_is_mount(struct bilbyfs_info *bi1, struct bilbyfs_info *bi2)
{
        return bi1->vi.cdev == bi2->vi.cdev;
}

int fsop_init(struct bilbyfs_info *bi, const char *name, char *bd_name)
{
        struct ubi_volume_desc *ubi;
        int sz;

        bilbyfs_debug("fsop_init()\n");
        bi->odata = kmalloc(BILBYFS_MAX_DATA_SZ);
        if (!bi->odata)
                return -ENOMEM;
        /*
         * Get UBI device number and volume ID. Mount it read-only so far
         * because this might be a new mount point, and UBI allows only one
         * read-write user at a time.
         */
        ubi = open_ubi(name, UBI_READONLY);
        if (IS_ERR(ubi)) {
                bilbyfs_err("cannot open \"%s\", error %d",
                          name, (int)PTR_ERR(ubi));
                kfree(bi->odata);
                return PTR_ERR(ubi);
        }

        bi->next_sqnum = BILBYFS_FIRST_SQNUM;
        bi->next_inum = BILBYFS_FIRST_INO;
        bi->is_ro = 1;
        ubi_get_volume_info(ubi, &bi->vi);
        ubi_get_device_info(bi->vi.ubi_num, &bi->di);
        sz  = snprintf(bd_name, BILBYFS_BD_MAX_NLEN,
                       "bilbyfs_%d_%d", bi->vi.ubi_num, bi->vi.vol_id);
        if (sz < BILBYFS_BD_MAX_NLEN) {
                ubi_close_volume(ubi);
                return 0;
        }
        bilbyfs_err("backing device name buffer is too small\n");
        ubi_close_volume(ubi);
        kfree(bi->odata);
        return -EINVAL;
}

void fsop_unmount(struct bilbyfs_info *bi)
{
        bilbyfs_debug("fsop_unmount()\n");
        if (!bi->is_ro)
                ostore_unmount(bi);
        ostore_clean(bi);
        bi->is_ro = 1;
        kfree(bi->odata);
        /*ubi_close_volume(bi->ubi); */
}

void fsop_clean(struct bilbyfs_info *bi)
{
        bilbyfs_debug("fsop_clean()\n");
}
