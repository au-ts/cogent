/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */
/*
 * abstract_vfs.h
 * This file contains the abstract VFS data type definitions.
 */


#ifndef _ABSTRACT_VFS_H
#define _ABSTRACT_VFS_H

/* inode operations */
struct cogent_inode_operations {
        int lookup;
        int get_link;
        int permission;

        int readlink;

        int create;
        int link;
        int unlink;
        int symlink;
        int mkdir;
        int rmdir;
        int mknod;
        int rename;
        int setattr;
        int listxattr;
        int fiemap;
        int update_time;
        int atomic_open;
        int tmpfile;
        int set_acl;
};

/* file operations */
struct cogent_file_operations {
        int llseek;
        int read;
        int write;
        int read_iter;
        int write_iter;
        int iterate;
        int iterate_shared;
        int poll;
        int unlocked_ioctl;
        int compat_ioctl;
        int mmap;
        int open;
        int flush;
        int release;
        int fsync;
        int fasync;
        int lock;
        int sendpage;
        int get_unmapped_area;
        int check_flags;
        int flock;
        int splice_write;
        int splice_read;
        int setlease;
        int fallocate;
        int show_fdinfo;
#ifndef CONFIG_MMU
        int mmap_capabilities;
#endif
        int copy_file_range;
        int clone_file_range;
        int dedupe_file_range;
};

/* super operations */
struct cogent_super_operations {
        int alloc_inode;
        int destroy_inode;

        int dirty_inode;
        int write_inode;
        int drop_inode;
        int evict_inode;
        int put_super;
        int sync_fs;
        int freeze_super;
        int freeze_fs;
        int thaw_super;
        int unfreeze_fs;
        int statfs;
        int remount_fs;
        int umount_begin;

        int show_options;
        int show_devname;
        int show_path;
        int show_stats;
#ifdef CONFIG_QUOTA
        int quota_read;
        int quota_write;
        int get_dquots;
#endif
        int bdev_try_to_free_page;
        int nr_cached_objects;
        int free_cached_objects;
};

#endif  /* _ABSTRACT_VFS_H */
