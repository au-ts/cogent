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

struct obj_dentry *dentarr_first_dentry(struct obj_dentarr *dentarr)
{
        if (le32_to_cpu(dentarr->nb_dentry) == 0)
                return NULL;
        return (void *)dentarr + BILBYFS_DENTARR_SZ;
}

static struct obj_dentry *dentarr_end(struct obj_dentarr *dentarr)
{
        return ((void *)dentarr + obj_dentarr_size(dentarr));
}

struct obj_dentry *dentarr_next_dentry(struct obj_dentarr *dentarr,
                                       struct obj_dentry *dentry)
{
        struct obj_dentry *next_de;

        next_de = (void *) dentry + obj_dentry_size(dentry);
        if (next_de == dentarr_end(dentarr))
                return NULL;
        return next_de;
}

int dentarr_check_empty(struct bilbyfs_info *bi, struct obj_dentarr *dentarr)
{
        return (!dentarr_first_dentry(dentarr) ? 0 : -ENOTEMPTY);
}

int dentarr_add_dentry(struct bilbyfs_info *bi, struct obj_dentarr *dentarr,
                       struct inode *inode, const char *name)
{
        struct obj_dentry *de;
        int sz_change;
        int nb_dentry;
        obj_id id;
        int len;

        sz_change = obj_dentry_size_from_nm(name);
        id = le64_to_cpu(dentarr->id);
        nb_dentry = le32_to_cpu(dentarr->nb_dentry) + 1;
        len = obj_dentarr_size(dentarr);
        de = dentarr_end(dentarr);

        pack_obj_dentry(de, inode, name);
        pack_obj_dentarr(dentarr, id, nb_dentry, len + sz_change);
        return sz_change;
}

int dentarr_del_dentry(struct bilbyfs_info *bi, struct obj_dentarr *dentarr,
                       const char *name)
{
        struct obj_dentarr *copy_dentarr;
        struct obj_dentry *de;
        struct obj_dentry *copy_de;
        int sz_change;
        int nb_dentry;
        obj_id id;
        int delen;
        int len;

        sz_change = obj_dentry_size_from_nm(name);
        id = le64_to_cpu(dentarr->id);
        nb_dentry = le32_to_cpu(dentarr->nb_dentry);
        len = obj_dentarr_size(dentarr);

        copy_dentarr = kmalloc(len);
        if (!copy_dentarr)
                return -ENOMEM;
        memcpy(copy_dentarr, dentarr, len);

        copy_de = dentarr_lookup_nm(bi, copy_dentarr, name);
        de = dentarr_lookup_nm(bi, dentarr, name);
        if (nb_dentry <= 0 || !copy_de) {
                kfree(copy_dentarr);
                return 0;
        }

        copy_de = dentarr_next_dentry(copy_dentarr, copy_de);
        while (copy_de) {
                delen = obj_dentry_size(de);
                memcpy(de, copy_de, delen);
                de = (void *) de + delen;
                copy_de = dentarr_next_dentry(copy_dentarr, copy_de);
        }
        kfree(copy_dentarr);

        nb_dentry--;
        if (nb_dentry == 0) {
                memset(dentarr, 0, len);
                pack_obj_del(dentarr, id);
        } else {
                pack_obj_dentarr(dentarr, id, nb_dentry, len - sz_change);
        }
        return sz_change;
}

struct obj_dentry *dentarr_lookup_nm(struct bilbyfs_info *bi,
                                     struct obj_dentarr *dentarr,
                                     const char *name)
{
        struct obj_dentry *de;

        de = dentarr_first_dentry(dentarr);
        while (de) {
                if (!strcmp(de->name, name)) 
                        return de;
                de = dentarr_next_dentry(dentarr, de);
        }
        return ERR_PTR(-ENOENT);
}

struct obj_dentarr *dentarr_read(struct bilbyfs_info *bi, obj_id id)
{
        struct obj_dentarr *dentarr;
        int err;
        /* We need to allocate enough to be able to add an entry */
        int size = BILBYFS_MAX_DENTARR_SZ;

        bilbyfs_debug("[S] dentarr_read(0x%llx)\n", id);
        dentarr = kmalloc(size);
        if (!dentarr)
                return ERR_PTR(-ENOMEM);

        err = ostore_read_obj(bi, id, dentarr, size);
        if (err) {
                kfree(dentarr);
                return ERR_PTR(err);
        }
        /* Sanity checking */
        if (le32_to_cpu(dentarr->nb_dentry) > BILBYFS_MAX_DENTARR_ENTRIES ||
            le32_to_cpu(dentarr->size) > BILBYFS_MAX_DENTARR_SZ) {
                kfree(dentarr);
                bilbyfs_err("dentarr_read: lookup err nb_dentry=%d, size=%d\n", le32_to_cpu(dentarr->nb_dentry), le32_to_cpu(dentarr->size));
                return ERR_PTR(-EINVAL);
        }
        return dentarr;
}

struct obj_dentarr *dentarr_read_or_create(struct bilbyfs_info *bi, obj_id id)
{
        struct obj_dentarr *dentarr;

        dentarr = dentarr_read(bi, id);
        if (IS_ERR(dentarr)) {
                if (PTR_ERR(dentarr) != -ENOENT)
                        return dentarr;
                dentarr = kmalloc(BILBYFS_DENTARR_SZ + BILBYFS_MAX_DENTRY_SZ);
                if (!dentarr)
                        return ERR_PTR(-ENOMEM);
                pack_obj_dentarr(dentarr, id, 0, BILBYFS_DENTARR_SZ);
        }
        return dentarr;
}
