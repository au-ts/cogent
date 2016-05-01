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

void rdx_init(struct bilbyfs_info *bi, struct fsop_readdir_ctx *rdx, ino_t ino)
{
        BUILD_BUG_ON(sizeof(struct fsop_readdir_ctx) > BILBYFS_MAX_READDIR_DATA_SIZE);
        rdx->id = inode_id_init(ino);
        rdx->dentarr = NULL;
        rdx->de = NULL;
}

void rdx_clean(struct fsop_readdir_ctx *rdx)
{
        rdx->id = NIL_ID;
        kfree(rdx->dentarr);
        rdx->dentarr = NULL;
        rdx->de = NULL;
}

static struct obj_dentry *next_dentarr_dentry(struct bilbyfs_info *bi,
                                              struct fsop_readdir_ctx *rdx)
{
        struct obj_dentarr *dentarr;

        do {
                kfree(rdx->dentarr);
                rdx->dentarr = NULL;
                rdx->id = ostore_next_obj_id(bi, rdx->id);
                if (!is_dentarr_id(rdx->id) || rdx->id == NIL_ID)
                        return ERR_PTR(-ENOENT);

                dentarr = dentarr_read(bi, rdx->id);
                if (IS_ERR(dentarr))
                        return (void *)dentarr;
                rdx->dentarr = dentarr;
                /* FIXME dentarr_read() should never return an empty
                 * dentarr, I believe this check is useless */
        } while (!dentarr_check_empty(bi, rdx->dentarr));
        /* As the dentarr object is non-empty: no risk to return NULL */
        return dentarr_first_dentry(rdx->dentarr);
}

struct obj_dentry *rdx_next_dentry(struct bilbyfs_info *bi,
                                   struct fsop_readdir_ctx *rdx)
{
        struct obj_dentry *de;

        if (!rdx->dentarr) {
                de = next_dentarr_dentry(bi, rdx);
                rdx->de = IS_ERR(de) ? NULL : de;
                return de;
        }

        /* Here rdx->de should always be a valid dentry within dentarr
         * unless rdx_next_dentry has already return -ENOENT */
        rdx->de = rdx->de ? dentarr_next_dentry(rdx->dentarr, rdx->de) : NULL;
        if (!rdx->de) {
                de = next_dentarr_dentry(bi, rdx);
                rdx->de = IS_ERR(de) ? NULL : de;
                return de;
        }
        return rdx->de ? rdx->de : ERR_PTR(-ENOENT);
}
