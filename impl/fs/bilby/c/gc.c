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

int gc_init(struct bilbyfs_info *bi)
{
        bi->gc_buf.buf = vmalloc(bi->super.leb_size);
        if (bi->gc_buf.buf) {
                bi->gc_buf.size = bi->super.leb_size;
                return 0;
        }
        return -ENOMEM;
}

void gc_clean(struct bilbyfs_info *bi)
{
        vfree(bi->gc_buf.buf);
}

int gc_garbage_collect(struct bilbyfs_info *bi)
{
        int err, i;
        int lnum;
        int list_limit = BILBYFS_MAX_OBJ_PER_TRANS;
        struct obj_ch *obj;
        struct obj_ch **list, **valid_list;
        int count = 0, valid_count = 0;

        bilbyfs_err("bilbyfs GC\n");
        bilbyfs_debug("gc_garbage_collect() starts\n");

        /* Find block with most garbage */
        lnum = fsm_get_dirtiest_eb(bi);
        if (lnum < 0) {
                bilbyfs_debug("gc_garbage_collect() : No erase-block to garbage collect.\n");
                return -ENOENT;
        }

        // Scan erase-block to build object lists
        list = kmalloc(sizeof(struct obj_ch *) *list_limit);
        if (!list)
                return -ENOMEM;
        count = ostore_scan_leb_obj(bi, &bi->gc_buf, lnum, (void **) list, list_limit);
        if (count < 0) {
                kfree(list);
                return count;
        }

        valid_list = kmalloc(sizeof(struct obj_ch *) * list_limit);
        if (!valid_list) {
                kfree(list);
                return -ENOMEM;
        }
        for (i = 0; i < count; i++) {
                obj = list[i];
                if (!gim_is_removable(bi, obj)) {
                        valid_list[valid_count] = obj;
                        valid_count++;
                }
        }

        /* Copy valid objects to new erase-block */
        if (valid_count > 0) {
                err = ostore_write_obj_list(bi, (void **) valid_list, valid_count, OSW_GC | OSW_SYNC);
                kfree(valid_list);
                if (err) {
                        kfree(list);
                        return err;
                }
        }

        err = ostore_erase(bi, lnum);
        if (err) {
                kfree(list);
                kfree(valid_list);
                return err;
        }

        for (i = 0; i < count; i++)
                gim_garbage_collected(bi, list[i]);

        bilbyfs_debug("gc_garbage_collect() Successfully clean up lnum=%d\n", lnum);
        kfree(list);
        return 0;
}


