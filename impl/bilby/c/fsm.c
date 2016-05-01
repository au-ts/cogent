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

int fsm_init(struct bilbyfs_info *bi)
{
        int nb_leb = bi->super.leb_cnt;
        int i;

        bi->dirty_list = kmalloc(sizeof(*bi->dirty_list) * nb_leb);
        if (!bi->dirty_list)
                return -ENOMEM;
        bi->used_leb_list = kmalloc(sizeof(*bi->used_leb_list) * nb_leb);
        if (!bi->used_leb_list) {
                kfree(bi->dirty_list);
                return -ENOMEM;
        }
        for (i = 0; i < nb_leb; i++) {
                bi->dirty_list[i] = 0;
                bi->used_leb_list[i] = false;
        }
        bi->fsm_nb_free_eb = nb_leb;
        bi->fsm_lnum = 0;
        return 0;
}

static int fsm_check_free_space(struct bilbyfs_info *bi, int osw_flag)
{
        u32 n_gc = bi->super.nb_reserved_gc;
        u32 n_del = bi->super.nb_reserved_del;
        u32 n_free = bi->fsm_nb_free_eb;

        if (n_free < n_gc && !(osw_flag & OSW_GC)) {
                bilbyfs_err("Warning: Number of free blocks extremely low, only "
                            "the garbage collector is allowed to run. (n_free = %d < n_gc = %d)\n",
                            n_free, n_gc);
                return -ENOSPC;
        }

        if (n_free < n_del + n_gc && !(osw_flag & OSW_DEL) && !(osw_flag & OSW_GC)) {
                bilbyfs_err("Warning: Number of free blocks is very low, only operations "
                            "that delete data are permitted. (n_free = %d < (n_del = %d) + (n_gc = %d)\n",
                            n_free, n_del, n_gc);
                return -ENOSPC;
        }
        return 0;
}

void fsm_clean(struct bilbyfs_info *bi)
{
        kfree(bi->dirty_list);
        kfree(bi->used_leb_list);
}

void fsm_mark_used(struct bilbyfs_info *bi, int lnum)
{
        bilbyfs_assert(lnum >= BILBYFS_LOG_FST_LNUM && lnum < bi->super.leb_cnt);
        bi->used_leb_list[lnum] = true;
        bi->fsm_nb_free_eb--;
}

void fsm_mark_dirty(struct bilbyfs_info *bi, struct obj_addr *addr)
{
        bilbyfs_assert(addr->lnum >= BILBYFS_LOG_FST_LNUM && addr->lnum < bi->super.leb_cnt);
        bilbyfs_assert(bi->used_leb_list[addr->lnum]);

        bi->dirty_list[addr->lnum] += addr->len;
}

void fsm_mark_erased(struct bilbyfs_info *bi, int lnum)
{
        bilbyfs_assert(lnum >= BILBYFS_LOG_FST_LNUM && lnum < bi->super.leb_cnt);
        bilbyfs_assert(bi->used_leb_list[lnum]);
        bilbyfs_debug("mark_erased({.dirty_list = %d, .leb_size=%d})\n", bi->dirty_list[lnum], bi->super.leb_size);
        /* FIXME Mount time dead space makes it hard to have the following assertion */
       /* bilbyfs_assert(bi->dirty_list[lnum] == bi->super.leb_size); */

        bi->used_leb_list[lnum] = false;
        bi->fsm_nb_free_eb++;
        bi->dirty_list[lnum] = 0;
}

int fsm_alloc_eb(struct bilbyfs_info *bi, int osw_flag)
{
        int i;
        int err;

	bi->fsm_lnum = 0; /* Reinitialise fsm_lnum */
        err = fsm_check_free_space(bi, osw_flag);
        if (err) {
                if (err == -ENOSPC && !(osw_flag & OSW_GC) && !gc_garbage_collect(bi))
                        err = fsm_check_free_space(bi, osw_flag);
                if (err)
                        return err;
        }

        /* Search for next available LEB */
        for (i = BILBYFS_LOG_FST_LNUM; i < bi->super.leb_cnt; i++) {
                if (!bi->used_leb_list[i]) {
                        /* Update cur leb */
                        fsm_mark_used(bi, i);
                        bi->fsm_lnum = i;
                        bilbyfs_debug("fsm_alloc_eb() = {.lnum = %d}\n", bi->fsm_lnum);
                        return 0;
                }
        }
        bilbyfs_debug("fsm_alloc_eb() = -ENOSPC\n");
        return -ENOSPC;
}

u32 fsm_get_lnum(struct bilbyfs_info *bi)
{
        return bi->fsm_lnum;
}

unsigned long long fsm_get_free_space(struct bilbyfs_info *bi)
{
        unsigned long long freespace = 0;
        int i;

        for (i = BILBYFS_LOG_FST_LNUM; i < bi->super.leb_cnt; i++)
                if (!bi->used_leb_list[i])
                        freespace += bi->super.leb_size;
        return freespace;
}

unsigned long long fsm_get_available_space(struct bilbyfs_info *bi)
{
        unsigned long long freespace;
        int n_reserved = bi->super.nb_reserved_gc + bi->super.nb_reserved_del;

        freespace = fsm_get_free_space(bi);
        if (freespace < n_reserved * bi->super.leb_size)
                freespace = 0;
        else
                freespace -= n_reserved * bi->super.leb_size;
        return freespace;
}

int fsm_get_dirtiest_eb(struct bilbyfs_info *bi)
{
        int lnum;
        int dirtiest_lnum = -1;
        int garbage_size = 0;

        for (lnum = BILBYFS_LOG_FST_LNUM; lnum < bi->super.leb_cnt; lnum++) {
                if (bi->used_leb_list[lnum] && lnum != fsm_get_lnum(bi)
                                && bi->dirty_list[lnum] > garbage_size) {
                        dirtiest_lnum = lnum;
                        garbage_size = bi->dirty_list[lnum];
                }
        }

        return dirtiest_lnum;
}
