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

int wbuf_init(struct bilbyfs_info *bi)
{
        bi->rbuf.buf = vmalloc(bi->super.leb_size);
        if (bi->rbuf.buf) {
                bi->rbuf.size = bi->super.leb_size;
                return 0;
        }
        wbuf_clean(bi);
        return -ENOMEM;
}

void wbuf_clean(struct bilbyfs_info *bi)
{
        vfree(bi->rbuf.buf);
        memset(&bi->rbuf, 0, sizeof(bi->rbuf));
}

void wbuf_start(struct bilbyfs_info *bi, struct bilbyfs_wbuf *wbuf)
{
        bilbyfs_assert(bi->super.leb_size == bi->vi.usable_leb_size);
        wbuf->used = 0;
        wbuf->sync_offs = 0;
        wbuf->avail = bi->super.leb_size;
        wbuf->size = bi->super.leb_size;
}

int wbuf_write_obj(struct bilbyfs_info *bi, void *obj, int objlen, struct bilbyfs_wbuf *wbuf)
{
        bilbyfs_assert(objlen % BILBYFS_OBJ_PADDING == 0);
        bilbyfs_debug("wbuf_write_obj({lnum=%u,offs=%u,len=%u,oid=%llx}) = %d\n",
                      fsm_get_lnum(bi), wbuf->used, objlen,
                      ((struct obj_ch *)obj)->type >= BILBYFS_SUP_OBJ ? 0 : get_obj_id(obj),
                      (wbuf->avail < objlen ? -EINVAL : 0));
        if (wbuf->avail < objlen)
                return -EINVAL;

        memcpy(wbuf->buf + wbuf->used, obj, objlen);
        wbuf->avail -= objlen;
        wbuf->used += objlen;
        return 0;
}

int wbuf_prepare_commit(struct bilbyfs_info *bi, u32 *padding_sz, struct bilbyfs_wbuf *wbuf)
{
        struct obj_ch *ch;
        int pad_sz;

        /* Ensure non-empty transactions */
        bilbyfs_assert(wbuf->used > 0);
        if (wbuf->avail == 0)
                return wbuf->used;
        /*  padding to the next flash page */
        pad_sz = ALIGN(wbuf->used, bi->super.min_io_size) - wbuf->used;
        if (pad_sz < BILBYFS_CH_SZ) {
                memset(wbuf->buf + wbuf->used, BILBYFS_PAD_BYTE, pad_sz);
        } else {
                ch = wbuf->buf + wbuf->used;
                pack_obj_pad(ch, pad_sz);
                pack_obj_header(ch, next_sqnum(bi), BILBYFS_TRANS_ATOM);
        }
        if (padding_sz)
                *padding_sz = pad_sz;

        wbuf->avail -= pad_sz;
        wbuf->used += pad_sz;
        return wbuf->used;
}

int wbuf_atom_leb_commit(struct bilbyfs_info *bi, int lnum, struct bilbyfs_wbuf *wbuf)
{
        int err;

        /* Ensure that a LEB is big enough to store the data */
        bilbyfs_assert(bi->super.leb_size >= wbuf->used);
        /* Ensure that we do not commit an empty transaction */
        bilbyfs_assert(wbuf->used > 0);
        /* Ensure that we called wbuf_prepare_commit() */
        bilbyfs_assert(wbuf->used == ALIGN(wbuf->used, bi->super.min_io_size));

        err = ubi_leb_change(bi->ubi, lnum, wbuf->buf, wbuf->used);
        bilbyfs_debug("ubi_leb_change(ubi, %d, %p, %d) = %d\n",
                      lnum, wbuf->buf, wbuf->used, err);
        return err;
}

int wbuf_commit(struct bilbyfs_info *bi, u32 lnum, struct bilbyfs_wbuf *wbuf)
{
        int err;

        /* Ensure that sync is within used range */
        bilbyfs_assert(wbuf->sync_offs < wbuf->used);
        /* Ensure that sync is aligned to min-io-size */
        bilbyfs_assert(wbuf->sync_offs == ALIGN(wbuf->sync_offs, bi->super.min_io_size));
        /* Ensure that buffer contains enough room for synchronizing the
         * remaining data */
        bilbyfs_assert(wbuf->size >= wbuf->used);
        /* Ensure that we called wbuf_prepare_commit() */
        bilbyfs_assert(wbuf->used == ALIGN(wbuf->used, bi->super.min_io_size));

        err = ubi_leb_write(bi->ubi, lnum, wbuf->buf + wbuf->sync_offs, wbuf->sync_offs, wbuf->used - wbuf->sync_offs);
        bilbyfs_debug("ubi_leb_write(ubi, %d, %p, %d, %d) = %d\n",
                      lnum, wbuf->buf + wbuf->sync_offs, wbuf->sync_offs, wbuf->used - wbuf->sync_offs, err);
        if (!err)
                wbuf->sync_offs = wbuf->used;
        return err;
}

static int wbuf_read_obj_pages(struct bilbyfs_info *bi, struct obj_addr *addr,
                               struct bilbyfs_rbuf *rbuf)
{
        int min_io_size = bi->super.min_io_size;
        int max_io_size = bi->super.max_io_size;
        int offs_in_page = addr->offs % min_io_size;
        int aligned_offs = addr->offs - offs_in_page;
        int aligned_end = ALIGN(addr->offs + addr->len, min_io_size);
        int toread;
        int offs;
        int err;

        offs = 0;
        toread = aligned_end - aligned_offs;
        bilbyfs_assert(aligned_offs == ALIGN(aligned_offs, min_io_size));
        bilbyfs_assert(toread == ALIGN(toread, min_io_size));

        while (toread > max_io_size) {
                err = ubi_read(bi->ubi, addr->lnum, rbuf->buf + offs,
                               aligned_offs + offs, max_io_size);
                if (err)
                        return err;
                offs += max_io_size;
                toread -= max_io_size;
        }
        while (toread >= min_io_size) {
                err = ubi_read(bi->ubi, addr->lnum, rbuf->buf + offs,
                               aligned_offs + offs, min_io_size);
                if (err)
                        return err;
                offs += min_io_size;
                toread -= min_io_size;
        }
        bilbyfs_assert(toread <= 0);
        /* offset from where we started to read */
        rbuf->offs = aligned_offs;
        return offs_in_page;
}

int wbuf_read_obj(struct bilbyfs_info *bi, void *buf, struct obj_addr *addr)
{
        int err;
        int offs_in_page;

        err = wbuf_read_obj_pages(bi, addr, &bi->rbuf);
        if (err < 0)
                return err;

        offs_in_page = err;
        memcpy(buf, bi->rbuf.buf + offs_in_page, addr->len);
        return 0;
}

int wbuf_read_sum(struct bilbyfs_info *bi, int lnum, struct bilbyfs_rbuf *rbuf, u32 *sum_offs_ret)
{
        int io_sz = bi->super.min_io_size;
        int sum_offs;
        int nb_read;
        int offs = bi->super.leb_size - io_sz;
        int err;
        int i;
        struct obj_sum *sum;
        /* struct timeval st, stp; */

        bilbyfs_assert(rbuf->size == bi->super.leb_size);
        /* bilbyfs_err("reading 1 page from erase-block %x\n", lnum); */
        bi->nb_pages += 1;
        /*
        do_gettimeofday(&st);
        */
        err = ubi_read(bi->ubi, lnum, rbuf->buf + offs, offs, io_sz);
        if (err)
                return err;
        /*
        do_gettimeofday(&stp);
        pr_err("timed ubi_read() : %ld.%ld\n", stp.tv_sec - st.tv_sec, stp. tv_usec - st.tv_usec);
        */
        sum_offs = le32_to_cpu(*(u32*)(rbuf->buf + bi->super.leb_size - BILBYFS_OBJ_SUM_OFFS_SZ));
        if (sum_offs >= (bi->super.leb_size - BILBYFS_OBJ_SUM_OFFS_SZ))
                return -ENOENT;
        offs = sum_offs - sum_offs % io_sz;
        nb_read = (bi->super.leb_size - offs) / io_sz;
        /* bilbyfs_err("reading more pages (%u) from erase-block %x\n", nb_read - 1, lnum); */
        bi->nb_extra_pages += nb_read - 1;
        for (i = 0; i < nb_read - 1; i++) {
        /*
                do_gettimeofday(&st);
        */
                err = ubi_read(bi->ubi, lnum, rbuf->buf + offs, offs, io_sz);
                if (err)
                        return err;
        /*
                do_gettimeofday(&stp);
                pr_err("timed ubi_read() e : %ld.%ld\n", stp.tv_sec - st.tv_sec, stp. tv_usec - st.tv_usec);
        */
                offs += io_sz;
        }
        sum= rbuf->buf + sum_offs;
        bilbyfs_debug("summary (.lnum=%d, .nb_read=%d, .sum_sz=%u, io_sz=%d, sum.size=%u, sum.nb_entry=%u)\n", lnum, nb_read, bi->super.leb_size - sum_offs, io_sz, le32_to_cpu(sum->ch.len), le32_to_cpu(sum->nb_sum_entry));
        rbuf->offs = 0;
        *sum_offs_ret = sum_offs;
        return 0;
}

/* Read an entires LEB but stops when encountering a block that starts by 0xffff
 * and assumes that the remaining pages are full of 0xff too.
 */
int wbuf_read_leb_fast(struct bilbyfs_info *bi, int lnum, struct bilbyfs_rbuf *rbuf)
{
        int io_sz = bi->super.min_io_size;
        int nb_read = bi->super.leb_size / io_sz;
        int offs = 0;
        int err;
        int i;

        bilbyfs_assert(rbuf->size == bi->super.leb_size);
        for (i = 0; i < nb_read; i++) {
                err = ubi_read(bi->ubi, lnum, rbuf->buf + offs, offs, io_sz);
                if (err)
                        return err;
                if (*(u64*)(rbuf->buf + offs) == 0xffffffffffffffff) {
                        break;
                }
                offs += io_sz;
        }
        rbuf->offs = 0;
        return 0;
}

int wbuf_read_leb(struct bilbyfs_info *bi, int lnum, struct bilbyfs_rbuf *rbuf)
{
        int io_sz = bi->super.min_io_size;
        int nb_read = bi->super.leb_size / io_sz;
        int offs = 0;
        int err;
        int i;

        bilbyfs_assert(rbuf->size == bi->super.leb_size);
        for (i = 0; i < nb_read; i++) {
                err = ubi_read(bi->ubi, lnum, rbuf->buf + offs, offs, io_sz);
                if (err)
                        return err;
                offs += io_sz;
        }
        rbuf->offs = 0;
        return 0;
}

int wbuf_erase(struct bilbyfs_info *bi, int lnum)
{
        int err = ubi_leb_erase(bi->ubi, lnum);
        bilbyfs_debug("ubi_leb_erase(lnum=%d) = %d\n", lnum, err);
        return err;
}

void *wbuf_next_obj_addr(struct bilbyfs_info *bi, struct obj_addr *addr,
                         struct bilbyfs_rbuf *rbuf)
{
        struct obj_ch *obj;
        u32 leb_offs;
        u32 rbuf_offs;
        int err;

        /* Ensures that rbuf covers addr */
        bilbyfs_assert(rbuf->offs <= addr->offs);

        /* Note: This function also works if addr->len = 0, it will
         * just check that there exists a valid object at addr->offs
         * and store its length in addr->len.
         */

        leb_offs = addr->offs + addr->len;
        if (leb_offs >= (rbuf->offs + rbuf->size))
                return ERR_PTR(-ENOENT);

        /* Make offs an offset in the rbuf */
        rbuf_offs = leb_offs - rbuf->offs;
        /* Get a pointer to obj in rbuf */
        obj = rbuf->buf + rbuf_offs;
        err = check_obj_header(obj, rbuf->size - rbuf_offs);
        if (!err) {
                addr->offs = leb_offs;
                addr->len = le32_to_cpu(obj->len);
                addr->sqnum = le64_to_cpu(obj->sqnum);
                return obj;
        }

        /* Scan for pad byte */
        if (err == -ENOENT) {
                if (*((u8 *) obj) == BILBYFS_PAD_BYTE) {
                        addr->offs = leb_offs;
                        addr->len = 8;
                        return wbuf_next_obj_addr(bi, addr, rbuf);
                }
        }
        return ERR_PTR(err);
}

