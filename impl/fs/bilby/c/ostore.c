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

int ostore_init(struct bilbyfs_info *bi)
{
        struct bilbyfs_wbuf *wbuf = &bi->wbuf;
        int err;

        wbuf->buf = vmalloc(bi->super.leb_size);
        if (!wbuf->buf)
                return -ENOMEM;
        bi->sup_wbuf.buf = vmalloc(bi->super.leb_size);
        if (!bi->sup_wbuf.buf) {
                vfree(wbuf->buf);
                return -ENOMEM;
        }
        bi->summary = vmalloc(bi->super.leb_size);
        if (!bi->summary) {
                vfree(wbuf->buf);
                vfree(bi->sup_wbuf.buf);
                return -ENOMEM;
        }
        bi->summary->nb_sum_entry = 0;
        wbuf->size = bi->super.leb_size;
        bi->sup_wbuf.size = bi->super.leb_size;
        err = allocpool_init(&bi->node_pool);
        if (!err) {
                err = idx_init(bi);
                if (!err) {
                        err = fsm_init(bi);
                        if (!err) {
                                err = wbuf_init(bi);
                                if (!err) {
                                        err = gim_init(bi);
                                        if (!err) {
                                                err = gc_init(bi);
                                                if (!err)
                                                        return 0;
                                                gim_clean(bi);
                                        }
                                        wbuf_clean(bi);
                                }
                                fsm_clean(bi);
                        }
                        idx_clean(bi);
                }
                allocpool_destroy(&bi->node_pool);
        }
        vfree(wbuf->buf);
        vfree(bi->sup_wbuf.buf);
        vfree(bi->summary);
        return err;
}

void ostore_clean(struct bilbyfs_info *bi)
{
        struct bilbyfs_wbuf *wbuf = &bi->wbuf;

        vfree(wbuf->buf);
        memset(wbuf, 0, sizeof(*wbuf));
        vfree(bi->sup_wbuf.buf);
        memset(&bi->sup_wbuf, 0, sizeof(*wbuf));
        vfree(bi->summary);
        idx_clean(bi);
        fsm_clean(bi);
        wbuf_clean(bi);
        gim_clean(bi);
        gc_clean(bi);
        allocpool_destroy(&bi->node_pool);
}

int ostore_get_obj_size(struct bilbyfs_info *bi, obj_id id)
{
        struct obj_addr addr;
        int err;

        err = idx_get_obj_addr(bi, id, &addr);
        if (err)
                return err;
        return addr.len;
}

int ostore_read_obj(struct bilbyfs_info *bi, obj_id id, void *buf, u32 len)
{
        struct obj_addr addr;
        int err;

        err = idx_get_obj_addr(bi, id, &addr);
        if (err)
                return err;

        if (len < addr.len) {
                bilbyfs_err("ostore_read_obj: buf too small\n");
                return -EINVAL; /* please try again with a larger buffer */
        }

        if (addr.lnum == fsm_get_lnum(bi)) { /* Read from write-buffer */
                bilbyfs_debug("read_obj(oid=%llx) from buffer\n", id);
                memcpy(buf, bi->wbuf.buf + addr.offs, addr.len);
                return 0;
        }
        err = wbuf_read_obj(bi, buf, &addr);
        {
                struct obj_ch *obj = buf;
                bilbyfs_debug("read_obj({%s,oid=%llx}, {lnum=%d,offs=%d,len=%d}) = %d\n",
                        (obj->type == BILBYFS_INODE_OBJ ? "inode" :
                        (obj->type == BILBYFS_DENTARR_OBJ ? "dentarr":
                        (obj->type == BILBYFS_DATA_OBJ ? "data" :
                        (obj->type == BILBYFS_DEL_OBJ ? "del" : "unknown")))),
                        id,
                        addr.lnum, addr.offs, addr.len, err);
                bilbyfs_assert(get_obj_id(obj) == id);
                (void)obj;
        }
        return err;
}

obj_id ostore_next_obj_id(struct bilbyfs_info *bi, obj_id id)
{
        obj_id nxt = idx_next_obj_id(bi, id);
        if (inum_from_id(id) == inum_from_id(nxt))
                return nxt;
        return NIL_ID;
}

/**
 * proc_obj - process an object
 *
 * @bi: global fs info
 * @type: type of the object
 * @id: ID of the object
 * @addr: address of the object on disk
 *
 * This function will update:
 *  - Index: if the object is newer, update the index with the object
 *  - FSM: older version (if exist) of an object is marked as dirty
 *
 * Returns negative error code if unsuccessful or zero otherwise
 */
static int proc_obj(struct bilbyfs_info *bi, u8 type, obj_id id, struct obj_addr *addr)
{
        obj_id curr_id;
        struct obj_addr old_addr;
        struct idx_node *idx_node;
        struct gim_node *gnode;
        int err = 0;

        switch (type) {
        case BILBYFS_PAD_OBJ:
                fsm_mark_dirty(bi, addr);
                break;
        case BILBYFS_INODE_OBJ:
        case BILBYFS_DENTARR_OBJ:
        case BILBYFS_DATA_OBJ:
                /* Valid object */
                idx_node = idx_get_or_create_obj_addr_node(bi, id);
                if (!idx_node->addr.sqnum) { /* If we just created this node */
                        idx_node->addr = *addr;
                } else {
                        if (idx_node->addr.sqnum < addr->sqnum) {
                                /* idx_set_obj_addr(bi, id, addr, NULL); */
                                idx_node->addr = *addr;
                                gim_mark_garbage(bi, id, &idx_node->addr, NULL);
                                fsm_mark_dirty(bi, &idx_node->addr);
                        } else {
                                gim_mark_garbage(bi, id, addr, NULL);
                                fsm_mark_dirty(bi, addr);
                        }
                }
                break;
        case BILBYFS_DEL_OBJ:
                /* Delete object */
                switch (type_from_id(id)) {
                case BILBYFS_DENTARR_OBJ:
                        /* Deletion object that cover single object */
                        err = idx_get_obj_addr(bi, id, &old_addr);
                        if (!err) { /* Obj found in index */
                                if (old_addr.sqnum < addr->sqnum) {
                                        gnode = idx_del_obj_addr(bi, id);
                                        gim_mark_garbage(bi, id, &old_addr, gnode);
                                        fsm_mark_dirty(bi, &old_addr);
                                }
                        }

                        break;
                case BILBYFS_INODE_OBJ:
                case BILBYFS_DATA_OBJ:
                        /* Deletion object that cover a range of objects */
                        for (curr_id = id; curr_id != NIL_ID; curr_id = idx_next_obj_id(bi, curr_id)) {
                                err = idx_get_obj_addr(bi, curr_id, &old_addr);
                                if (!err) {
                                        if (old_addr.sqnum < addr->sqnum) {
                                                gnode = idx_del_obj_addr(bi, curr_id);
                                                gim_mark_garbage(bi, curr_id, &old_addr, gnode);
                                                fsm_mark_dirty(bi, &old_addr);
                                        }
                                }
                        }
                        break;
                default:
                        bilbyfs_assert(0);
                }
                /* Mark the deletion object itself as dirty */
                gim_mark_garbage(bi, id, addr, NULL);
                fsm_mark_dirty(bi, addr);
                break;
        default:
                bilbyfs_assert(0);
        }

        return 0;
}

static u8 get_obj_trans(int count, int i)
{
        if (count == 1)
                return BILBYFS_TRANS_ATOM;
        else if (i == 0)
                return BILBYFS_TRANS_ST;
        else if (i == count - 1)
                return BILBYFS_TRANS_END;
        return BILBYFS_TRANS_IN;
}

#define NOBJ BILBYFS_MAX_OBJ_PER_TRANS
int obj_has_id(struct obj_ch *obj)
{
        return (obj->type == BILBYFS_INODE_OBJ ||
                obj->type == BILBYFS_DENTARR_OBJ ||
                obj->type == BILBYFS_DATA_OBJ ||
                obj->type == BILBYFS_DEL_OBJ);
}

static inline int debug_print_objs(struct bilbyfs_info *bi, u32 lnum)
{
        struct obj_ch **olist, **olist2;
        struct obj_addr addr;
        int err;
        int i;
        struct obj_ch *obj;
        struct bilbyfs_rbuf rbuf;
        int nbo, nbo2;

        bilbyfs_debug("ostore_scan_obj() : alloc = %lu\n", (unsigned long)(sizeof(*olist) * NOBJ));
        olist = kmalloc(sizeof(*olist) * NOBJ);
        if (!olist)
                return -ENOMEM;
        rbuf.buf = bi->wbuf.buf;
        rbuf.size = bi->wbuf.size;
        rbuf.offs = 0;
        err = ostore_scan_obj(bi, &rbuf, lnum, (void **)olist, NOBJ);
        bilbyfs_debug("ostore_scan_obj() = %d\n", err);
        if (err < 0) {
                kfree(olist);
                return err;
        }
        addr.lnum = lnum;
        addr.offs = 0;
        addr.len = 0;
        nbo = err;
        for (i = 0; i < nbo; i++) {
                obj = olist[i];
                addr.len = obj->len;
                bilbyfs_debug("scan_obj({%s,oid=%llx}, {lnum=%d,offs=%d,len=%d})\n",
                              (obj->type == BILBYFS_INODE_OBJ ? "inode" :
                               (obj->type == BILBYFS_DENTARR_OBJ ? "dentarr":
                                (obj->type == BILBYFS_DATA_OBJ ? "data" :
                                 (obj->type == BILBYFS_DEL_OBJ ? "del" :
                                  (obj->type == BILBYFS_SUP_OBJ ? "super" :
                                   (obj->type == BILBYFS_PAD_OBJ ? "pad" : "unknown")))))),
                                (!obj_has_id(obj) ? 0 : get_obj_id(obj)),
                              addr.lnum, addr.offs, addr.len);
                addr.offs += addr.len;
        }
        bilbyfs_debug("ostore_scan_obj() = %d\n", err);
        olist2 = kmalloc(sizeof(*olist) * NOBJ);
        if (!olist2)
                return -ENOMEM;
        err = ostore_scan_leb_obj(bi, &bi->rbuf, lnum, (void **)olist2, NOBJ);
        if (err < 0) {
                kfree(olist);
                kfree(olist2);
                return err;
        }
        addr.lnum = lnum;
        addr.offs = 0;
        addr.len = 0;
        nbo2 = err;
        for (i = 0; i < nbo2; i++) {
                obj = olist2[i];
                addr.len = obj->len;
                bilbyfs_debug("scan_obj({%s,oid=%llx}, {lnum=%d,offs=%d,len=%d})\n",
                              (obj->type == BILBYFS_INODE_OBJ ? "inode" :
                               (obj->type == BILBYFS_DENTARR_OBJ ? "dentarr":
                                (obj->type == BILBYFS_DATA_OBJ ? "data" :
                                 (obj->type == BILBYFS_DEL_OBJ ? "del" :
                                  (obj->type == BILBYFS_SUP_OBJ ? "super" :
                                   (obj->type == BILBYFS_PAD_OBJ ? "pad" : "unknown")))))),
                                (!obj_has_id(obj) ? 0 : get_obj_id(obj)),
                              addr.lnum, addr.offs, addr.len);
                err = memcmp(obj, olist[i], obj->len);
                bilbyfs_assert(!err);
                addr.offs += addr.len;
        }
        if (nbo != nbo2) {
                print_hex_dump(KERN_ERR, "wbuf: ", DUMP_PREFIX_ADDRESS, 32, 8, rbuf.buf, rbuf.size, true);
                print_hex_dump(KERN_ERR, "rbuf: ", DUMP_PREFIX_ADDRESS, 32, 8, bi->rbuf.buf, bi->rbuf.size, true);
        }
        kfree(olist2);
        kfree(olist);
        return 0;
}

int obj_sum_size_with_extra(struct obj_sum *sum, u32 nb_extra_entries)
{
        return ALIGN(obj_sum_size(sum) + nb_extra_entries * BILBYFS_SUM_ENTRY_SZ, BILBYFS_OBJ_PADDING);
}

int ostore_write_summary(struct bilbyfs_info *bi, u32 *padding_sz)
{
        struct bilbyfs_wbuf *wbuf = &bi->wbuf;
        struct obj_ch *ch;
        int err;
        u32 len;
        u32 pad_sz;

        len = obj_sum_size(bi->summary);
        bilbyfs_assert(wbuf->avail >= len);

        /* wbuf summary aware padding */
        pad_sz = wbuf->avail - len;
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
        pack_obj_sum(bi->summary, wbuf->used);
        pack_obj_header(&bi->summary->ch, next_sqnum(bi), BILBYFS_TRANS_ATOM);
        err = wbuf_write_obj(bi, bi->summary, len, wbuf);
        bilbyfs_debug("ostore_write_summary(offset=%u) = %d\n", wbuf->used, err);
        if (!err)
                bi->summary->nb_sum_entry = 0;
        bilbyfs_assert(wbuf->avail == 0);
        return err;
}

void sum_obj(struct bilbyfs_info *bi, struct obj_ch *obj, struct obj_addr *addr)
{
        struct obj_sum *sum = bi->summary;
        struct obj_sum_entry *entry;
        obj_id oid, eoid;
        u8 oid_type;
        u32 nb_sum_entry = le32_to_cpu(sum->nb_sum_entry);
        bool is_del;
        int i;

        oid = get_obj_id(obj);
        oid_type = type_from_id(oid);
        is_del = obj->type == BILBYFS_DEL_OBJ;

        /* If we have a deletion object, we can only replace younger deletion
         * objects that have the exact same oid in case of dentarr deletion or
         * objects that have a higher oid for inode and data deletion objects.
         * Summary of non-deletion objects can only replace objects with
         * the exact same oid.
         */
        if (is_del) {
                for (i = 0; i < nb_sum_entry; i++) {
                        entry = &sum->entries[i];
                        eoid = le64_to_cpu(entry->id);

                        if (oid_type == BILBYFS_DENTARR_OBJ) {
                                if (eoid == oid) {
                                        if (le64_to_cpu(entry->sqnum) > addr->sqnum) {
                                                return;
                                        }
                                        break;
                                }
                        } else if (inum_from_id(eoid) == inum_from_id(oid) && eoid > oid) {
                                if (le64_to_cpu(entry->sqnum) < addr->sqnum)
                                        break;
                        }
                }
        } else {
                for (i = 0; i < nb_sum_entry; i++) {
                        entry = &sum->entries[i];
                        /* We cannot replace a del object with an new object */
                        if (obj_sum_entry_is_del(entry) && oid_type != BILBYFS_DENTARR_OBJ)
                                continue;
                        eoid = le64_to_cpu(entry->id);
                        if (eoid == oid) {
                                if (le64_to_cpu(entry->sqnum) > addr->sqnum)
                                        return;
                                break;
                        }
                }
        }
        /*  Not that the whole if/else above is an optimisation to
         *  reuse a sum_entry, we could safely replace it with
         *  i = nb_sum_entry;
         */
        entry = &sum->entries[i];
        entry->id = oid;
        entry->len = cpu_to_le32(addr->len);
        entry->sqnum = cpu_to_le64(addr->sqnum);
        entry->del_flag_and_offs = cpu_to_le32(addr->offs | (is_del ? BILBYFS_SUM_ENTRY_DEL_FLAG_MASK : 0));
        if (i == nb_sum_entry) {
                sum->nb_sum_entry = cpu_to_le32(nb_sum_entry + 1);
                entry->count = 0;
        } else
                entry->count = cpu_to_le32(le32_to_cpu(entry->count) + 1);
}

int ostore_sync(struct bilbyfs_info *bi, int force_summary)
{
        struct bilbyfs_wbuf *wbuf = &bi->wbuf;
        int err = 0;
        u32 padding_size;
        struct obj_addr curr_addr;
        u32 sum_sz;

        bilbyfs_debug("ostore_sync()\n");
        if (bi->no_summary)
                force_summary = 0;
        if (wbuf->sync_offs == wbuf->used && !force_summary)
                return 0;
        if (!wbuf->avail)
                return 0;
        bilbyfs_assert(!!fsm_get_lnum(bi));
        curr_addr.lnum = fsm_get_lnum(bi);
        curr_addr.offs = wbuf->used;
        /* Pad buffer to min_io_size */
        /*
         * We want to pad with a obj_pad only if that leaves enough space to
         * write at least one more object (remember we also need to count space
         * for the summary).
         */
        sum_sz = obj_sum_size_with_extra(bi->summary, 1);
        if (!bi->no_summary && (force_summary || ALIGN(wbuf->used, bi->super.min_io_size) + sum_sz + BILBYFS_MIN_OBJ_SZ > bi->super.leb_size)) {
                err = ostore_write_summary(bi, &padding_size);
                if (err)
                        return err;
        } else
                wbuf_prepare_commit(bi, &padding_size, wbuf);

        if (padding_size > 0) {
                curr_addr.len = padding_size;
                fsm_mark_dirty(bi, &curr_addr);
        }
        err = wbuf_commit(bi, fsm_get_lnum(bi), wbuf);
        /* bilbyfs_debug("debug_print_obj(%u) = %d\n", fsm_get_lnum(bi), debug_print_objs(bi, fsm_get_lnum(bi))); */
        return err;
}

u32 obj_list_serial_size(struct obj_ch **obj_list, int count)
{
        u32 sz = 0;
        int i;

        for (i = 0; i < count; i++) {
                sz += obj_list[i]->len;
        }
        return sz;
}

int ostore_write_obj_list(struct bilbyfs_info *bi, void **obj_list, int count, int osw_flag)
{
        int i;
        int err = 0;
        struct obj_ch *obj;
        struct obj_addr curr_addr;
        struct bilbyfs_wbuf *wbuf = &bi->wbuf;
        u32 serial_sz;
        u32 offs;

	if (!fsm_get_lnum(bi) || !wbuf->avail) {
                err = fsm_alloc_eb(bi, osw_flag);
                if (err)
                        return err;
                wbuf_start(bi, wbuf);
        }
        bilbyfs_debug("wbuf->avail = %u, obj_sum_size = %u\n", wbuf->avail , obj_sum_size(bi->summary));
        if (!bi->no_summary)
                bilbyfs_assert(wbuf->avail >= obj_sum_size(bi->summary));
        if (osw_flag & OSW_SYNC) {
               err = ostore_sync(bi, false);
               if (err)
                       return err;
        }
        if (!bi->no_summary)
                bilbyfs_assert(wbuf->avail >= obj_sum_size(bi->summary));
        bilbyfs_assert(count > 0);
        for (i = 0; i < count; i++) {
                obj = obj_list[i];
                pack_obj_header(obj, next_sqnum(bi), get_obj_trans(count, i));
        }
        serial_sz = obj_list_serial_size((struct obj_ch **)obj_list, count);
        bilbyfs_assert(serial_sz <= bi->super.leb_size);
        if (wbuf->avail < serial_sz + (bi->no_summary ? 0 : obj_sum_size_with_extra(bi->summary, count))) {
                err = ostore_sync(bi, true);
                if (err)
                        return err;
                err = fsm_alloc_eb(bi, osw_flag);
                if (err)
                        return err;
                wbuf_start(bi, wbuf);
        }

        offs = wbuf->used;
        /* Write objects into wbuf */
        for (i = 0; i < count; i++) {
                obj = obj_list[i];
                err = wbuf_write_obj(bi, obj, le32_to_cpu(obj->len), wbuf);
                if (err)
                        return err;
        }

        if (osw_flag & OSW_SYNC) {
               err = ostore_sync(bi, false);
               if (err)
                       return err;
        }

        /* Preallocate new index and gim entries */
        err = allocpool_alloc(&bi->node_pool, count * 2, NODE_SIZE);
        if (err)
                return err;

        /* Update index & fsm */
        curr_addr.lnum = fsm_get_lnum(bi);
        curr_addr.offs = offs;
        curr_addr.len = 0;
        bilbyfs_debug(".\n");
        for (i = 0; i < count; i++) {
                obj = obj_list[i];
                curr_addr.offs += curr_addr.len;
                curr_addr.len = le32_to_cpu(obj->len);
                curr_addr.sqnum = le64_to_cpu(obj->sqnum);

                err = proc_obj(bi, obj->type, get_obj_id(obj), &curr_addr);
                bilbyfs_debug("write_obj({%s,oid=%llx}, {lnum=%d,offs=%d,len=%d,sqnum=%llu}) = %d\n",
                              (obj->type == BILBYFS_INODE_OBJ ? "inode" :
                               (obj->type == BILBYFS_DENTARR_OBJ ? "dentarr":
                                (obj->type == BILBYFS_DATA_OBJ ? "data" :
                                 (obj->type == BILBYFS_DEL_OBJ ? "del" : "unknown")))),
                                get_obj_id(obj),
                              curr_addr.lnum, curr_addr.offs, curr_addr.len, curr_addr.sqnum, err);
                if (err)
                        bilbyfs_assert(false);
                if (!bi->no_summary)
                        sum_obj(bi, obj, &curr_addr);
        }
        allocpool_empty(&bi->node_pool);
        return 0;
}

int ostore_erase(struct bilbyfs_info *bi, int lnum)
{
        int err;

        err = wbuf_erase(bi, lnum);
        if (err)
                return err;

        fsm_mark_erased(bi, lnum);
        return 0;
}

int ostore_scan_obj(struct bilbyfs_info *bi, struct bilbyfs_rbuf *rbuf, int lnum,
                    void **list, int max_count)
{
        int err;
        struct obj_addr addr;
        struct obj_ch *obj;
        int count = 0;

        addr.lnum = lnum;
        addr.offs = 0;
        addr.len = 0;
        obj = wbuf_next_obj_addr(bi, &addr, rbuf);
        while (!IS_ERR(obj)) {
                if (count >= max_count)
                        return -EOVERFLOW;
                list[count] = obj;
                count++;
                obj = wbuf_next_obj_addr(bi, &addr, rbuf);
        }
        err = PTR_ERR(obj);
        if (err == -ENOENT)
                if (count > 0)
                        return count;
        return err;
}

int ostore_scan_leb_obj(struct bilbyfs_info *bi, struct bilbyfs_rbuf *rbuf, int lnum,
                        void **list, int max_count)
{
        int err;

        rbuf->offs = 0;
        err = wbuf_read_leb(bi, lnum, rbuf);
        if (err)
                return err;
        return ostore_scan_obj(bi, rbuf, lnum, list, max_count);
}

unsigned long long ostore_get_free_space(struct bilbyfs_info *bi)
{
        return fsm_get_free_space(bi);
}

unsigned long long ostore_get_available_space(struct bilbyfs_info *bi)
{
        return fsm_get_available_space(bi);
}

static struct obj_super *next_super_addr(struct bilbyfs_info *bi,
                                         struct obj_addr *addr,
                                         struct bilbyfs_rbuf *rbuf)
{
        struct obj_ch *obj;

        do {
                obj = wbuf_next_obj_addr(bi, addr, rbuf);
                if (IS_ERR(obj))
                        return (struct obj_super *)obj;
        } while (obj->type != BILBYFS_SUP_OBJ);
        return (struct obj_super *)obj;
}

/* SuperBlock objects are sequentially stored in BILBYFS_SUP_LNUM
 * When BILBYFS_SUP_LNUM is full we need to atomically erase the erase-block
 * and store a new object in it. To this end we use ubi_leb_change.
 */
static int mount_read_super(struct bilbyfs_info *bi)
{
        struct bilbyfs_rbuf *rbuf = &bi->rbuf;
        struct obj_super *super, *perr;
        struct obj_addr addr;
        int err;

        err = wbuf_read_leb_fast(bi, BILBYFS_SUP_LNUM, rbuf);
        if (err)
                return err;

        addr.lnum = BILBYFS_SUP_LNUM;
        addr.offs = 0;
        addr.len = 0;
        perr = next_super_addr(bi, &addr, rbuf);
        super = perr;
        while (!IS_ERR(perr)) {
                super = perr;
                perr = next_super_addr(bi, &addr, rbuf);
        }
        if (IS_ERR(super))
                return PTR_ERR(super);

        if (super->ch.type != BILBYFS_SUP_OBJ ||
            le32_to_cpu(super->ch.len) != BILBYFS_SUPER_SZ) {
                bilbyfs_err("Invalid Super object!\n");
                return -EINVAL;
        }
        unpack_obj_super(&bi->super, super);
        bi->super.min_io_size = bi->di.min_io_size;
        /* FIXME: Ensure that max_io_size is only used for write accesses */
        bi->super.max_io_size = bi->di.max_write_size;
        /* Go to the very last object and get the offs */
        while (!IS_ERR(wbuf_next_obj_addr(bi, &addr, rbuf)));
        bi->super_offs = addr.offs + addr.len;

        if (bi->next_sqnum < bi->super.sqnum) /* FIXME sanity check */
                bi->next_sqnum = bi->super.sqnum + 1;
        if (bi->next_inum < bi->super.last_inum) /* FIXME sanity check */
                bi->next_inum = bi->super.last_inum + 1;
        return 0;
}

int ostore_write_super(struct bilbyfs_info *bi)
{
        struct bilbyfs_wbuf *wbuf = &bi->sup_wbuf;
        struct obj_super sup;
        int size_trans;
        int err;

        bilbyfs_debug("ostore_write_super(lnum = %d, offs = %d) = ?\n",
                      BILBYFS_SUP_LNUM, bi->super_offs);

        bi->super.log_lnum = fsm_get_lnum(bi);
        bi->super.log_offs = bi->wbuf.sync_offs;
        bi->super.last_inum = bi->next_inum - 1;
        wbuf_start(bi, wbuf);
        wbuf->used = bi->super_offs;
        wbuf->sync_offs = bi->super_offs;
        memset(&sup, 0, sizeof(sup));
        pack_obj_super(&sup, &bi->super);
        pack_obj_header(&sup, next_sqnum(bi), BILBYFS_TRANS_ATOM);
        err = wbuf_write_obj(bi, &sup, BILBYFS_SUPER_SZ, wbuf);
        if (!err) {
                size_trans = wbuf_prepare_commit(bi, NULL, wbuf);
                err = wbuf_commit(bi, BILBYFS_SUP_LNUM, wbuf);
                if (!err) /* Obtain the next super offset */
                        bi->super_offs = wbuf->used;
        } else {
                wbuf_start(bi, wbuf);
                err = wbuf_write_obj(bi, &sup, BILBYFS_SUPER_SZ, wbuf);
                if (!err) {
                        size_trans = wbuf_prepare_commit(bi, NULL, wbuf);
                        err = wbuf_atom_leb_commit(bi, BILBYFS_SUP_LNUM, wbuf);
                        if (!err) /* Obtain the next super offset */
                                bi->super_offs = wbuf->used;
                }
        }
        return err;
}

static int mount_check_super(struct bilbyfs_info *bi)
{
        struct bilbyfs_super *sup = &bi->super;

        if (sup->leb_size != bi->vi.usable_leb_size) {
                bilbyfs_err("super.leb_size (%d) is not compatible with the"
                            "vi.usable_leb_size (%d) of the flash\n",
                            sup->leb_size, bi->vi.usable_leb_size);
                return -EINVAL;
        }
        if (sup->min_io_size > sup->leb_size ||
            sup->max_io_size > sup->leb_size ||
            sup->min_io_size > sup->max_io_size ||
            (sup->max_io_size % sup->min_io_size) != 0 ||
            (sup->leb_size % sup->min_io_size) != 0 ||
            (sup->leb_size % sup->max_io_size) != 0) {
                bilbyfs_err("Invalid leb_size/min_io_size/max_io_size "
                            "combinaison: "
                            "(leb_size = %d, max_io_sz = %d, min_io_sz = %d)",
                            sup->leb_size, sup->max_io_size, sup->min_io_size);
                return -EINVAL;
        }
        if (sup->leb_cnt < sup->nb_reserved_gc + sup->nb_reserved_del + BILBYFS_MIN_USABLE_LOG_SZ) {
                bilbyfs_err("Number of erasble-blocks too small for nb_(eb|gc|del) and min_usable_log_sz "
                            "(leb_cnt = %d, nb_gc = %d, nb_del = %d, min_usable_log_sz = %d)\n",
                            sup->leb_cnt, sup->nb_reserved_gc, sup->nb_reserved_del, BILBYFS_MIN_USABLE_LOG_SZ);
                return -EINVAL;
        }

        return 0;
}

/**
 * A list list to store deletion objects and their addresses at mount time 
 */
struct list_obj_del {
        u8 type;
        obj_id id;
        struct obj_addr addr;
        struct list_obj_del *next;
};

static int add_to_del_list(struct list_obj_del **del_list, obj_id id, struct obj_addr *addr)
{
        struct list_obj_del *node;

        node = kmalloc(sizeof(*node));
        if (!node)
                return -ENOMEM;

        node->id = id;
        memcpy(&node->addr, addr, sizeof(*addr));

        node->next = *del_list;
        *del_list = node;

        return 0;
}

static void clean_del_list(struct list_obj_del *del_list)
{
        struct list_obj_del *curr, *next;
        curr = del_list;

        while (curr != NULL) {
                next = curr->next;
                kfree(curr);
                curr = next;
        }
}

/* check_trans_pos: Checks whether the transaction attribute @pos is
 * valid.
 * @trans_nb_obj: current number of elements in the transaction
 * @pos: transaction attribute of last element read
 *
 * This function returns %-EINVAL if the attribute is invalid, it
 * returns 1 if it's the last element of the transaction, 0 if more
 * objects are expected.
 */
static int check_trans_pos(int trans_nb_obj, u8 pos)
{
        switch (pos) {
        case BILBYFS_TRANS_ATOM:
                if (trans_nb_obj)
                        return -EINVAL;
                return  1;
        case BILBYFS_TRANS_ST:
                if (trans_nb_obj)
                        return -EINVAL;
                return 0;
        case BILBYFS_TRANS_IN:
                if (!trans_nb_obj)
                        return -EINVAL;
                return 0;
        case BILBYFS_TRANS_END:
                if (!trans_nb_obj)
                        return -EINVAL;
                return 1;
        default:
                bilbyfs_err("Unknown trans pos value %x", pos);
                return -EINVAL;
        }
}

/* mount_scan_rbuf: Scan every object stored in a read-buffer
 * @bi: global fs info
 * @addr: address to start with
 * @rbuf: read-buffer to scan
 * @del_list: a list to store the deletion objects
 *
 * This function returns a negative error-code if unsuccessful.
 */
static int mount_scan_rbuf(struct bilbyfs_info *bi, struct obj_addr *addr,
                           struct bilbyfs_rbuf *rbuf, struct list_obj_del **del_list)
{
        struct obj_addr *addrs;
        struct obj_ch *obj;
        int trans_nb_obj = 0;
        int last;
        int err;
        int i;

        bilbyfs_assert(addr->len == 0);
        addrs = bi->addrs;
        if (!addrs)
                return -ENOMEM;

        for (obj = wbuf_next_obj_addr(bi, addr, rbuf);
             !IS_ERR(obj);
             obj = wbuf_next_obj_addr(bi, addr, rbuf)) {
                bilbyfs_debug("mount_scan_rbuf() loop obj->type = %d nb_obj_in_trans=%d\n", obj->type, trans_nb_obj);
                last = check_trans_pos(trans_nb_obj, obj->trans);
                /* Invalid transaction value */
                if (last < 0) {
                        bilbyfs_err("Invalid trans pos value 0x%x, this may just"
                                    "be because of a power-failure.", obj->trans);
                        trans_nb_obj = 0;
                        continue;
                }

                /* We enqueue all the objects of a transaction */
                memcpy(&addrs[trans_nb_obj], addr, sizeof(*addr));
                trans_nb_obj++;
                if (!last) {
                        if (trans_nb_obj == BILBYFS_MAX_OBJ_PER_TRANS) {
                                bilbyfs_err("Invalid transaction with too many objects (%d"
                                            "objects, limit=%d)", trans_nb_obj,
                                            BILBYFS_MAX_OBJ_PER_TRANS);
                                trans_nb_obj = 0;
                        }
                        continue;
                }
                /* This was the last object of the transaction,
                 * will process all the objects.
                 * Note: deletion objects are saved in a list and will be processed later.
                 */
                err = allocpool_alloc(&bi->node_pool, trans_nb_obj * 2, NODE_SIZE);
                if (err)
                        return err;
                for (i = 0; i < trans_nb_obj; i++) {
                        obj = rbuf->buf + addrs[i].offs;
                        if (obj->type == BILBYFS_DEL_OBJ)
                                err = add_to_del_list(del_list, get_obj_id(obj), &addrs[i]);
                        else if (obj->type == BILBYFS_PAD_OBJ)
                                err = proc_obj(bi, obj->type, 0, &addrs[i]);
                        else if  (obj->type != BILBYFS_SUM_OBJ)
                                err = proc_obj(bi, obj->type, get_obj_id(obj), &addrs[i]);

                        if (err) {
                                allocpool_empty(&bi->node_pool);
                                return err;
                        }
                }
                trans_nb_obj = 0;
                allocpool_empty(&bi->node_pool);
        }

        err = PTR_ERR(obj);
        return err;
}

int mount_proc_sum(struct bilbyfs_info *bi, u32 lnum, struct obj_sum *sum, u32 maxsz, struct list_obj_del **del_list)
{
        int i;
        int err;
        struct obj_addr addr;
        struct obj_sum_entry *entry;
        obj_id id;
        u32 tot_used = 0;

        addr.lnum = lnum;
        err = check_obj_header(&sum->ch, maxsz);
        if (err)
                return err;
        if (sum->ch.type != BILBYFS_SUM_OBJ) {
                bilbyfs_debug("Summary object expected, found %d\n", sum->ch.type);
                return -EINVAL;
        }
        for (i = 0; i < le32_to_cpu(sum->nb_sum_entry); i++) {
                entry = &sum->entries[i];
                addr.offs = obj_sum_entry_offs(entry);
                addr.len = le32_to_cpu(entry->len);
                tot_used += addr.len;
                addr.sqnum = le64_to_cpu(entry->sqnum);
                id = le64_to_cpu(entry->id);
                // bilbyfs_debug("sum_entry{.offs = %u, .len = %u, .sqnum = %llu, .oid = %llu, .is_del=%u}\n", obj_sum_entry_offs(entry), le32_to_cpu(entry->len), le64_to_cpu(entry->sqnum), le64_to_cpu(entry->id), obj_sum_entry_is_del(entry));
                if (obj_sum_entry_is_del(entry)) {
                        err = add_to_del_list(del_list, id, &addr);
                        if (err)
                                return err;
                } else {
                        err = proc_obj(bi, type_from_id(id), id, &addr);
                        if (err)
                                return err;
                }
                gim_mark_garbage_cnt(bi, id, &addr, (u32) cpu_to_le16(entry->count), NULL);
        }
        addr.lnum = lnum;
        addr.len = bi->super.leb_size - tot_used;
        fsm_mark_dirty(bi, &addr);
        return 0;
}

static inline int mount_init_log(struct bilbyfs_info *bi, struct list_obj_del **del_list)
{
        struct bilbyfs_rbuf rbuf;
        struct obj_addr addr;
        int err;

        rbuf.buf = bi->wbuf.buf;
        rbuf.size = bi->wbuf.size;
        rbuf.offs = 0;
        bi->fsm_lnum = bi->super.log_lnum;
        fsm_mark_used(bi, bi->fsm_lnum);
        err = wbuf_read_leb(bi, bi->super.log_lnum, &rbuf);
        if (err)
                return err;
        addr.lnum = bi->fsm_lnum;
        addr.offs = 0;
        addr.len = 0;
        err = mount_scan_rbuf(bi, &addr, &rbuf, del_list);
        if (err == -ENOENT) {
                bi->wbuf.sync_offs = addr.offs + addr.len;
                bi->wbuf.used = addr.offs + addr.len;
                bi->wbuf.avail = bi->super.leb_size - bi->wbuf.used;
        } else if (err) {
                clean_del_list(*del_list);
                return err;
        } else { /* mount_scan_rbuf didn't fail, erase-block is full of valid data */
                bi->wbuf.sync_offs = bi->super.leb_size;
                bi->wbuf.used = bi->super.leb_size;
                bi->wbuf.avail = 0;
        }
        bi->wbuf.buf = rbuf.buf;
        if (bi->wbuf.sync_offs  != bi->super.log_offs) {
                bilbyfs_err("super.log_offs is different from the content of the erase-block %d, %d != %d\n", bi->super.log_lnum, bi->wbuf.sync_offs, bi->super.log_offs);
        }
        return 0;
}

static int mount_scan(struct bilbyfs_info *bi)
{
        struct obj_addr addr;
        struct list_obj_del *del_list = NULL;
        struct list_obj_del *curr;
        int err = 0;
        u32 sum_offs;
        /* struct timeval st, stp; */

        bilbyfs_debug("mount_scan(): Scanning each LEB\n");
        /*
        if (bi->super.log_lnum > 0) {
                err = mount_init_log(bi, &del_list);
                if (err)
                        return err;
        }
        */
        bilbyfs_err("BilbyFs mount start\n");
        bi->nb_pages = 0;
        bi->nb_extra_pages = 0;
        bi->node_pool.tot_nodes_needed = 0;
        bi->gim_allocated_for_nothing = 0;
        for (addr.lnum = BILBYFS_LOG_FST_LNUM;
             addr.lnum < bi->super.leb_cnt;
             addr.lnum++) {
                if (!ubi_is_mapped(bi->ubi, addr.lnum) /* || addr.lnum == bi->super.log_lnum */)
                        continue;
                fsm_mark_used(bi, addr.lnum);
                if (!bi->no_summary) {
                        /*
                        do_gettimeofday(&st);
                        */
                        err = wbuf_read_sum(bi, addr.lnum, &bi->rbuf, &sum_offs);
                        /*
                        do_gettimeofday(&stp);
                        pr_err("timed wbuf_read_sum() : %ld sec %ld usec\n", stp.tv_sec - st.tv_sec, stp. tv_usec - st.tv_usec);
                        */
                        if (!err) {
                         /*       do_gettimeofday(&st); */
                                err = mount_proc_sum(bi, addr.lnum, (struct obj_sum *)(bi->rbuf.buf + sum_offs), 
                                                     bi->super.leb_size - sum_offs, &del_list);
                        /*
                                do_gettimeofday(&stp);
                                pr_err("timed mount_proc_sum() : %ld sec %ld usec\n", stp.tv_sec - st.tv_sec, stp. tv_usec - st.tv_usec);
                        */
                                if (err)
                                        return err;
                                continue;
                        }
                        bilbyfs_err("Failure to use the summary, fall back to scanning the erase-block (lnum=%d), err = %d\n", addr.lnum, err);
                        if (err != -ENOENT)
                                return err;
                }
                err = wbuf_read_leb(bi, addr.lnum, &bi->rbuf);
                if (err) {
                        clean_del_list(del_list);
                        return err;
                }
                addr.offs = 0;
                addr.len = 0;
                err = mount_scan_rbuf(bi, &addr, &bi->rbuf, &del_list);
                if (err == -ENOENT) {
                        addr.offs += addr.len;
                        addr.len = bi->super.leb_size - addr.offs;
                        fsm_mark_dirty(bi, &addr);
                } else if (err) {
                        clean_del_list(del_list);
                        return err;
                }
        }

        bilbyfs_debug("mount_scan(): Processing deletion objects\n");
        /* do_gettimeofday(&st); */
        for (curr = del_list; curr; curr = curr->next) {
                err = proc_obj(bi, BILBYFS_DEL_OBJ, curr->id, &curr->addr);
                if (err) {
                        clean_del_list(del_list);
                        return err;
                }
        }

        clean_del_list(del_list);
        /*
        do_gettimeofday(&stp);
        pr_err("timed del_obj_proc() : %ld.%ld\n", stp.tv_sec - st.tv_sec, stp. tv_usec - st.tv_usec);
        */

        bilbyfs_err("BilbyFs mount finished pages = %d, extra_pages = %d, tot_nodes = %d, gim_allocated_for nothing = %d\n", bi->nb_pages, bi->nb_extra_pages, bi->node_pool.tot_nodes_needed, bi->gim_allocated_for_nothing);
        return 0;
}

/* Move this to wbuf? */
static int check_flash_empty(struct bilbyfs_info *bi)
{
        int empty = 1;
        int lnum;
        int err;

        for (lnum = 0; lnum < bi->super.leb_cnt; lnum++) {
                err = ubi_is_mapped(bi->ubi, lnum);
                if (err < 0)
                        return err;
                if (err == 1) {
                        empty = 0;
                        break;
                }
        }
        return empty;
}

int ostore_mount(struct bilbyfs_info *bi)
{
        int empty;
        int err;

        empty = check_flash_empty(bi);
        if (empty < 0) {
                err = empty;
        } else if (empty) {
                return -ENODATA;
        } else {
                err = mount_read_super(bi);
                if (!err) {
                        err = mount_check_super(bi);
                        if (!err) {
                                bi->is_mounting = true;
                                bi->addrs = kmalloc(sizeof(*(bi->addrs)) * BILBYFS_MAX_OBJ_PER_TRANS);
                                if (!bi->addrs)
                                        return -ENOMEM;
                                err = allocpool_alloc(&bi->node_pool, 10000, NODE_SIZE);
                                if (err) {
                                        kfree(bi->addrs);
                                        return err;
                                }
                                err = mount_scan(bi);
                                allocpool_empty(&bi->node_pool);
                                kfree(bi->addrs);
                                bi->is_mounting = false;
                                if (!err)
                                        return 0;
                        }
                } else if (err == -ENOENT) {
                        bilbyfs_err("Not a BilbyFs file system!\n");
                }
        }
        ostore_unmount(bi);
        return err;
}

void ostore_unmount(struct bilbyfs_info *bi)
{
        int err;

        /* We write a new super object only if we have written objects to the
         * media since the last update. (i.e. the last written object is not
         * the super block).
         */
        if (bi->super.sqnum + 1 < bi->next_sqnum) {
                err = ostore_sync(bi, true);
                if (err) {
                        bilbyfs_err("Could not synchronize FS when unmounting.\n");
                }
                err = ostore_write_super(bi);
                if (err)
                        bilbyfs_err("Could not write the super object %d\n", err);
                else
                        bilbyfs_debug("ostore_unmount(): super block written\n");
        }
}

