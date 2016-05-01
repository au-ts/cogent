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

static u8 inode_mode_to_dent_type(umode_t mode)
{
        switch (mode & S_IFMT) {
        case S_IFREG:  return BILBYFS_ITYPE_REG;
        case S_IFDIR:  return BILBYFS_ITYPE_DIR;
        case S_IFLNK:  return BILBYFS_ITYPE_LNK;
        case S_IFSOCK: return BILBYFS_ITYPE_SOCK;
        case S_IFIFO:  return BILBYFS_ITYPE_FIFO;
        case S_IFBLK:  return BILBYFS_ITYPE_BLK;
        case S_IFCHR:  return BILBYFS_ITYPE_CHR;
        default: bilbyfs_assert(0);
        }
        return 0;
}

int check_obj_header(void *obj, int max_obj_sz)
{
        struct obj_ch *ch = obj;
        u32 offs;
        u32 crc;

        if (max_obj_sz < BILBYFS_CH_SZ)
                return -ENOENT;
        if (le32_to_cpu(ch->magic) != BILBYFS_OBJ_MAGIC) 
                return -ENOENT;
        if (le32_to_cpu(ch->len) < BILBYFS_CH_SZ ||
            le32_to_cpu(ch->len) > max_obj_sz) {
                bilbyfs_err("Invalid object size (%d vs %d)", le32_to_cpu(ch->len), max_obj_sz);
                return -EINVAL;
        }
        offs = offsetof(struct obj_ch, crc) + sizeof(ch->crc);
        crc = crc32(BILBYFS_CRC32_INIT, obj + offs, le32_to_cpu(ch->len) - offs);
        if (crc != le32_to_cpu(ch->crc)) {
                bilbyfs_err("Invalid CRC32 for object %x != %x, obj->type=%d\n", crc, le32_to_cpu(ch->crc), ch->type);
                return -EINVAL;
        }
        /* FIXME: More sanity checking?? */
        return 0;
}

void pack_obj_header(void *obj, u64 sqnum, u8 trans_pos)
{
        struct obj_ch *ch = obj;
        uint32_t crc;
        int offs;

        bilbyfs_assert(ch->type < BILBYFS_OBJ_TYPES_CNT);

        ch->magic = cpu_to_le32(BILBYFS_OBJ_MAGIC);
        ch->sqnum = cpu_to_le64(sqnum);
        ch->trans = trans_pos;
        zero_obj_ch_unused(ch);

        /* we CRC right after the field crc to the end of the object */
        offs = offsetof(struct obj_ch, crc) + sizeof(ch->crc);
        crc = crc32(BILBYFS_CRC32_INIT, obj + offs, le32_to_cpu(ch->len) - offs);
        ch->crc = cpu_to_le32(crc);
}

__le32 len_to_le32(int len)
{
        bilbyfs_assert(len >= BILBYFS_CH_SZ);
        return cpu_to_le32(ALIGN(len, BILBYFS_OBJ_PADDING));
}

void pack_obj_inode(struct obj_inode *ino, struct inode *inode)
{
        struct bilbyfs_inode *binode = inode_to_binode(inode);

        ino->ch.type = BILBYFS_INODE_OBJ;
        ino->ch.len = len_to_le32(BILBYFS_INODE_SZ);
        
        ino->id = cpu_to_le64(inode_id_init(inode->i_ino));
        ino->creat_sqnum = cpu_to_le64(binode->creat_sqnum);
        ino->size  = cpu_to_le64(inode->i_size);
        ino->atime_sec = cpu_to_le64(inode->i_atime.tv_sec);
        ino->ctime_sec = cpu_to_le64(inode->i_ctime.tv_sec);
        ino->mtime_sec = cpu_to_le64(inode->i_mtime.tv_sec);
        ino->nlink = cpu_to_le32(inode->i_nlink);
        ino->uid   = cpu_to_le32(i_uid_read(inode));
        ino->gid   = cpu_to_le32(i_gid_read(inode));
        ino->mode  = cpu_to_le32(inode->i_mode);
        ino->flags = cpu_to_le32(binode->flags);
        zero_obj_inode_unused(ino);
}

void pack_obj_dentarr(struct obj_dentarr *dentarr, obj_id id,
                      int nbdentry, int size)
{
        dentarr->ch.type = BILBYFS_DENTARR_OBJ;
        dentarr->ch.len = len_to_le32(size);

        dentarr->id = cpu_to_le64(id);
        dentarr->nb_dentry = cpu_to_le32(nbdentry);
        dentarr->size = cpu_to_le32(size);
        zero_obj_dentarr_unused(dentarr);
}

void pack_obj_data(struct obj_data *odata, obj_id id, int sz_data,
                   const void *data)
{
        odata->ch.type = BILBYFS_DATA_OBJ;
        odata->ch.len = len_to_le32(BILBYFS_DATA_SZ + sz_data);

        odata->id = cpu_to_le64(id);
        odata->size = cpu_to_le32(sz_data);
        memcpy(odata->data, data, sz_data);
        zero_obj_data_unused(odata);
}

void pack_obj_dentry(struct obj_dentry *de, struct inode *inode,
                     const char *name)
{
        de->ino = cpu_to_le32(inode->i_ino);
        de->type = inode_mode_to_dent_type(inode->i_mode);
        /* The dentry.nlen field does not include the \0 */
        de->nlen = cpu_to_le16(strlen(name));
        strcpy(de->name, name);
        zero_obj_dentry_unused(de);
}

void pack_obj_pad(struct obj_ch *pad, int pad_sz)
{
        pad->type = BILBYFS_PAD_OBJ;
        pad->len = len_to_le32(pad_sz);

        memset(pad + 1, BILBYFS_PAD_BYTE, pad_sz - BILBYFS_CH_SZ);
}

void unpack_obj_inode(struct inode *inode, struct obj_inode *ino)
{
        struct bilbyfs_inode *binode = inode_to_binode(inode);

        inode->i_flags |= (S_NOCMTIME | S_NOATIME);
        set_nlink(inode, le32_to_cpu(ino->nlink));
        i_uid_write(inode, le32_to_cpu(ino->uid));
        i_gid_write(inode, le32_to_cpu(ino->gid));
        inode->i_atime.tv_sec = (int64_t)le64_to_cpu(ino->atime_sec);
        inode->i_mtime.tv_sec = (int64_t)le64_to_cpu(ino->mtime_sec);
        inode->i_ctime.tv_sec = (int64_t)le64_to_cpu(ino->ctime_sec);
        inode->i_mode = le32_to_cpu(ino->mode);
        inode->i_size = le64_to_cpu(ino->size);

        binode->flags       = le32_to_cpu(ino->flags);
        binode->creat_sqnum = le64_to_cpu(ino->creat_sqnum);
}

void pack_obj_super(struct obj_super *super, const struct bilbyfs_super *bsuper)
{
        super->ch.type = BILBYFS_SUP_OBJ;
        super->ch.len = len_to_le32(BILBYFS_SUPER_SZ);

        super->flags = cpu_to_le32(bsuper->flags);
        super->leb_cnt = cpu_to_le32(bsuper->leb_cnt);
        super->nb_reserved_del = cpu_to_le32(bsuper->nb_reserved_del);
        super->nb_reserved_gc = cpu_to_le32(bsuper->nb_reserved_gc);
        super->leb_size = cpu_to_le32(bsuper->leb_size);
        super->log_head_leb = cpu_to_le32(bsuper->log_lnum);
        super->log_head_offs = cpu_to_le32(bsuper->log_offs);
        super->lowest_sqnum = cpu_to_le64(bsuper->lowest_sqnum);
        zero_obj_super_unused(super);
}

void unpack_obj_super(struct bilbyfs_super *bsuper, struct obj_super *super)
{
        bsuper->sqnum = le64_to_cpu(super->ch.sqnum);
        bsuper->flags = le32_to_cpu(super->flags);
        bsuper->leb_cnt = le32_to_cpu(super->leb_cnt);
        bsuper->nb_reserved_del = le32_to_cpu(super->nb_reserved_del);
        bsuper->nb_reserved_gc = le32_to_cpu(super->nb_reserved_gc);
        bsuper->leb_size = le32_to_cpu(super->leb_size);
        bsuper->log_lnum = le32_to_cpu(super->log_head_leb);
        bsuper->log_offs = le32_to_cpu(super->log_head_offs);
        bsuper->lowest_sqnum = le64_to_cpu(super->lowest_sqnum);
        bsuper->last_inum = le64_to_cpu(super->last_inum);
}

void pack_obj_del(void *obj, obj_id id)
{
        struct obj_del *del = (struct obj_del *) obj;

        del->ch.type = BILBYFS_DEL_OBJ;
        del->ch.len = len_to_le32(BILBYFS_DEL_SZ);

        del->id = cpu_to_le64(id);

        zero_obj_del_unused(del);
}

void pack_obj_sum(struct obj_sum *sum, u32 offs)
{
        u32 len = obj_sum_size(sum);

        sum->ch.type = BILBYFS_SUM_OBJ;
        sum->ch.len = len_to_le32(len);
        memset((void *)sum + len, BILBYFS_PAD_BYTE, le32_to_cpu(sum->ch.len) - len);
        *obj_sum_offs(sum) = cpu_to_le32(offs);

        zero_obj_sum_unused(sum);
}
