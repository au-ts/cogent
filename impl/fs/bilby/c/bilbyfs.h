/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef __BILBYFS_H__
#define __BILBYFS_H__

#include <wrapper.h>

#define bilbyfs_assert(v) BUG_ON(!(v))

#define bilbyfs_err(...) \
        printk(KERN_ERR __VA_ARGS__)

#define bilbyfs_msg(...) \
        printk(KERN_INFO __VA_ARGS__)

#ifndef BILBYFS_DEBUG
#define bilbyfs_debug(...) \
        do {} while (0)
#else
#define bilbyfs_debug(...) \
        printk(KERN_ERR __VA_ARGS__)
#endif /* !BILBYFS_DEBUG */

#define BILBYFS_SUPER_MAGIC     0x0b17b9f5
#define BILBYFS_ROOT_INO        24
#define BILBYFS_FIRST_SQNUM     1 /* Must be greater than 0 */
#define BILBYFS_FIRST_INO   (BILBYFS_ROOT_INO + 1)
#define BILBYFS_SUP_LNUM       0
#define BILBYFS_LOG_FST_LNUM    3
#define BILBYFS_MIN_USABLE_LOG_SZ 2
#define BILBYFS_MAX_READDIR_DATA_SIZE 64
#define BILBYFS_BD_MAX_NLEN 16 /* maximum length of block device */
#define BILBYFS_MAX_NLEN 255 /* maximum length of a file name */
#define BILBYFS_DEFAULT_NB_RESERVED_GC 3
#define BILBYFS_DEFAULT_NB_RESERVED_DEL 3


#define BILBYFS_OBJ_MAGIC 0xb17b9f50
#define BILBYFS_PAD_BYTE  0x42
#define BILBYFS_OBJ_PADDING  8
#define BILBYFS_CRC32_INIT 0xFFFFFFFFU

#define BILBYFS_TRUE (1)
#define BILBYFS_FALSE (0)

/*
 * BILBYFS inode types.
 *
 * BILBYFS_ITYPE_REG: regular file
 * BILBYFS_ITYPE_DIR: directory
 * BILBYFS_ITYPE_LNK: soft link
 * BILBYFS_ITYPE_BLK: block device node
 * BILBYFS_ITYPE_CHR: character device node
 * BILBYFS_ITYPE_FIFO: fifo
 * BILBYFS_ITYPE_SOCK: socket
 * BILBYFS_ITYPES_CNT: count of supported file types
 */
enum {
        BILBYFS_ITYPE_REG,
        BILBYFS_ITYPE_DIR,
        BILBYFS_ITYPE_LNK,
        BILBYFS_ITYPE_BLK,
        BILBYFS_ITYPE_CHR,
        BILBYFS_ITYPE_FIFO,
        BILBYFS_ITYPE_SOCK,
        BILBYFS_ITYPES_CNT,
};

/*
 * Object types.
 *
 * BILBYFS_INODE_OBJ: inode object
 * BILBYFS_DATA_OBJ: data object
 * BILBYFS_DENTARR_OBJ: directory entry array object
 * BILBYFS_PAD_OBJ: padding object
 * BILBYFS_OBJ_TYPES_CNT: count of supported object types
 *
 * Note: we use these constants for id types as well.
 * Directory entry array (dentarr) is a collection of obj_dentry
 * see the definition of obj_dentry.
 */
enum {
        BILBYFS_INODE_OBJ,
        BILBYFS_DATA_OBJ,
        BILBYFS_DENTARR_OBJ,
        BILBYFS_SUP_OBJ,
        BILBYFS_PAD_OBJ,
        BILBYFS_DEL_OBJ,
        BILBYFS_SUM_OBJ,
        BILBYFS_OBJ_TYPES_CNT,
};

/* Object inode flags (on-flash inode flags)
 * BILBYFS_ORPHAN_INODE: orhpan inode flag
 */
enum {
        BILBYFS_ORPHAN_FL       = 0x01,
        BILBYFS_APPEND_FL       = 0x02,
        BILBYFS_IMMUTABLE_FL    = 0x04,
};

/* Super object flags
 * BILBYFS_SUP_ISDIRTY: was the file system unmount cleanly?
 */
enum {
        BILBYFS_SUP_ISDIRTY     = 0x01,
};

/* obj_id: id to retrieve an object from the index.
 * This id is 64 bits long organised differently for each
 * type of object:
 * - inode: inode number (32 bits), zero (32 bits)
 * - dentarr: inode number (32 bits), type dentry (3 bits), name hash (29 bits)
 * - data: inode number (32 bits), type data (3 bits), block index (29 bits)
 */
typedef u64 obj_id;
typedef __le64 __le_obj_id; /* little endian version: as we store it on the media */

/* NIL_ID: Key returned by next_obj_id() when the id passed as argument is the
 * highest id present in the index: there is no next id.
 */
#define NIL_ID ((u64)~0)

/* Number of bits available to store extra information in an id */
#define BILBYFS_ID_XINFO_BITS 29
#define BILBYFS_ID_XINFO_MASK 0x1FFFFFF

#define BILBYFS_MAX_FILE_SZ (1ULL << (BILBYFS_ID_XINFO_BITS + BILBYFS_BLOCK_SHIFT))

/* inum_from_id: extract the inode number from an id
 * @id: id to analyse
 * Returns the inode number of the id.
 */
static inline ino_t inum_from_id(obj_id id)
{
        return id >> 32;
}
/* type_from_id: extract the type of an id
 * @id: id to analyse
 * Returns the type of the id (BILBYFS_INODE_OBJ, BILBYFS_DATA_OBJ...).
 */
static inline u32 type_from_id(obj_id id)
{
        return (id >> BILBYFS_ID_XINFO_BITS) & 7;
}

static inline u32 xinfo_from_id(obj_id id)
{
        return (id & BILBYFS_ID_XINFO_MASK);
}

/* inode_id_init: Initialise an inode id.
 * ino: inode number of the id
 * returns the id
 */
static inline obj_id inode_id_init(ino_t ino)
{
        obj_id id = (u64)ino << 32;
        return id;
}

/**
 * id_hash_nm - R5 hash function (borrowed from reiserfs).
 * @s: dentry name
 * @len: name length
 */
static inline uint32_t id_hash_nm(const char *s, int len)
{
        uint32_t a = 0;
        const signed char *str = (const signed char *)s;

        while (*str) {
                a += *str << 4;
                a += *str >> 4;
                a *= 11;
                str++;
        }
        return (a & BILBYFS_ID_XINFO_MASK);
}

/* dentarr_id_init: Initialise an `dentry array' id.
 * ino: inode number of the id
 * returns the id
 */
static inline obj_id dentarr_id_init(ino_t ino, const char *name)
{
        obj_id id = (u64)ino << 32 |
                (BILBYFS_DENTARR_OBJ << BILBYFS_ID_XINFO_BITS) |
                id_hash_nm(name, strlen(name));
        return id;
}

/* data_id_init: Initialise an data id.
 * ino: inode number of the id
 * block: block index number
 * returns the id
 */
static inline obj_id data_id_init(ino_t ino, u32 block)
{
        obj_id id = (u64)ino << 32 |
                (BILBYFS_DATA_OBJ << BILBYFS_ID_XINFO_BITS) |
                block;
        return id;
}


/* is_inode_id: assess if the id is a inode id
 * @id: id to assess
 * Returns 1 if id is a inode id 0 otherwise
 */
static inline int is_inode_id(obj_id id)
{
        return (type_from_id(id) == BILBYFS_INODE_OBJ);
}

/* is_dentarr_id: assess if the id is a `dentry array' id
 * @id: id to assess
 * Returns 1 if id is a `dentry array' id 0 otherwise
 */
static inline int is_dentarr_id(obj_id id)
{
        return (type_from_id(id) == BILBYFS_DENTARR_OBJ);
}

/* is_data_id: assess if the id is a data id
 * @id: id to assess
 * Returns 1 if id is a data id 0 otherwise
 */
static inline int is_data_id(obj_id id)
{
        return (type_from_id(id) == BILBYFS_DATA_OBJ);
}

/* struct obj_addr: Address of an object on-disk
 * @lnum: logical-erase block number
 * @offs: offset inside the logical-erase block
 * @len: length of the object
 */
struct obj_addr {
        u32 lnum;
        u32 offs;
        u32 len;
        u64 sqnum;
};

/*
 * struct bilbyfs_wbuf - BilbyFs write-buffer.
 * @buf: write-buffer (of min. flash I/O unit size)
 * @size: write-buffer size (in [@c->min_io_size, @c->max_write_size] range)
 * @avail: number of bytes available in the write-buffer
 * @used:  number of used bytes in the write-buffer
 * @sync_offs: offset to which data was synchronised to disk
 *
 */
struct bilbyfs_wbuf {
        void *buf;
        int size;
        int avail;
        int used;
        int sync_offs;
};

/*
 * struct bilbyfs_rbuf - BilbyFs read-buffer.
 * @buf: buffer of leb_size
 * @offs: read-buffer offset in this logical eraseblock
 * @size: read-buffer size (usually leb_size)
 */
struct bilbyfs_rbuf {
        void *buf;
        int size;
        int offs;
};

/* struct bilbyfs_inode: in-memory inode representation
 * @vfs_inode: VFS inode is embedded and MUST be the first field for
 * container_of to work.
 * @creat_sqnum: sequence number generated when the inode was created
 * @flags: flags that will be stored on flash
 */
struct bilbyfs_inode {
        struct inode vfs_inode;
        u64 creat_sqnum;
        int flags;
};

/* inode_to_binode: obtain a bilbyfs_inode from a VFS inode.
 * @inode: inode to introspect
 * Returns the bilbyfs_inode pointer attached to @inode.
 */
static inline struct bilbyfs_inode *inode_to_binode(struct inode *inode)
{
        return (void *)inode;
}

static inline void inode_init_perm(struct inode *inode, const struct inode *dir,
                                   umode_t mode)
{
	inode->i_uid = current_fsuid();
	if (dir && dir->i_mode & S_ISGID) {
		inode->i_gid = dir->i_gid;
		if (S_ISDIR(mode))
			mode |= S_ISGID;
	} else
		inode->i_gid = current_fsgid();
	inode->i_mode = mode;
}

/* struct bilbyfs_dirent: Generic directory entry structure used for readdir
 * The structure allows to abstract away the Linux VFS filldir callback.
 * @d_ino: inode number the directory entry is pointing to
 * @d_off: offset of the directory entry in the directory
 * @d_reclen: length of the name
 * @d_type: type of inode (DT_REG, DT_DIR, DT_LNK...)
 * @d_name: name of the (file/directory/link...)
 */
struct bilbyfs_dirent {
        unsigned long   d_ino;
        unsigned long   d_off;
        unsigned short  d_reclen;
        unsigned int    d_type;
        char            d_name[BILBYFS_MAX_NLEN];
};

/* struct bilbyfs_super: in-memory superblock object representation
 * @uuid: UUID from superblock
 * @flags: (%BILBYFS_SUP_ISDIRTY, ...)
 * @sqnum: sequence number of the super object, is the highest one if the FS was
 *         cleanly unmounted.
 * @leb_size: size of a LEB for the media.
 * @leb_cnt: number of LEB for the fs.
 * @nb_reserved_gc: number of LEB reserved for GC
 * @nb_reserved_del: number of LEB reserved for deletion
 * @min_io_size: minimum amount of data we can write in a LEB in one go
 * @max_io_size: maximum amount of data we can write in a LEB in one go
 * @log_lnum: last erase-block number in the log (likely partially written)
 * @log_offs: offset in the last erase-block of the log.
 * @lowest_sqnum: lowest sqnum of a valid object on-flash (therefore indexed)
 * @last_inum: last inode number used when unmount (next one is +1).
 */
struct bilbyfs_super {
        u8 uuid[16];
        u32 flags;
        u64 sqnum;
        int leb_cnt;
        int leb_size;
        int nb_reserved_gc;
        int nb_reserved_del;
        int min_io_size;
        int max_io_size;
        u32 log_lnum;
        u32 log_offs;
        u64 lowest_sqnum;
        u64 last_inum;
};

/* Red-Black tree node */
struct rbt_node {
	unsigned long  rbt_parent_color;
#define	RBT_RED		0
#define	RBT_BLACK	1
        struct rbt_node *rbt_left;
        struct rbt_node *rbt_right;
};

struct rbt_root {
        struct rbt_node *rbt_node;
};

/* idx_node: Node index
 * node: red-black tree node
 * addr: address and sqnum of the object stored in the index
 */
struct idx_node {
        struct rbt_node node;
        struct obj_addr addr;
        obj_id id;
};

/* gim_node: Node for GIM tree
 * @node: red-black tree node
 * @id: object id
 * @sqnum: sequence number of the newest garbage object
 * @count: number of objects with the same id
 */
struct gim_node {
        struct rbt_node node;
        obj_id id;
        u64 sqnum;
        u32 count;
};

#define NODE_SIZE max(sizeof(struct idx_node), sizeof(struct gim_node))

/* alloc_pool: Pool of pre-allocated content
 * @arr:  array of content
 * @len: length of array of content
 */
struct alloc_pool {
        int tot_nodes_needed;
        void **arr;
        int len;
        int i;
        int sz_obj;
};

/*
 * Transactional object store flags
 * BILBYFS_TRANS_ST: first object of a transaction with multiple objects
 * BILBYFS_TRANS_IN: object in a transaction that is not the first nor the last
 *                   one
 * BILBYFS_TRANS_END: last object of a transaction
 * BILBYFS_TRANS_ATOM: transaction of a single object
 *
 * Valid sequences pattern: (ST IN* END | ATOM)
 */
enum {
        BILBYFS_TRANS_ST  = 0x1,
        BILBYFS_TRANS_IN  = 0x2,
        BILBYFS_TRANS_END = 0x4,
        BILBYFS_TRANS_ATOM = 0x1 | 0x4,
};

/**
 * struct obj_ch - object common header.
 * @magic: object magic number (%BILBYFS_NODE_MAGIC)
 * @crc: CRC-32 checksum of the object header
 * @sqnum: sequence number
 * @len: full object length (including this header)
 * @type: object type (%BILBYFS_INODE_OBJ, %BILBYFS_EXPR_OBJ...)
 * @trans: position in transaction (%BILBYFS_TRANS_*)
 * @padding: reserved for future, zeroes
 *
 * Every object on-flash starts with this common part. If the object has an id, the
 * id always goes next.
 */
struct obj_ch {
        __le32 magic;
        __le32 crc;
        __le64 sqnum;
        __le32 len;
        __u8  type;
        __u8  trans;
        __u8  padding[2];
} __packed;

static inline void zero_obj_ch_unused(struct obj_ch *ch)
{
        memset(ch->padding, 0, 2);
}

/**
 * struct obj_inode - inode object.
 * @ch: common header
 * @id: object id
 * @creat_sqnum: sequence number at time of creation
 * @size: inode size in bytes
 * @atime_sec: access time seconds
 * @ctime_sec: creation time seconds
 * @mtime_sec: modification time seconds
 * @nlink: number of hard links
 * @uid: owner ID
 * @gid: group ID
 * @mode: access flags, inode type...
 * @flags: BILBYFS_ORPHAN_FL, BILBYFS_APPEND_FL...
 */
struct obj_inode {
        struct obj_ch ch;
        __le_obj_id id;
        __le64 creat_sqnum;
        __le64 size;
        __le64 atime_sec;
        __le64 ctime_sec;
        __le64 mtime_sec;
        __le32 nlink;
        __le32 uid;
        __le32 gid;
        __le32 mode;
        __le32 flags;
        __le32 padding;
} __packed;

static inline void zero_obj_inode_unused(struct obj_inode *ino)
{
        ino->padding = 0;
}

/**
 * struct obj_dentarr - `directory entry array' object.
 * @ch: common header
 * @id: object id
 * @nb_dentry: number of dentry object in the array (i.e. hash collisions)
 * @size: size in bytes of the obj_dentarr including the header (ch) but as
 * opposed to ch.len, @size is not aligned.
 */
struct obj_dentarr {
        struct obj_ch ch;
        __le_obj_id id;
        __le32 nb_dentry;
        __le32 size;
} __packed;

static inline void zero_obj_dentarr_unused(struct obj_dentarr *dentarr)
{
}

/* struct obj_dentry - directory entry object.
 * @ino: target inode number
 * @type: type of the target inode (%BILBYFS_ITYPE_REG, %BILBYFS_ITYPE_DIR, etc)
 * @nlen: name length
 * @name: zero-terminated name
 *
 * No padding here for simplicity.
 */
struct obj_dentry {
        __le32 ino;
        __u8 type;
        __le16 nlen;
        __u8 name[];
} __packed;

static inline void zero_obj_dentry_unused(struct obj_dentry *de)
{
}

/**
 * struct obj_data - data object.
 * @ch: common header
 * @id: object id
 * @size: data size in bytes
 * @padding: reserved for future, zeroes
 * @data: data
 */
struct obj_data {
        struct obj_ch ch;
        __le_obj_id id;
        __le32 size;
        __u8 padding[4];
        __u8 data[];
} __packed;

static inline void zero_obj_data_unused(struct obj_data *data)
{
        memset(data->padding, 0, 4);
}

/**
 * struct obj_del - deletion object
 * @ch: common header
 * @id: id of the object which is deleted
 */
struct obj_del {
        struct obj_ch ch;
        __le_obj_id id;
} __packed;

static inline void zero_obj_del_unused(struct obj_del *del)
{
}

/**
 * struct obj_sum_entry - summary object
 * @id: obj id
 * @sqnum: sequence number of the object
 * @len: length of the object
 * @del_flag_and_offs: the most significant bit indicates whether this
 *  is a deletion entry, the rest of bits are the offset of the object
 *  within the erase-block.
 * @count: number of objects covered by deletion object (can't we use len
 *         for this for deletion objects? Their size is fixed isn't it?
 */
struct obj_sum_entry {
        __le_obj_id id;
        __le64 sqnum;
        __le32 len;
        __le32 del_flag_and_offs;
#define BILBYFS_SUM_ENTRY_DEL_FLAG_MASK 0x80000000
        __le16 count;
} __packed;

static inline void zero_obj_sum_entry_unused(struct obj_sum_entry *sum_entry)
{
}

static inline u32 obj_sum_entry_offs(struct obj_sum_entry *sum_entry)
{
        return (le32_to_cpu(sum_entry->del_flag_and_offs) & ~ BILBYFS_SUM_ENTRY_DEL_FLAG_MASK);
}

static inline u32 obj_sum_entry_is_del(struct obj_sum_entry *sum_entry)
{
        return !!(le32_to_cpu(sum_entry->del_flag_and_offs) & BILBYFS_SUM_ENTRY_DEL_FLAG_MASK);
}

/**
 * struct obj_sum - summary object
 * @ch: common header
 * @nb_sum_entry: number of entries in the summary
 * @entries: summary entries
 */
struct obj_sum {
        struct obj_ch ch;
        __le32 nb_sum_entry;
        struct obj_sum_entry entries[];
        /* __le32 offs; The very last word32 is an offset to the summary object */ 
#define BILBYFS_OBJ_SUM_OFFS_SZ 4
} __packed;

static inline void zero_obj_sum_unused(struct obj_sum *sum)
{}

static inline u32 *obj_sum_offs(struct obj_sum *sum)
{
        return (u32 *)((void *)sum + le32_to_cpu(sum->ch.len) - BILBYFS_OBJ_SUM_OFFS_SZ);
}

/* get_obj_id: Get the obj_id of an object
 * @obj: pointer to the object
 *
 * Note that only indexed objects have an ID.
 * Object ID has to be positioned right after the common header.
 */
static inline obj_id get_obj_id(void *obj)
{
        struct obj_ch *ch = obj;
        __le_obj_id *le_id = (__le_obj_id *)(ch + 1);

        bilbyfs_assert(ch->type == BILBYFS_INODE_OBJ ||
                       ch->type == BILBYFS_DENTARR_OBJ ||
                       ch->type == BILBYFS_DATA_OBJ ||
                       ch->type == BILBYFS_DEL_OBJ );
        return le64_to_cpu(*le_id);
}

/**
 * struct obj_super - super object.
 * @ch: common header
 * @flags: various flags (%BILBYFS_FS_DIRTY, etc)
 * @gc_lnum: LEB reserved for garbage collection
 * @total_free: total free space in bytes
 * @total_dirty: total dirty space in bytes
 * @total_used: total used space in bytes (includes only data LEBs)
 * @total_dead: total dead space in bytes (includes only data LEBs)
 * @total_dark: total dark space in bytes (includes only data LEBs)
 * @empty_lebs: number of empty logical eraseblocks
 * @leb_cnt: count of LEBs used by file-system
 * @nb_reserved_gc: Number of LEBs reserved for garbage collection
 * @log_head_leb: where was the head of log at last unmount
 * @log_head_offs: and its offset in the leb
 * @lowest_sqnum: Lowest valid sqnum on FS?
 * @last_inum: Last inode number generated
 */
struct obj_super {
        struct obj_ch ch;
#define BILBYFS_FS_DIRTY 0x1
        __le32 flags;
        __le32 gc_lnum;
        __le64 total_free;
        __le64 total_dirty;
        __le64 total_used;
        __le64 total_dead;
        __le64 total_dark;
        __le32 empty_lebs;
        __le32 leb_size;
        __le32 leb_cnt;
        __le32 nb_reserved_gc;
        __le32 nb_reserved_del;
        __le32 log_head_leb;
        __le32 log_head_offs;
        __le64 lowest_sqnum;
        __le64 last_inum;
        __u8   padding[4];
} __packed;

static inline void zero_obj_super_unused(struct obj_super *o)
{
        memset(o->padding, 0, 4);
}

/* Size of objects */
#define BILBYFS_CH_SZ           sizeof(struct obj_ch)
#define BILBYFS_INODE_SZ        sizeof(struct obj_inode)
#define BILBYFS_DATA_SZ         sizeof(struct obj_data)
#define BILBYFS_DENTARR_SZ      sizeof(struct obj_dentarr)
#define BILBYFS_SUPER_SZ        sizeof(struct obj_super)
/* Note: obj_dentry objects do NOT have a common header */
#define BILBYFS_DENTRY_SZ       sizeof(struct obj_dentry)
#define BILBYFS_DEL_SZ          sizeof(struct obj_del)
#define BILBYFS_SUM_SZ          sizeof(struct obj_sum)
#define BILBYFS_SUM_ENTRY_SZ    sizeof(struct obj_sum_entry)

/* BILBYFS_BLOCK_SIZE: Block granularity of the index and maximum amount
 * of data attached to a obj_data.
 */
#define BILBYFS_BLOCK_SIZE 4096
#define BILBYFS_BLOCK_SHIFT 12

/* Maximum object size (must all be aligned on 8) */
#define BILBYFS_MAX_DATA_SZ     (BILBYFS_DATA_SZ + BILBYFS_BLOCK_SIZE)
#define BILBYFS_MAX_DENTRY_SZ   (BILBYFS_DENTRY_SZ + BILBYFS_MAX_NLEN + 1)
/* Maximum number of entries stored in a dentarr.
 * We put this limitation to ensure that all transactions fits in a leb even
 * in the worst case scenario.
 */
#define BILBYFS_MAX_DENTARR_ENTRIES 16
#define BILBYFS_MAX_DENTARR_SZ (BILBYFS_DENTARR_SZ + \
                                BILBYFS_MAX_DENTARR_ENTRIES * BILBYFS_MAX_DENTRY_SZ)
/* dentarr clearly has the biggest obj size */
#define BILBYFS_MAX_OBJ_SZ BILBYFS_MAX_DENTARR_SZ
#define BILBYFS_MIN_OBJ_SZ BILBYFS_CH_SZ

/* Maximum number of object in one transaction
 * A transaction can span a whole erase-block, hence this number should
 * be large enough to commodate this
 */
#define BILBYFS_MAX_OBJ_PER_TRANS 2048

#define BILBYFS_LAST_INUM 0xFFFFFF00 /* max inode number */

static inline int obj_dentry_size(struct obj_dentry *de)
{
        return BILBYFS_DENTRY_SZ + le16_to_cpu(de->nlen) + 1;
}

static inline int obj_dentarr_size(struct obj_dentarr *dearr)
{
        return (!le32_to_cpu(dearr->size) ? BILBYFS_DENTARR_SZ : le32_to_cpu(dearr->size));
}

static inline int obj_dentry_size_from_nm(const char *name)
{
        return BILBYFS_DENTRY_SZ + strlen(name) + 1;
}

static inline int obj_dentarr_size_with_nm(struct obj_dentarr *dentarr,
                                           const char *name)
{
        return obj_dentarr_size(dentarr) + obj_dentry_size_from_nm(name);
}

static inline int obj_data_size_with_data(int data_size)
{
        return BILBYFS_DATA_SZ + data_size;
}

static inline int obj_sum_size(struct obj_sum *sum)
{
        return ALIGN(BILBYFS_SUM_SZ + le32_to_cpu(sum->nb_sum_entry) * BILBYFS_SUM_ENTRY_SZ + BILBYFS_OBJ_SUM_OFFS_SZ, BILBYFS_OBJ_PADDING);
}

/* struct bilbyfs_info:
 * @vfs_sb: VFS superblock structure
 * @ubi: UBI volume descriptor
 * @di: UBI device information
 * @vi: UBI volume information
 * @next_inum: next inode number to use
 * @next_sqnum: next sequence number to use
 * @is_ro: Is the FS in read-only mode?
 * @wbuf: write-buffer for writing objects in a transaction
 * @rbuf: read-buffer to store an entire leb
 * @super: super block structure
 * @super_offs: superblock on-flash address
 * @dirty_list: a list containing how much garbage each erase-block has
 * @used_leb_list: a list indicating whether an erase-block is used
 * @fsm_lnum: lnum of currently active LEB
 * @fsm_offs: offset of next free space in currently active LEB
 * @gc_buf: buffer for garbage collection
 * @no_summary: mount option value
 */
struct bilbyfs_info {
        struct wrapper_data wd;
        /* VFS specific */
        struct super_block *vfs_sb;
        /* UBI */
        struct ubi_volume_desc *ubi;
        struct ubi_device_info di;
        struct ubi_volume_info vi;
        /* BilbyFs */
        /* FsOp */
        u32 next_inum;
        u64 next_sqnum;
        u32 is_ro;
        struct bilbyfs_dirent dirent;
        struct obj_data *odata;
        /* Index */
        struct rbt_root *idx_hash;
        /* Wbuf */
        struct bilbyfs_wbuf wbuf;
        struct bilbyfs_rbuf rbuf;
        /* Ostore */
        struct bilbyfs_super super;
        struct bilbyfs_wbuf sup_wbuf;
        int super_offs;
        struct alloc_pool node_pool;
        struct obj_sum *summary;
        struct obj_addr *addrs;
        u32 is_mounting;

        /* FSM */
        u32 *dirty_list;
        u8 *used_leb_list;
        u32 fsm_lnum;
        u32 fsm_nb_free_eb;
        /* GIM */
        struct rbt_root *gim_hash;
        /* GC */
        struct bilbyfs_rbuf gc_buf;
        /* Mount */
        int no_summary;
        int nb_pages;
        int nb_extra_pages;
        int gim_allocated_for_nothing;
};

/**
 * next_sqnum: obtain a unique sequence number.
 * @bi: global fs info
 * This function returns an unique sequence number and
 * should be the only function accessing @bi->next_sqnum.
 */
static inline u64 next_sqnum(struct bilbyfs_info *bi)
{
        bi->next_sqnum++;
        return bi->next_sqnum;
}

/**
 * next_inum: obtain a unused inode number.
 * @bi: global fs info
 * This function returns an unused inode number and
 * should be the only function accessing @bi->next_inum.
 */
static inline u32 next_inum(struct bilbyfs_info *bi)
{
        bi->next_inum++;
        return bi->next_inum;
}

/**
 * inode_current_time - round current time to time granularity.
 * @inode: inode
 */
struct timespec64 inode_current_time(struct inode *inode);

/* ReadDir ConteXt: This component helps to list a inline diretory by sequentially
 * reading all directory entries in a directory. 
 *
 * fsop_readdir_ctx: current position of the directory listing.
 * @dentarr: current dentarr evaluated.
 * @de: current diretory entry in the dentarr
 * @id: id of the current dentarr;
 */
struct fsop_readdir_ctx {
        struct  obj_dentarr *dentarr;
        struct  obj_dentry *de;
        obj_id id;
};

/* rdx_init: initialise a readdir context 
 * @bi: global fs info
 * @rdx: context holder
 * @ino: inode number of the directory to list
 */
void rdx_init(struct bilbyfs_info *bi, struct fsop_readdir_ctx *rdx, ino_t ino);

/* rdx_clean: clean a readdir context by freeing the potentially allocated
 * dentarr.
 * @bi: global fs info
 * @rdx: context holder
 */
void rdx_clean(struct fsop_readdir_ctx *rdx);

/* rdx_next_dentry: obtain the next directory entry given a context.
 * dentarr.
 * @bi: global fs info
 * @rdx: context holder
 */
struct obj_dentry *rdx_next_dentry(struct bilbyfs_info *bi, struct fsop_readdir_ctx *rdx);

/* File System Operations (fsop) component:
 * This component implements all the logic of the file system.
 * It only manipulates objects using their ID, every filesystem operation is
 * implemented as a list of objects modifications.
 *
 * See fsop.c.
 */

/* fsop_iget: Read an inode from the disk.
 * @bi: global fs info
 * @inum: inode number to read
 * @inode: inode pointer to store the result to
 *
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_iget(struct bilbyfs_info *bi, unsigned long inum, struct inode *inode);

/* fsop_lookup: Inspect a directory to find a name
 * @bi: global fs info
 * @dir: inode of the directory to inspect
 * @name: name of the file/directory to find
 * @ino: pointer where to store the inode number
 *
 * fsop_lookup will look for the name specified by @dentry->d_name and store
 * the inode number in the parameter @ino.
 * The function returns a negative error code if unsuccessful and zero
 * otherwise
 */
int fsop_lookup(struct bilbyfs_info *bi, struct inode *dir, const char *name, ino_t *ino);

/* fsop_link: Create a hardlink
 * @bi: global fs info
 * @inode: target inode
 * @dir: source inode from which we want to add a directory entry
 * @name: name of the link to create
 *
 * Add a link (directory entry) from @dir to @inode. The function
 * has to deal with the nlink counters of inodes. The function returns a
 * negative error code if unsuccessful and zero otherwise.
 */
int fsop_link(struct bilbyfs_info *bi, struct inode *inode, struct inode *dir, const char *name);

/* fsop_create: Create a file in a directory
 * @bi: global fs info
 * @dir: directory inode in which the file is created
 * @name: name of the file to create
 * @mode: permission, inode type...
 * @excl: NFS specific exclusion flag? FIXME
 * @inode: inode to fill
 *
 * If the function is successful it creates a file on disk in @dir and fill in
 * information about the file in @inode.
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_create(struct bilbyfs_info *bi, struct inode *dir, const char *name,
                umode_t mode, int excl, struct inode *inode);

/* fsop_unlink: Remove a hardlink from a file inode
 * @bi: global fs info
 * @dir: directory inode from which we remove a directory entry
 * @name: name of the file to unlink
 * @inode: inode to which @dentry points
 *
 * The function removes @dentry and decrements the nlink counter of the inode
 * pointed by @dentry. If the counter reaches 0, the inode is removed as well
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_unlink(struct bilbyfs_info *bi, struct inode *dir, const char *name, struct inode *inode);

/* fsop_rmdir: Remove an entry from a directory
 * @bi: global fs info
 * @dir: directory inode from which we remove a directory entry
 * @dentry: directory entry to remove
 * @inode: inode to which @dentry points
 *
 * The function removes @dentry from the directory @dir.
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_rmdir(struct bilbyfs_info *bi, struct inode *dir, const char *name, struct inode *inode);

/* fsop_mkdir: Create a directory
 * @bi: global fs info
 * @dir: directory inode from which we create a directory entry
 * @name: name of the directory to create
 * @mode: permission...
 * @inode: inode to fill
 *
 * The function removes @dentry from the directory @dir.
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_mkdir(struct bilbyfs_info *bi, struct inode *dir, const char *name, umode_t mode, struct inode *inode);

/* fsop_readdir: Read a directory sequentially
 * @bi: global fs info
 * @inode: directory inode
 * @ctx: context for FS use
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_readdir(struct bilbyfs_info *bi, struct inode *inode, struct dir_context *ctx, struct fsop_readdir_ctx **rdx);
void fsop_dir_release(struct fsop_readdir_ctx *rdx);

/* fsop_symlink: Create a symbolic link
 * @bi: global fs info
 * @dir: directory inode in which we create symlink
 * @name: the name of the symlink
 * @symname: path to which the symlink points
 * @inode: inode to fill
 *
 * If the function is successful it creates a symlink inode on disk
 * and fill in information about the symlink in @inode.  The new symlink's 
 * path is put into a data object pointed to by the inode.
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_symlink(struct bilbyfs_info *bi, struct inode *dir, const char *name, const char *symname, struct inode *inode);

/* fsop_rename: Change the name and parent for an inode
 * @bi: global fs info
 * @old_dir: parent directory inode of the source inode
 * @old_name: source inode to be renamed
 * @old_inode: inode to which @old_dentry points
 * @new_dir: parent directory inode for destination inode (can be the same as old_dir)
 * @new_name: new name for the destination inode
 * @new_inode: destination inode, can be null if destination inode is the same as source inode
 *
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_rename(struct bilbyfs_info *bi, struct inode *old_dir, const char *old_name,
                struct inode *old_inode, struct inode *new_dir, const char *new_name,
                struct inode *new_inode);

/* fsop_readpage: Read a page (could be multiple blocks) from a file inode
 * @bi: global fs info
 * @inode: file inode we read a page from
 * @block: block index in the file
 * @addr: address to store read data to
 *
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_readpage(struct bilbyfs_info *bi, struct inode *inode, pgoff_t block, void *addr);

/* fsop_write_begin: Read pages overlapping range of data for a future write
 * @bi: global fs info
 * @inode: file inode we read a page from
 * @pos: position in file from which we want to write
 * @len: number of bytes we want to write
 * @addr: address to store read data to
 *
 * Storage devices only allow to write data by blocks (e.g. 4096 bytes), so
 * this function is meant to read data that is needed to be able to update the
 * file from offset @pos to @pos + @len.
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_write_begin(struct bilbyfs_info *bi, struct inode *inode, int pos, int len, void *addr);

/* fsop_write_end: Write file data to disk
 * @bi: global fs info
 * @inode: file inode we read a page from
 * @pos: position in file from which we want to write
 * @len: number of bytes we want to write
 * @addr: address to store read data to
 *
 * This function writes back the actual @file's data stored in @addr to disk.
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_write_end(struct bilbyfs_info *bi, struct inode *inode, int pos, int len, void *addr);

/* fsop_follow_link: Read a symbolic link inode
 * @bi: global fs info
 * @inode: inode in which the path is stored
 * @path: pointer where to store the path read
 *
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_follow_link(struct bilbyfs_info *bi, struct inode *inode, char *path);

/* fsop_setattr: Set attributes of an inode (file/directory/symlink)
 * @bi: global fs info
 * @dentry: inode to modify
 * @attr: attributes to modify and their new value
 *
 * This function also handles truncate, which is just an inode size
 * modification.
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_setattr(struct bilbyfs_info *bi, struct inode *inode, struct iattr *attr);

/* fsop_getattr: Read inode attributes
 * @bi: global fs info
 * @inode: inode to read
 * @stat: stat structure to fill
 *
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_getattr(struct bilbyfs_info *bi, struct inode *inode, struct kstat *stat);

/* fsop_evict_inode: Inode cache eviction
 * @bi: global fs info
 * @inode: inode to evict
 *
 * If the OS caches inodes, fsop_evict_inode will be called when the OS decides
 * to remove the inode from the cache.
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
void fsop_evict_inode(struct bilbyfs_info *bi, struct inode *inode);

/* fsop_evict_inode: Get statistic about the FS
 * @bi: global fs info
 * @kstat: kstat structure to fill
 *
 * This function enables reporting the amount of free space available among
 * other stats.
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_statfs(struct bilbyfs_info *bi, struct kstatfs *kstat);

int fsop_budget_data_update(struct bilbyfs_info *bi);
void fsop_budget_cancel_data_update(struct bilbyfs_info *bi);

/* fsop_sync_fs: Synchronise the FS to disk
 * @bi: global fs info
 * @sb: superblock data structure
 * @wait: flag indicated whether the function is allowed to wait
 *
 * The function returns a negative error code if unsuccessful and zero
 * otherwise.
 */
int fsop_sync_fs(struct bilbyfs_info *bi, struct super_block *sb, int wait);

/* fsop_test_is_mount: Check whether the FS is already mounted
 * @bi1: global fs info
 * @bi2: global fs info
 *
 * The function returns 0 if the FS is not already mounted, 1 otherwise.
 */
int fsop_test_is_mount(struct bilbyfs_info *bi1, struct bilbyfs_info *bi2);

/* fsop_fill_super: Read the super block and fills the structure
 * @bi: global fs info
 * @sb: super block to fill
 * @silent: flag indicated whether the FS should print error messages or not
 * @rootino: pointer to an inode number
 *
 * The function must read the super block and find the root inode number.
 * If successful the function set the root inode number in @rootino and 
 * returns 0. A negative error code is returned in case of failure.
 */
int fsop_fill_super(struct bilbyfs_info *bi, struct super_block *sb, int silent, ino_t *rootino, struct inode *root);

/* fsop_init: Initialise the FS
 * @bi: global fs info
 * @name: mount command line device name
 * @bd_name: backing device name to be filled
 *
 * The function allocates vital FS data structures and open the storage
 * device. The @bd_name must be filled with the backing device name.
 * The function returns a negative error code in case of failure, 0 otherwise.
 */
int fsop_init(struct bilbyfs_info *bi, const char *name, char *bd_name);

/* fsop_umount: unmount the fs
 * @bi: global fs info
 *
 * this function must deallocate most data structures allocated in init.
 */
void fsop_unmount(struct bilbyfs_info *bi);

/* fsop_clean: Free the remaining data structures left allocated by unmount
 * @bi: global fs info
 */
void fsop_clean(struct bilbyfs_info *bi);

/* Linux Helpers */
struct ubi_volume_desc *open_ubi(const char *name, int mode);

/*
 * Object Store () component:
 * Reading/Writing objects from their id, writing is transactional using the
 * `trans' propertry stored in objects' header.
 */

/* ostore_init: Initialise Ostore component
 * @bi: global fs info
 *
 */
int ostore_init(struct bilbyfs_info *bi);

/* ostore_clean: Clean up Ostore component
 * @bi: global fs info
 *
 */
void ostore_clean(struct bilbyfs_info *bi);

/* ostore_get_obj_size: request the size of an object
 * @bi: global fs info
 * @id: id of the object
 *
 * This function returns the size of an object or a negative error code.
 */
int ostore_get_obj_size(struct bilbyfs_info *bi, obj_id id);

/* ostore_read_obj: read an obj using its id
 * @bi: global fs info
 * @id: id of the object
 * @buf: buffer to store data in
 * @len: size of the buffer
 *
 * It is possible to read an object before, after and while a transaction.
 * ostore_read_obj will only return an object written once the transaction
 * has been commited.
 * Return non-zero value if it fails.
 */
int ostore_read_obj(struct bilbyfs_info *bi, obj_id id, void *buf, u32 len);

enum { OSW_NONE = 0,
       OSW_DEL = 1,
       OSW_GC = 2,
       OSW_SYNC = 4,
};

/* ostore_write_obj_list: write objects in the list to disk
 * @bi: global fs info
 * @obj_list: an array of objects to write, the header must be complete and
 * the object cannot be modified as its CRC has been calculated.
 * @count: number of objects in the list
 * @write_flag: OSW_NONE, OSW_DEL (Deletion), OSW_GC (Garbage Collection)
 *
 * This function will writes all the objects in the list into the disk
 * in one single transaction.
 * 
 * Note that this function will set the object command header
 * according to their position in the transaction
 *
 * A successful execution is indicated by a return value of 0.
 * A failure is indicated by a negative error-code.
 *
 */
int ostore_write_obj_list(struct bilbyfs_info *bi, void **obj_list, int count, int write_flag);
int ostore_sync(struct bilbyfs_info *bi, int force_summary);

/* ostore_erase: Erase an erase-block
 * @bi: global fs info
 * @lnum: LEB number of the erase-block
 */
int ostore_erase(struct bilbyfs_info *bi, int lnum);

/* ostore_scan_obj: Scan an erase-block and build a list of objects in the block
 * @bi: global fs info
 * @rbuf: buffer used to store the objects
 * @lnum: LEB number of the erase-block
 * @list: list to store object addresses in the buffer
 * @max_count: maximum number of objects the list can store
 *
 * This function return the number of object in the erase block
 * It also return a negative error code if unsuccessful
 */
int ostore_scan_obj(struct bilbyfs_info *bi, struct bilbyfs_rbuf *rbuf, int lnum,
                void **list, int max_count);
int ostore_scan_leb_obj(struct bilbyfs_info *bi, struct bilbyfs_rbuf *rbuf, int lnum,
                        void **list, int max_count);

/* ostore_next_obj_id: return the next id from an id
 * @bi: global fs info
 * @id: id of the object
 *
 * This function just calls tix_next_obj_id, see def for doc.
 */
obj_id ostore_next_obj_id(struct bilbyfs_info *bi, obj_id id);

/* ostore_mount: scan the media and initialises underlying components
 * @bi: global fs info
 *
 * This function initialises fsm and tindex components by scanning
 * and reading all objects present on the media.
 */
int ostore_mount(struct bilbyfs_info *bi);

/* ostore_unmount: free all memory allocated by trans.
 * @bi: global fs info
 *
 * This function frees all the memory allocated by trans.
 */
void ostore_unmount(struct bilbyfs_info *bi);

/* ostore_get_free_space: returns how much free space available on the media
 * @bi: global fs info
 */
unsigned long long ostore_get_free_space(struct bilbyfs_info *bi);
unsigned long long ostore_get_available_space(struct bilbyfs_info *bi);

/* ostore_write_super: update the superblock on-flash
 * @bi: global fs info
 *
 * This function is used by mount() to store the initial super-block.
 * The function ostore_unmount() also implicitly call it.
 * The function returns a negative error-code in case of failure.
 */
int ostore_write_super(struct bilbyfs_info *bi);

/*
 * Write Buffer component:
 * Reading/Writing objects in a buffer that is then flushed by wbuf_commit().
 */

/* wbuf_init: initialise wbuf component
 * @bi: global fs info
 */
int wbuf_init(struct bilbyfs_info *bi);

/* wbuf_clean: clean-up wbuf component
 * @bi: global fs info
 */
void wbuf_clean(struct bilbyfs_info *bi);

/* wbuf_start: initialise bi->wbuf for a transaction
 * @bi: global fs info
 */
void wbuf_start(struct bilbyfs_info *bi, struct bilbyfs_wbuf *wbuf);

/* wbuf_read_obj: read an obj from wbuf if in cache or from UBI otherwise.
 * @bi: global fs info
 * @buf: buffer to store data in
 * @addr: object's address
 *
 */
int wbuf_read_obj(struct bilbyfs_info *bi, void *buf, struct obj_addr *addr);

/* wbuf_write_obj: write an object in a group
 * @bi: global fs info
 * @buf: buffer where to get data to write.
 * @wbuf: write-buffer to use
 * This function returns 0 if the object has been added to the transaction.
 */
int wbuf_write_obj(struct bilbyfs_info *bi, void *buf, int len, struct bilbyfs_wbuf *wbuf);

/* wbuf_prepare_commit: prepare (padding) the wbuf for a commit
 * @bi: global fs info
 * @paading_sz: when function return, amount of padding will be stored
 *              if set to NULL, no value will be stored
 * @wbuf: write-buffer to use
 *
 * This function never fails, it always returns the size of the transaction
 * including padding in bytes.
 */
int wbuf_prepare_commit(struct bilbyfs_info *bi, u32 *padding_sz, struct bilbyfs_wbuf *wbuf);


/* wbuf_commit: commit the buffer on-flash
 * @bi: global fs info
 * @lnum: LEB to write to
 * @wbuf: write-buffer to use
 *
 * The function either succeed or fail, if the returned value is greater than
 * 0, it means that the entire transaction has been successfully flushed
 * on-flash and the return value is the number of bytes written to the LEB.
 * In case of failure the function returns a negative error-code.
 *
 */
int wbuf_commit(struct bilbyfs_info *bi, u32 lnum, struct bilbyfs_wbuf *wbuf);

/* wbuf_atom_leb_commit: update an LEB on flash atomically
 * @bi: global fs info
 * @lnum: LEB to update
 * @wbuf: write-buffer to use
 *
 * This function overwrites @leb regardless of the current status of LEB,
 * it enssentially unmap the leb and map to an empty one to write the data.
 * This operation is quite slow and should only be used when strictly
 * necessary.
 *
 * In case of failure the function returns a negative error-code.
 *
 */
int wbuf_atom_leb_commit(struct bilbyfs_info *bi, int lnum, struct bilbyfs_wbuf *wbuf);

/* wbuf_read_leb: Reads an entire LEB in memory
 * @bi: global fs info
 * @lnum: LEB number to read
 * @rbuf: read-buffer where to store the data read
 *
 * This function returns a negative error-code if unsuccessful.
 */
int wbuf_read_leb(struct bilbyfs_info *bi, int lnum, struct bilbyfs_rbuf *rbuf);
int wbuf_read_leb_fast(struct bilbyfs_info *bi, int lnum, struct bilbyfs_rbuf *rbuf);

/* wbuf_read_sum: Reads pages covering the summary object and returns offset in
 * @sum_offs_ret
 * @bi: global fs info
 * @lnum: LEB number to read
 * @rbuf: read-buffer where to store the data read
 * @sum_offs_ret: pointer used to store the offset of the summary object.
 *
 * This function returns a negative error-code if unsuccessful.
 */
int wbuf_read_sum(struct bilbyfs_info *bi, int lnum, struct bilbyfs_rbuf *rbuf, u32 *sum_offs_ret);

/* wbuf_erase: Erase an earse-block
 * @bi: global fs info
 * @lnum: LEB number of the erase-block
 */
int wbuf_erase(struct bilbyfs_info *bi, int lnum);

/* wbuf_next_obj_addr: Find the next object in a read-buffer
 * @bi: global fs info
 * @addr: address to start from
 * @rbuf: read-buffer to analyse
 *
 * Read the next object present in a LEB starting from
 * addr->offs + addr->len in LEB addr->lnum.
 *
 * If there isn't any object present in the LEB the function
 * returns %-ENOENT. In this case addr is unchanged.
 *
 * If addr->len = 0, as the function cannot find the next object,
 * it will return the object at addr->offs if one exists.
 *
 * This function is needed to implement the mount operation and the
 * transaction commit operation.
 * We use it to perform the initial media scanning to populate the
 * components fsm and index.
 * We also use it to update the index & fsm components when the
 * transaction in progress has been committed on-flash.
 *
 * This function returns a pointer to the next object if successful and
 * writes the address of the next object stored on the media in @addr.
 * If unsuccessful it returns %-ENOENT as mentionned above.
 */
void *wbuf_next_obj_addr(struct bilbyfs_info *bi, struct obj_addr *addr,
                         struct bilbyfs_rbuf *rbuf);

/*
 * Object pool component: Preallocates tree nodes to protect against
 * memory allocation errors in critical section of the FS where not
 * updating an in-memory data structure would lead to an inconsistency
 * between the in-mem state and on-disk state.
 */
int allocpool_init(struct alloc_pool *pool);
void allocpool_destroy(struct alloc_pool *pool);
int allocpool_alloc(struct alloc_pool *pool, int sz_pool, int sz_obj);
void allocpool_empty(struct alloc_pool *pool);
void *allocpool_pop(struct alloc_pool *pool);
void allocpool_free_single(void *p);

/*
 * Free Space Management (fsm) component:
 * Find logical erase-blocks with enough free space for wbuf's purpose.
 */

/* fsm_init: initialise the fsm component
 * @bi: global fs info
 */
int fsm_init(struct bilbyfs_info *bi);


/* fsm_clean: clean-up the fsm component
 * @bi: global fs info
 */
void fsm_clean(struct bilbyfs_info *bi);

/* fsm_alloc_eb: find a leb with @req_size free space to write objects.
 * @bi: global fs info
 * @osw_flag: Flags helping choosing erase-blocks to allocate
 *
 * This function returns a leb number >0 if successful or a negative error code.
 */
int fsm_alloc_eb(struct bilbyfs_info *bi, int osw_flag);

/* fsm_get_lnum: return current leb allocated
 * @bi: global fs info
 */
u32 fsm_get_lnum(struct bilbyfs_info *bi);

/* fsm_mark_dirty: mark the address of an object as dirty space for garbage
 * collection.
 * @bi: global fs info
 * @addr: address of the dirty object
 *
 */
void fsm_mark_dirty(struct bilbyfs_info *bi, struct obj_addr *addr);

/* fsm_mark_used: mark a leb as used
 * @bi: global fs info
 * @lnum: which LEB
 */
void fsm_mark_used(struct bilbyfs_info *bi, int lnum);

/* fsm_mark_erased: Mark the erase-block as empty
 * @bi: global fs info
 * @lnum: LEB number of the erase-block that has been erased
 */
void fsm_mark_erased(struct bilbyfs_info *bi, int lnum);

/* fsm_get_free_space: returns how much free space available on the media
 * @bi: global fs info
 */
unsigned long long fsm_get_free_space(struct bilbyfs_info *bi);
unsigned long long fsm_get_available_space(struct bilbyfs_info *bi);

/* fsm_get_dirtiest_eb: get erase-block with most garbage
 * @bi: global fs info
 *
 * This function return erase-block logical number if the dirtiest
 * erase-block is found.
 * It returns -1 if no block is found
 */
int fsm_get_dirtiest_eb(struct bilbyfs_info *bi);
/* Red-Black tree component
 */


#define rbt_parent(r)   ((struct rbt_node *)((r)->rbt_parent_color & ~3))
#define rbt_color(r)   ((r)->rbt_parent_color & 1)
#define rbt_is_red(r)   (!rbt_color(r))
#define rbt_is_black(r) rbt_color(r)
#define rbt_set_red(r)  do { (r)->rbt_parent_color &= ~1; } while (0)
#define rbt_set_black(r)  do { (r)->rbt_parent_color |= 1; } while (0)

static inline void rbt_set_parent(struct rbt_node *rb, struct rbt_node *p)
{
	rb->rbt_parent_color = (rb->rbt_parent_color & 3) | (unsigned long)p;
}
static inline void rbt_set_color(struct rbt_node *rb, int color)
{
	rb->rbt_parent_color = (rb->rbt_parent_color & ~1) | color;
}

#define RBT_ROOT	(struct rbt_root) { NULL, }
#define	rbt_entry(ptr, type, member) container_of(ptr, type, member)

#define RBT_EMPTY_ROOT(root)	((root)->rbt_node == NULL)
#define RBT_EMPTY_NODE(node)	(rbt_parent(node) == node)
#define RBT_CLEAR_NODE(node)	(rbt_set_parent(node, node))

void rbt_insert_color(struct rbt_node *, struct rbt_root *);
struct rbt_node *rbt_first(const struct rbt_root *root);
void rbt_erase(struct rbt_node *, struct rbt_root *);
void rbt_link_node(struct rbt_node * node, struct rbt_node * parent,
                   struct rbt_node ** rbt_link);

/*
 * Index functions:
 * The index caches the address of an object to avoid scanning the entire
 * disk to find the object.
 */

/* idx_init: Initialise Index component
 * @bi: global fs info
 *
 */
int idx_init(struct bilbyfs_info *bi);

/* idx_clean: Clean up Index component
 * @bi: global fs info
 *
 */
void idx_clean(struct bilbyfs_info *bi);

/* idx_get_obj_addr: retrieve the address of an object from the index.
 * @bi: global fs info
 * @id: id of the object
 * @addr: obj_addr struct to store the object's address in.
 *
 * This function returns 0 if the object was found in the index and addr is set.
 * A negative error code is return otherwise, including -ENOENT if the object
 * wasn't found.
 */
int idx_get_obj_addr(struct bilbyfs_info *bi, obj_id id, struct obj_addr *addr);
struct idx_node *idx_get_or_create_obj_addr_node(struct bilbyfs_info *bi, obj_id id);

/* idx_set_obj_addr: sets the address of an object designated by @id
 * @id: id of the object
 * @addr: address to store for the id
 * @node: preallocated node that is freed by the function if unused.
 *
 * This function always returns 0.
 */
int idx_set_obj_addr(struct bilbyfs_info *bi, obj_id id, struct obj_addr *addr, struct idx_node *node);

/* idx_next_obj_id: returns the next id stored in the index.
 * An id can be interpreted as a u64 and therefore each object is ordered
 * using this interpretation.
 * If there is no id greater than @id stored in the index, the function
 * returns ~0
 * @bi: global fs info
 * @id: id of the object
 */
obj_id idx_next_obj_id(struct bilbyfs_info *bi, obj_id id);

/* idx_del_obj_addr: delete an object address from the index.
 * @bi: global fs info
 * @id: id of the object
 *
 * The function returns the removed node.
 * The function cannot be called if the node doesn't exists, doing so
 * will break an assertion check.
 */
void *idx_del_obj_addr(struct bilbyfs_info *bi, obj_id id);


/*
 * DentArr component: Ideally we would store directory entry directly in the
 * index and retrieve entries as we need. In practice, object IDs are limited
 * in size (64 bits) and we cannot store the entire name attached to an
 * directory entry in the object ID. Accessing a directory entry by name is
 * required for the ->lookup() operation to be efficient.
 * Therefore we only store a hash of the name in object IDs and we deal with
 * collisions by storing arrays of directory entry (dentarr) in the index.
 */
/* dentarr_add_dentry: adds a directory entry in a dentarr
 * @bi: global fs info
 * @dentarr: dentarr where to add the directory entry
 * @inode: inode to initialise the dentry with
 * @name: name to initialise the dentry with
 *
 * The function can return -ENAMETOOLONG if the maximum number of collision for
 * a name in a directory has been reached.
 * Otherwise the function returns the size in bytes of the directory entry
 * freshly added.
 */
int dentarr_add_dentry(struct bilbyfs_info *bi, struct obj_dentarr *dentarr,
                       struct inode *inode, const char *name);

/* dentarr_del_dentry: deletes a directory entry from a dentarr
 * @bi: global fs info
 * @dentarr: dentarr where to add the directory entry
 * @name: name to delete
 *
 * This function can return -ENOMEM as error, when successul it returns
 * the number of bytes removed from the dentarr.
 * If the name was not found in the dentarr, the function returns 0.
 */
int dentarr_del_dentry(struct bilbyfs_info *bi, struct obj_dentarr *dentarr,
                       const char *name);

/* dentarr_check_empty: checks whether a dentarr is empty
 * @bi: global fs info
 * @dentarr: dentarr to examine
 *
 * This function return -ENOTEMPTY if the dentarr is not empty otherwise 0 is
 * returned.
 */
int dentarr_check_empty(struct bilbyfs_info *bi, struct obj_dentarr *dentarr);

/* dentarr_lookup_nm: lookup a name in a `directory entry array'
 * @bi: global fs info
 * @darr: directory entry array object
 * @name: name to lookup
 *
 * The function returns a pointer to the obj_dentry if the entry was found,
 * %-ENOENT if the name was not found and a negative error code otherwise.
 */
struct obj_dentry *dentarr_lookup_nm(struct bilbyfs_info *bi,
                                     struct obj_dentarr *dentarr,
                                     const char *name);
struct obj_dentry *dentarr_first_dentry(struct obj_dentarr *dentarr);
struct obj_dentry *dentarr_next_dentry(struct obj_dentarr *dentarr,
                                       struct obj_dentry *dentry);
/* dentarr_read: allocate and read a dentarr
 * @bi: global fs info
 * @id: id of the object to read
 *
 * This function returns a negative error code if the object
 * does not exist.
 */
struct obj_dentarr *dentarr_read(struct bilbyfs_info *bi, obj_id id);

/* dentarr_read_or_create: read a dentarr or create one if it doesn't exist.
 * @bi: global fs info
 * @id: id of the object to read
 *
 * If the function creates a new dentarr, it allocates the memory space for
 * a dentry.
 * This function returns a negative error code if an error happens.
 */
struct obj_dentarr *dentarr_read_or_create(struct bilbyfs_info *bi, obj_id id);

/* PackObj component:
 *
 * stateless component that prepares objects to be written on the med$a.
 */
/**
 * pack_obj_header - prepare object header to be written to flash.
 * @obj: object pointer
 * @sqnum: sequence number to store in the object.
 * @trans_pos: position in transaction (%BILBYFS_TRANS_ST, ...)
 *
 * This function prepares an object headeer - it calculates the CRC and
 * fills the common header.
 */
void pack_obj_header(void *obj, u64 sqnum, u8 trans_pos);

/**
 * check_obj_header - check whether the pointer passed is an object header
 * @buf: object pointer
 * @max_obj_sz: maximum possible valid size of this object.
 *
 * The maximum possible object size must be calculated from the object offset
 * in a LEB (an object cannot spread over multiple LEBs).
 * It returns 0 if the pointer points to an object.
 */
int check_obj_header(void *obj, int max_obj_sz);

/**
 * pack_obj_inode - pack an inode object.
 * @ino: obj where to store the inode
 * @inode: inode to pack
 */
void pack_obj_inode(struct obj_inode *ino, struct inode *inode);

/**
 * pack_obj_dentarr - pack a dentarr object.
 * @dentarr: obj dentarr to pack
 * @id: id of the object to pack
 * @nbdentry: number of dentry embedded in the dentarr
 * @size: size in bytes of the dentarr object
 */
void pack_obj_dentarr(struct obj_dentarr *dentarr, obj_id id,
                      int nbdentry, int size);

/**
 * pack_obj_data - pack a data object.
 * @odata: obj data to pack
 * @id: id of the object to pack
 * @sz_data: size of the data to store in the obj_data
 * @data: pointer to the data to store in the obj_data
 */
void pack_obj_data(struct obj_data *odata, obj_id id, int sz_data,
                   const void *data);

/**
 * pack_obj_dentry - pack a dentry object.
 * @de: obj dentry to pack
 * @inode: inode the dentry is linked with
 * @name: name to store in the dentry
 */
void pack_obj_dentry(struct obj_dentry *de, struct inode *inode, const char *name);

/**
 * pack_obj_pad - pad a padding object.
 * @pad: padding object to pack
 * @pad_sz: padding size;
 */
void pack_obj_pad(struct obj_ch *pad, int pad_sz);

/**
 * unpack_obj_inode - unpack an inode object.
 * @inode: inode where to store the object inode
 * @ino: obj inode to unpack
 */
void unpack_obj_inode(struct inode *inode, struct obj_inode *ino);

/**
 * pack_obj_super - pack a super object.
 * @super: obj super to unpack
 * @bsuper: super object memory representation
 */
void pack_obj_super(struct obj_super *super, const struct bilbyfs_super *bsuper);

/**
 * unpack_obj_super - unpack a super object.
 * @bsuper: super in memory representation where to store the obj_super
 * @super: obj super to unpack
 */
void unpack_obj_super(struct bilbyfs_super *bsuper, struct obj_super *super);

/**
 * pack_obj_del - pack a deletion object
 * @obj: potentially a deletion object, but other objects can be casted to
 * deletion object as well
 * @id: object id of the object to be deleted
 */
void pack_obj_del(void *obj, obj_id id);

/**
 * pack_obj_sum - pack a summary object
 * @sum: summary object to pack
 * @offs: erase-block offset to at which the summary object itself lives.
 */
void pack_obj_sum(struct obj_sum *sum, u32 offs);

/**
 * GIM - garbage information manager
 * GIM manages the all information about garbage on disk.
 * It maintains dirty list which specify how much garbage each erase block has.
 * It also keep a garbage object list
 */
/* gim_init: Initialise GIM component
 * @bi: global fs info
 */
int gim_init(struct bilbyfs_info *bi);

/* gim_clean: clean up GIM component
 * @bi: global fs info
 */
void gim_clean(struct bilbyfs_info *bi);

/* gim_mark_garbage: mark an object as garbage
 * @bi: global fs info
 * @id: object id
 * @addr: object address containing sequence number
 * @node: preallocated node that is freed by the function if not used.
 *
 * This function return negative error code upon failure
 */
int gim_mark_garbage(struct bilbyfs_info *bi, obj_id id, struct obj_addr *addr, struct gim_node *node);
int gim_mark_garbage_cnt(struct bilbyfs_info *bi, obj_id id, struct obj_addr *addr, u32 count, struct gim_node *allocated_node);


/* gim_is_removable: determine if an object can be garbage collected
 * @bi: global fs info
 * @obj: object to be tested
 *
 * This function return a boolean indicate whether the garbage can be removed
 * from disk or not
 */
int gim_is_removable(struct bilbyfs_info *bi, struct obj_ch *obj);

/* gim_garbage_collected: mark as object has been garbage collected
 * @bi: global fs info
 * @obj: object that have been garbage collected
 *
 * This function return negative error code upon failure
 */
int gim_garbage_collected(struct bilbyfs_info *bi, struct obj_ch *obj);

/**
 * Garbage Collector
 */
/* gc_init: Initialise the garbage collector
 * @bi: global fs info
 *
 * The function returns a negative error code in case of failure, 0 otherwise
 */
int gc_init(struct bilbyfs_info *bi);

/* gc_clean: Clean up GC component
 * @bi: global fs info
 */
void gc_clean(struct bilbyfs_info *bi);

/* gc_garbage_collect: Perform garbage collection
 * @bi: global fs info
 */
int gc_garbage_collect(struct bilbyfs_info *bi);


/* Debug functions */
void dump_sum_entry( struct obj_sum_entry *entry);
void dump_obj_addr( struct obj_addr *addr);

#endif /* !__BILBYFS_H__ */
