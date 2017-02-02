
#ifndef WRAPPER_HEAD
#define WRAPPER_HEAD

/*================
	IMPORTANT NOTE
	EXPORT_SYMBOL_GPL STUFF!! DIFFERENT! Important
	FIX U P in the end
*=================*/

// static removed - is this an issue?
extern int vfat_add_entry(struct inode *dir, struct qstr *qname, int is_dir,
			  int cluster, struct timespec *ts,
			  struct fat_slot_info *sinfo);

extern int fat_fill_inode(struct inode *inode, struct msdos_dir_entry *de);

extern struct inode *fat_iget(struct super_block *sb, loff_t i_pos);

extern unsigned int vfat_striptail_len(const struct qstr *qstr); // TODO: skip the middle man and go to __vfat_striptail_len directly

extern int vfat_build_slots(struct inode *dir, const unsigned char *name,
			    int len, int is_dir, int cluster,
			    struct timespec *ts,
			    struct msdos_dir_slot *slots, int *nr_slots);

extern int vfat_find(struct inode *dir, struct qstr *qname,
		     struct fat_slot_info *sinfo);

extern int vfat_d_anon_disconn(struct dentry *dentry);

extern unsigned long fat_hash(loff_t i_pos);

extern int __fat_remove_entries(struct inode *dir, loff_t pos, int nr_slots);
void fat_msg(struct super_block *sb, const char *level, const char *fmt, ...);
extern int __fat_write_inode(struct inode *inode, int wait);

extern int fat_get_entry(struct inode *dir, loff_t *pos,
				struct buffer_head **bh,
				struct msdos_dir_entry **de);

extern void fat_dir_readahead(struct inode *dir, sector_t iblock,
				     sector_t phys);

extern int fat_bmap(struct inode *inode, sector_t sector, sector_t *phys,
	     unsigned long *mapped_blocks, int create);

// not used for now
/*
struct i_remaining {
	umode_t			i_mode;
	unsigned short		i_opflags;
	kuid_t			i_uid;
	kgid_t			i_gid;
	unsigned int		i_flags;

#ifdef CONFIG_FS_POSIX_ACL // how to check which are defined
	struct posix_acl	*i_acl;
	struct posix_acl	*i_default_acl;
#endif

	const struct inode_operations	*i_op;
	struct address_space	*i_mapping;

#ifdef CONFIG_SECURITY
	void			*i_security;
#endif
	unsigned long		i_ino;
	union {
		const unsigned int i_nlink;
		unsigned int __i_nlink;
	};
	dev_t			i_rdev;
	loff_t			i_size;
	struct timespec		i_atime;
	struct timespec		i_mtime;
	struct timespec		i_ctime;
	//spinlock_t		i_lock;
	spinlock_t	*	i_lock;
	unsigned short          i_bytes;
	unsigned int		i_blkbits;
	blkcnt_t		i_blocks;

#ifdef __NEED_I_SIZE_ORDERED
	seqcount_t		i_size_seqcount;
#endif


	unsigned long		i_state;
	struct mutex		i_mutex;

	unsigned long		dirtied_when;
	unsigned long		dirtied_time_when;

	struct hlist_node	i_hash;
	struct list_head	i_io_list;
#ifdef CONFIG_CGROUP_WRITEBACK
	struct bdi_writeback	*i_wb;

	int			i_wb_frn_winner;
	u16			i_wb_frn_avg_time;
	u16			i_wb_frn_history;
#endif
	struct list_head	i_lru;
	struct list_head	i_sb_list;
	union {
		struct hlist_head	i_dentry;
		struct rcu_head		i_rcu;
	};
	//MOVED: u64			i_version;
	atomic_t		i_count;
	atomic_t		i_dio_count;
	atomic_t		i_writecount;
#ifdef CONFIG_IMA
	atomic_t		i_readcount;
#endif
	const struct file_operations	*i_fop;
	struct file_lock_context	*i_flctx;
	//struct address_space	i_data;
	struct address_space * i_data;
	struct list_head	i_devices;
	union {
		struct pipe_inode_info	*i_pipe;
		struct block_device	*i_bdev;
		struct cdev		*i_cdev;
		char			*i_link;
	};

	__u32			i_generation;

#ifdef CONFIG_FSNOTIFY
	__u32			i_fsnotify_mask;
	struct hlist_head	i_fsnotify_marks;
#endif

	void			*i_private;
};
*/
#endif
