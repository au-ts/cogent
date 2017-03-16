/*
 * Copyright 2017, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */


#ifndef FAT_HEAD_WRAP
#define FAT_HEAD_WRAP

// Fix up EXPORT_SYMBOL_GPL stuff

// static removed from these
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

#endif
