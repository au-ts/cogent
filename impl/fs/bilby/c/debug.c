/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include "bilbyfs.h"

void dump_sum_entry( struct obj_sum_entry *entry)
{
        bilbyfs_err("{id=0x%llx,sqnum=%llu,len=%u,is_del=%d,offs=%u,count=%u}\n",
                    le64_to_cpu(entry->id), le64_to_cpu(entry->sqnum), le32_to_cpu(entry->len),
obj_sum_entry_is_del(entry), obj_sum_entry_offs(entry), le16_to_cpu(entry->count));
}

void dump_obj_addr( struct obj_addr *addr)
{
        bilbyfs_err("{lnum=%u,offs=%u,len=%u,sqnum=%llu}\n", addr->lnum, addr->offs, addr->len, addr->sqnum);
}

