/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef FAKE_STDLIB_H__
#define FAKE_STDLIB_H__

#define printf(...) ((void)0)

typedef unsigned long long size_t;
void *malloc(size_t);
void *calloc(size_t, size_t);
void free(void*);

#define NULL 0

#endif
