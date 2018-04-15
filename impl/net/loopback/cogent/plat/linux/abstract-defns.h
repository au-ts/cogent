/*
 * Copyright 2018, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

/*
 * abstract-defns.h
 * This file contains the abstract data type definitions that all linux kernel
 * network modules will need.
 */

#ifndef ABSTRACT_DEFNS_H_
#define ABSTRACT_DEFNS_H_

typedef int Int;
typedef unsigned int UInt;
typedef u8 * U8Ptr;

typedef __le16 LE16;
typedef __le32 LE32;
typedef __le64 LE64;
typedef __be16 BE16;
typedef __be32 BE32;
typedef __be64 BE64;

#endif  /* ABSTRACT_DEFNS_H_ */
