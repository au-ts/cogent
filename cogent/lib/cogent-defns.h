/*
 * Copyright 2017, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef __COGENT_DEFNS_H__
#define __COGENT_DEFNS_H__

#define likely(x)       __builtin_expect(!!(x), 1)
#define unlikely(x)     __builtin_expect(!!(x), 0)

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long long u64;

typedef struct unit_t {
    int dummy;
} unit_t;

typedef struct bool_t {
    u8 boolean;
} bool_t;

#define GEN_UINT_8(SIZE) \
typedef struct u##SIZE##_t { \
    u8 uint; \
} u##SIZE##_t;

#define GEN_UINT_16(SIZE) \
typedef struct u##SIZE##_t { \
    u16 uint; \
} u##SIZE##_t;

#define GEN_UINT_32(SIZE) \
typedef struct u##SIZE##_t { \
    u32 uint; \
} u##SIZE##_t;

#define GEN_UINT_64(SIZE) \
typedef struct u##SIZE##_t { \
    u64 uint; \
} u##SIZE##_t;

GEN_UINT_8(1)
GEN_UINT_8(2)
GEN_UINT_8(3)
GEN_UINT_8(4)
GEN_UINT_8(5)
GEN_UINT_8(6)
GEN_UINT_8(7)

GEN_UINT_16(9)
GEN_UINT_16(10)
GEN_UINT_16(11)
GEN_UINT_16(12)
GEN_UINT_16(13)
GEN_UINT_16(14)
GEN_UINT_16(15)

GEN_UINT_32(17)
GEN_UINT_32(18)
GEN_UINT_32(19)
GEN_UINT_32(20)
GEN_UINT_32(21)
GEN_UINT_32(22)
GEN_UINT_32(23)
GEN_UINT_32(24)
GEN_UINT_32(25)
GEN_UINT_32(26)
GEN_UINT_32(27)
GEN_UINT_32(28)
GEN_UINT_32(29)
GEN_UINT_32(30)
GEN_UINT_32(31)

GEN_UINT_64(33)
GEN_UINT_64(34)
GEN_UINT_64(35)
GEN_UINT_64(36)
GEN_UINT_64(37)
GEN_UINT_64(38)
GEN_UINT_64(39)
GEN_UINT_64(40)
GEN_UINT_64(41)
GEN_UINT_64(42)
GEN_UINT_64(43)
GEN_UINT_64(44)
GEN_UINT_64(45)
GEN_UINT_64(46)
GEN_UINT_64(47)
GEN_UINT_64(48)
GEN_UINT_64(49)
GEN_UINT_64(50)
GEN_UINT_64(51)
GEN_UINT_64(52)
GEN_UINT_64(53)
GEN_UINT_64(54)
GEN_UINT_64(55)
GEN_UINT_64(56)
GEN_UINT_64(57)
GEN_UINT_64(58)
GEN_UINT_64(59)
GEN_UINT_64(60)
GEN_UINT_64(61)
GEN_UINT_64(62)
GEN_UINT_64(63)

#endif  /* __COGENT_DEFNS_H__ */
