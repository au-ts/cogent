// This build info header is now disabled by --fno-gen-header.
// --------------------------------------------------------------------------------
// We strongly discourage users from generating individual files for Isabelle
// proofs, as it will end up with an inconsistent collection of output files (i.e.
// Isabelle input files).

#ifndef VARIANT_H__
#define VARIANT_H__

#include <cogent-defns.h>

enum {
    LET_TRUE = 1,
} ;
enum {
    LETBANG_TRUE = 1,
} ;
enum tag_t {
    TAG_ENUM_A,
    TAG_ENUM_B,
} ;
typedef enum tag_t tag_t;
enum untyped_func_enum {
    FUN_ENUM_foo,
} ;
typedef enum untyped_func_enum untyped_func_enum;
typedef untyped_func_enum t8;
#define FUN_DISP_MACRO_dispatch_t8(a1, a2, a3)\
{\
    {\
        a1 = foo(a3);\
    }\
}
struct t1 {
    unsigned int data[3U];
} ;
typedef struct t1 *t1;
struct t2 {
    tag_t tag;
    u8 A;
    t1 B;
} ;
typedef struct t2 t2;
static inline u64 foo(t2);
static inline u64 dispatch_t8(untyped_func_enum a2, t2 a3)
{
    return foo(a3);
}
typedef t1 S;
typedef t2 foo_arg;
typedef u64 foo_ret;
#endif


