// This build info header is now disabled by --fno-gen-header.
// --------------------------------------------------------------------------------
// We strongly discourage users from generating individual files for Isabelle
// proofs, as it will end up with an inconsistent collection of output files (i.e.
// Isabelle input files).

#ifndef SUB_NO_H__
#define SUB_NO_H__

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
    TAG_ENUM_C,
    TAG_ENUM_D,
    TAG_ENUM_E,
    TAG_ENUM_F,
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
    bool_t p1;
    u32 p2;
} ;
typedef struct t1 t1;
struct t2 {
    tag_t tag;
    u32 A;
    bool_t B;
    unit_t C;
    u32 D;
    u64 E;
    t1 F;
} ;
typedef struct t2 t2;
struct t3 {
    tag_t tag;
    bool_t B;
    unit_t C;
    u32 D;
    u64 E;
    t1 F;
} ;
typedef struct t3 t3;
struct t4 {
    tag_t tag;
    unit_t C;
    u32 D;
    u64 E;
    t1 F;
} ;
typedef struct t4 t4;
struct t5 {
    tag_t tag;
    u32 D;
    u64 E;
    t1 F;
} ;
typedef struct t5 t5;
struct t6 {
    tag_t tag;
    u64 E;
    t1 F;
} ;
typedef struct t6 t6;
struct t7 {
    tag_t tag;
    t1 F;
} ;
typedef struct t7 t7;
extern t1 foo(t2);
static inline t1 dispatch_t8(untyped_func_enum a2, t2 a3)
{
    return foo(a3);
}
typedef t2 V;
typedef t2 foo_arg;
typedef t1 foo_ret;
#endif


