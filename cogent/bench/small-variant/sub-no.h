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
} ;
typedef enum tag_t tag_t;
enum untyped_func_enum {
    FUN_ENUM_foo,
} ;
typedef enum untyped_func_enum untyped_func_enum;
typedef untyped_func_enum t4;
#define FUN_DISP_MACRO_dispatch_t4(a1, a2, a3)\
{\
    {\
        a1 = foo(a3);\
    }\
}
struct t1 {
    tag_t tag;
    u32 A;
    bool_t B;
    unit_t C;
} ;
typedef struct t1 t1;
struct t2 {
    tag_t tag;
    bool_t B;
    unit_t C;
} ;
typedef struct t2 t2;
struct t3 {
    tag_t tag;
    bool_t B;
} ;
typedef struct t3 t3;
extern t2 foo(t1);
static inline t2 dispatch_t4(untyped_func_enum a2, t1 a3)
{
    return foo(a3);
}
typedef t1 V;
typedef t1 foo_arg;
typedef t2 foo_ret;
#endif


