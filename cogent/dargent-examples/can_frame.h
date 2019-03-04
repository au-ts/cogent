// This build info header is now disabled by --fno-gen-header.
// --------------------------------------------------------------------------------
// We strongly discourage users from generating individual files for Isabelle
// proofs, as it will end up with an inconsistent collection of output files (i.e.
// Isabelle input files).

#ifndef CAN_FRAME_H__
#define CAN_FRAME_H__

#include <cogent-defns.h>

enum {
    LET_TRUE = 1,
} ;
enum {
    LETBANG_TRUE = 1,
} ;
enum untyped_func_enum {
    FUN_ENUM_get_sid_eid,
} ;
typedef enum untyped_func_enum untyped_func_enum;
typedef untyped_func_enum t11;
#define FUN_DISP_MACRO_dispatch_t11(a1, a2, a3)\
{\
    {\
        a1 = get_sid_eid(a3);\
    }\
}
struct t1 {
    unsigned int data[6U];
} ;
typedef struct t1 *t1;
struct t2 {
    unsigned int data[4U];
} ;
typedef struct t2 *t2;
struct t10 {
    u32 p1;
    u32 p2;
} ;
typedef struct t10 t10;
static inline t10 get_sid_eid(t1);
static inline t10 dispatch_t11(untyped_func_enum a2, t1 a3)
{
    return get_sid_eid(a3);
}
typedef t1 CanFrame;
typedef t2 CanId;
typedef t1 get_sid_eid_arg;
typedef t10 get_sid_eid_ret;
#endif


