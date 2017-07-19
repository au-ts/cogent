/*
This build info header is now disabled by --fno-gen-header.
--------------------------------------------------------------------------------
We strongly discourage users from generating individual files for Isabelle
proofs, as it will end up with an inconsistent collection of output files (i.e.
Isabelle input files).
*/

#include <adt.h>
#include <rbt.h>
#include <stdio.h>
struct WrapperState {
    void *priv;
    struct semaphore lock;
    struct super_block *sb;
} ;
typedef struct inode VfsInodeAbstract;
typedef struct kstat VfsStat;
typedef struct iattr VfsIattr;
typedef struct buffer_head OSBuffer;
typedef struct WrapperState SysState;
typedef struct WrapperState WrapperState;
typedef struct dir_context OSDirContext;
typedef struct page OSPageBuffer;
typedef struct address_space VfsMemoryMap;
typedef struct page OSPage;
typedef struct ubi_volume_desc UbiVol;
typedef struct ubi_volume_info UbiVolInfo;
typedef struct ubi_device_info UbiDevInfo;
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
enum {
    LET_TRUE = 1,
} ;
enum {
    LETBANG_TRUE = 1,
} ;
enum tag_t {
    TAG_ENUM_Error,
    TAG_ENUM_Success,
    TAG_ENUM_TObjData,
    TAG_ENUM_TObjDel,
    TAG_ENUM_TObjDentarr,
    TAG_ENUM_TObjInode,
    TAG_ENUM_TObjPad,
    TAG_ENUM_TObjSummary,
    TAG_ENUM_TObjSuper,
} ;
typedef enum tag_t tag_t;
enum untyped_func_enum {
    FUN_ENUM_fsm_init,
    FUN_ENUM_rbt_create_0,
    FUN_ENUM_wordarray_create_0,
    FUN_ENUM_wordarray_create_1,
    FUN_ENUM_wordarray_free_0,
    FUN_ENUM_wordarray_free_1,
} ;
typedef enum untyped_func_enum untyped_func_enum;
typedef untyped_func_enum t30;
typedef untyped_func_enum t31;
typedef untyped_func_enum t32;
typedef untyped_func_enum t33;
typedef untyped_func_enum t34;
typedef untyped_func_enum t35;
struct WordArray_u32 {
    int len;
    u32 *values;
} ;
typedef struct WordArray_u32 WordArray_u32;
struct t1 {
    SysState *p1;
    WordArray_u32 *p2;
} ;
typedef struct t1 t1;
struct WordArray_u8 {
    int len;
    u8 *values;
} ;
typedef struct WordArray_u8 WordArray_u8;
struct t2 {
    SysState *p1;
    WordArray_u8 *p2;
} ;
typedef struct t2 t2;
struct t3 {
    u16 count;
    u64 sqnum;
} ;
typedef struct t3 t3;
struct Rbt_u64_ut3 {
    struct rbt_root rbt;
} ;
typedef struct Rbt_u64_ut3 Rbt_u64_ut3;
struct t4 {
    SysState *p1;
    Rbt_u64_ut3 *p2;
} ;
typedef struct t4 t4;
struct t5 {
    tag_t tag;
    SysState *Error;
    t4 Success;
} ;
typedef struct t5 t5;
struct t6 {
    SysState *p1;
    u32 p2;
} ;
typedef struct t6 t6;
struct t7 {
    tag_t tag;
    SysState *Error;
    t1 Success;
} ;
typedef struct t7 t7;
struct t8 {
    tag_t tag;
    SysState *Error;
    t2 Success;
} ;
typedef struct t8 t8;
struct t9 {
    u32 nb_eb;
    u32 eb_size;
    u32 io_size;
    u32 nb_reserved_gc;
    u32 nb_reserved_del;
    u32 cur_eb;
    u32 cur_offs;
    u32 last_inum;
    u64 next_sqnum;
} ;
typedef struct t9 t9;
struct t10 {
    u64 id;
    WordArray_u8 *odata;
} ;
typedef struct t10 t10;
struct t11 {
    u64 id;
} ;
typedef struct t11 t11;
struct t12 {
    u32 ino;
    u8 dtype;
    u16 nlen;
    WordArray_u8 *name;
} ;
typedef struct t12 t12;
struct Array_t12 {
    int len;
    t12 **values;
} ;
typedef struct Array_t12 Array_t12;
struct t13 {
    u64 id;
    u32 nb_dentry;
    Array_t12 *entries;
} ;
typedef struct t13 t13;
struct t14 {
    u64 id;
    u64 size;
    u64 atime_sec;
    u64 ctime_sec;
    u64 mtime_sec;
    u32 nlink;
    u32 uid;
    u32 gid;
    u32 mode;
    u32 flags;
} ;
typedef struct t14 t14;
struct t15 {
    u64 id;
    u64 sqnum;
    u32 len;
    u32 del_flags_and_offs;
    u16 count;
} ;
typedef struct t15 t15;
struct WordArray_ut15 {
    int len;
    t15 *values;
} ;
typedef struct WordArray_ut15 WordArray_ut15;
struct t16 {
    u32 nb_sum_entry;
    WordArray_ut15 *entries;
    u32 sum_offs;
} ;
typedef struct t16 t16;
struct t17 {
    tag_t tag;
    t10 TObjData;
    t11 TObjDel;
    t13 *TObjDentarr;
    t14 *TObjInode;
    unit_t TObjPad;
    t16 *TObjSummary;
    t9 *TObjSuper;
} ;
typedef struct t17 t17;
struct t18 {
    u32 magic;
    u32 crc;
    u64 sqnum;
    u32 offs;
    u32 len;
    u8 trans;
    u8 otype;
    t17 ounion;
} ;
typedef struct t18 t18;
struct t19 {
    u32 eb_recovery;
    u32 eb_recovery_offs;
    t9 *super;
    t18 *obj_sup;
    u32 super_offs;
    UbiVolInfo *vol;
    UbiDevInfo *dev;
    bool_t no_summary;
} ;
typedef struct t19 t19;
struct t20 {
    u32 nb_free_eb;
    WordArray_u8 *used_eb;
    WordArray_u32 *dirty_space;
    Rbt_u64_ut3 *gim;
} ;
typedef struct t20 t20;
struct t21 {
    SysState *p1;
    t19 *p2;
    t20 *p3;
} ;
typedef struct t21 t21;
struct t22 {
    u32 p1;
    t20 *p2;
} ;
typedef struct t22 t22;
struct t23 {
    tag_t tag;
    t22 Error;
    t20 *Success;
} ;
typedef struct t23 t23;
struct t24 {
    SysState *p1;
    t23 p2;
} ;
typedef struct t24 t24;
struct t25 {
    tag_t tag;
    t22 Error;
} ;
typedef struct t25 t25;
struct t26 {
    tag_t tag;
    t2 Success;
} ;
typedef struct t26 t26;
struct t27 {
    tag_t tag;
    t1 Success;
} ;
typedef struct t27 t27;
struct t28 {
    tag_t tag;
    t4 Success;
} ;
typedef struct t28 t28;
struct t29 {
    tag_t tag;
    t20 *Success;
} ;
typedef struct t29 t29;
static inline SysState *wordarray_free_1(t1);
static inline SysState *wordarray_free_0(t2);
static inline t5 rbt_create_0(SysState *);
static inline t7 wordarray_create_1(t6);
static inline t8 wordarray_create_0(t6);
t24 fsm_init(t21, int *);
struct ffi_fsm_init_ds {
  t24 *ret;
  int *ds;
};
struct ffi_fsm_init_ds *ffi_fsm_init(t21 *);
void ffi_destroy_Ct68 (t20 *);
static inline t5 dispatch_t30(untyped_func_enum a2, SysState *a3)
{
    return rbt_create_0(a3);
}
static inline SysState *dispatch_t31(untyped_func_enum a2, t1 a3)
{
    return wordarray_free_1(a3);
}
static inline SysState *dispatch_t32(untyped_func_enum a2, t2 a3)
{
    return wordarray_free_0(a3);
}
static inline t24 dispatch_t33(untyped_func_enum a2, t21 a3, int *ds)
{
    return fsm_init(a3, ds);
}
static inline t7 dispatch_t34(untyped_func_enum a2, t6 a3)
{
    return wordarray_create_1(a3);
}
static inline t8 dispatch_t35(untyped_func_enum a2, t6 a3)
{
    return wordarray_create_0(a3);
}
typedef WordArray_u8 CString;
typedef u32 ErrCode;
typedef t20 FsmState;
typedef t3 GimNode;
typedef t19 MountState;
typedef t18 Obj;
typedef t10 ObjData;
typedef t11 ObjDel;
typedef t13 ObjDentarr;
typedef t12 ObjDentry;
typedef u64 ObjId;
typedef u64 ObjIdData;
typedef u64 ObjIdDentarr;
typedef u64 ObjIdInode;
typedef t14 ObjInode;
typedef u32 ObjInodeFlags;
typedef t15 ObjSumEntry;
typedef t16 ObjSummary;
typedef t9 ObjSuper;
typedef u8 ObjTrans;
typedef u8 ObjType;
typedef t17 ObjUnion;
typedef u32 WordArrayIndex;
typedef t21 fsm_init_arg;
typedef t24 fsm_init_ret;
typedef SysState *rbt_create_0_arg;
typedef t5 rbt_create_0_ret;
typedef t6 wordarray_create_0_arg;
typedef t8 wordarray_create_0_ret;
typedef t6 wordarray_create_1_arg;
typedef t7 wordarray_create_1_ret;
typedef t2 wordarray_free_0_arg;
typedef SysState *wordarray_free_0_ret;
typedef t1 wordarray_free_1_arg;
typedef SysState *wordarray_free_1_ret;
t24 fsm_init(t21 a1, int *ds)
{
    SysState *r2 = a1.p1;
    t19 *r3 = a1.p2;
    t20 *r4 = a1.p3;
    u32 r5;
    
    if (LET_TRUE) {
        t9 *r6 = (*r3).super;
        
        r5 = (*r6).nb_eb;
    } else
        ;
    
    t8 r7;
    
    if (LET_TRUE) {
        t6 r8 = (t6) {.p1 = r2, .p2 = r5};
        r7 = wordarray_create_0(r8);
    } else
        ;
    
    t24 r9;
    
    if (r7.tag == TAG_ENUM_Error) {
        printf("1st malloc, failed\n");
        ds[0] = 0;
        u8 r10 = 12U;
        u32 r11 = (u32) r10;
        t22 r12 = (t22) {.p1 = r11, .p2 = r4};
        t25 r13 = (t25) {.tag = TAG_ENUM_Error, .Error = r12};
        t23 r14 = (t23) {.tag = r13.tag, .Error = r13.Error};
        
        r9 = (t24) {.p1 = r7.Error, .p2 = r14};
    } else {
        printf ("1st malloc, of size %u\n", r5);
        ds[0] = 1;
        t26 r15 = {.tag =r7.tag, .Success =r7.Success};
        t2 r16 = r15.Success;
        SysState *r17 = r16.p1;
        WordArray_u8 *r18 = r16.p2;
        t7 r19;
        
        if (LET_TRUE) {
            t6 r20 = (t6) {.p1 = r17, .p2 = r5};
            r19 = wordarray_create_1(r20);
        } else
            ;
        
        t24 r21;
        
        if (r19.tag == TAG_ENUM_Error) {
            printf ("2nd malloc, failed\n");
            ds[1] = 0;
            SysState *r22;
            if (LET_TRUE) {
                t2 r23 = (t2) {.p1 = r19.Error, .p2 = r18};
                
                r22 = wordarray_free_0(r23);
            } else
                ;
            
            u8 r24 = 12U;
            u32 r25 = (u32) r24;
            t22 r26 = (t22) {.p1 = r25, .p2 = r4};
            t25 r27 = (t25) {.tag = TAG_ENUM_Error, .Error = r26};
            t23 r28 = (t23) {.tag = r27.tag, .Error = r27.Error};
            
            r21 = (t24) {.p1 = r22, .p2 = r28};
        } else {
            printf ("2nd malloc, succeeded\n");
            ds[1] = 1;
            t27 r29 = {.tag =r19.tag, .Success =r19.Success};
            t1 r30 = r29.Success;
            SysState *r31 = r30.p1;
            WordArray_u32 *r32 = r30.p2;
            t5 r33 = rbt_create_0(r31);
            t24 r34;
            
            if (r33.tag == TAG_ENUM_Error) {
                printf ("rbt creation, failed!\n");
                SysState *r35;
                if (LET_TRUE) {
                    t2 r36 = (t2) {.p1 = r33.Error, .p2 = r18};
                    
                    r35 = wordarray_free_0(r36);
                } else
                    ;
                
                SysState *r37;
                
                if (LET_TRUE) {
                    t1 r38 = (t1) {.p1 = r35, .p2 = r32};
                    
                    r37 = wordarray_free_1(r38);
                } else
                    ;
                
                u8 r39 = 12U;
                u32 r40 = (u32) r39;
                t22 r41 = (t22) {.p1 = r40, .p2 = r4};
                t25 r42 = (t25) {.tag = TAG_ENUM_Error, .Error = r41};
                t23 r43 = (t23) {.tag = r42.tag, .Error = r42.Error};
                
                r34 = (t24) {.p1 = r37, .p2 = r43};
            } else {
                printf ("rbt creation, succeeded\n");
                t28 r44 = {.tag =r33.tag, .Success =r33.Success};
                t4 r45 = r44.Success;
                SysState *r46 = r45.p1;
                Rbt_u64_ut3 *r47 = r45.p2;
                u32 r48;
                
                if (LET_TRUE) {
                    t9 *r49 = (*r3).super;
                    u32 r50 = (*r49).nb_eb;
                    u8 r51 = 2U;
                    u32 r52 = (u32) r51;
                    
                    r48 = r50 - r52;
                } else
                    ;
                
                t20 *r53 = r4;
                
                (*r53).used_eb = r18;
                
                t20 *r54 = r53;
                t20 *r55 = r54;
                
                (*r55).dirty_space = r32;
                
                t20 *r56 = r55;
                t20 *r57 = r56;
                
                (*r57).gim = r47;
                
                t20 *r58 = r57;
                t20 *r59 = r58;
                
                (*r59).nb_free_eb = r48;
                
                t20 *r60 = r59;
                t29 r61 = (t29) {.tag = TAG_ENUM_Success, .Success = r60};
                t23 r62 = (t23) {.tag = r61.tag, .Success = r61.Success};
                
                r34 = (t24) {.p1 = r46, .p2 = r62};
            }
            r21 = r34;
        }
        r9 = r21;
    }
    
    t24 r63 = r9;
    printf ("********************\n");
    return r63;
}
u16 u8_to_u16(u8 x)
{
    return (u16) x;
}
u32 u8_to_u32(u8 x)
{
    return (u32) x;
}
u64 u8_to_u64(u8 x)
{
    return (u64) x;
}
u8 u16_to_u8(u16 x)
{
    return (u8) x;
}
u32 u16_to_u32(u16 x)
{
    return (u32) x;
}
u8 u32_to_u8(u32 x)
{
    return (u8) x;
}
u16 u32_to_u16(u32 x)
{
    return (u16) x;
}
u64 u32_to_u64(u32 x)
{
    return (u64) x;
}
u32 u64_to_u32(u64 x)
{
    return (u32) x;
}
u8 u64_to_u8(u64 x)
{
    return (u8) x;
}
u16 u64_to_u16(u64 x)
{
    return (u16) x;
}
t5 rbt_create_0(SysState *ex)
{
    t5 ret;
    
    ret.Success.p2 = kzalloc(sizeof(*ret.Success.p2));
    if (!ret.Success.p2) {
        ret.tag = TAG_ENUM_Error;
        ret.Error = ex;
        return ret;
    }
    ret.tag = TAG_ENUM_Success;
    ret.Success.p1 = ex;
    return ret;
}
t8 wordarray_create_0(t6 args)
{
    SysState *ex = args.p1;
    u32 size = args.p2;
    t8 ret;
    WordArray_u8 *array = kmalloc(sizeof(*array));
    
    if (array == NULL || !size) {
        ret.tag = TAG_ENUM_Error;
        ret.Error = ex;
    } else {
        array->values = kzalloc(size * sizeof(*array->values));
        if (array->values == NULL) {
            kfree(array);
            ret.tag = TAG_ENUM_Error;
            ret.Error = ex;
        } else {
            array->len = size;
            ret.tag = TAG_ENUM_Success;
            ret.Success.p1 = ex;
            ret.Success.p2 = array;
        }
    }
    return ret;
}
t7 wordarray_create_1(t6 args)
{
    SysState *ex = args.p1;
    u32 size = args.p2;
    t7 ret;
    WordArray_u32 *array = kmalloc(sizeof(*array));
    
    if (array == NULL || !size) {
        ret.tag = TAG_ENUM_Error;
        ret.Error = ex;
    } else {
        array->values = kzalloc(size * sizeof(*array->values));
        if (array->values == NULL) {
            kfree(array);
            ret.tag = TAG_ENUM_Error;
            ret.Error = ex;
        } else {
            array->len = size;
            ret.tag = TAG_ENUM_Success;
            ret.Success.p1 = ex;
            ret.Success.p2 = array;
        }
    }
    return ret;
}
SysState *wordarray_free_0(t2 args)
{
    WordArray_u8 *array = args.p2;
    
    if (array->values)
        kfree(array->values);
    kfree(array);
    return args.p1;
}
SysState *wordarray_free_1(t1 args)
{
    WordArray_u32 *array = args.p2;
    
    if (array->values)
        kfree(array->values);
    kfree(array);
    return args.p1;
}


struct ffi_fsm_init_ds *ffi_fsm_init(t21 *a1)
{
  struct ffi_fsm_init_ds *rets = malloc (sizeof (rets));
  t24* ret = malloc (sizeof (t24));
  int* ds = malloc (2 * sizeof (int));
    if (ret) {
      *ret = fsm_init (*a1, ds);
    } else {
      printf ("ffi_fsm_init malloc failed\n");
    }
    rets->ret = ret;
    rets->ds = ds;
    return rets;
}

void ffi_destroy_Ct68 (t20 *args)
{
  // u32 nb_free_eb;
  WordArray_u8 *used_eb = args->used_eb;
  WordArray_u32 *dirty_space = args->dirty_space;
  // Rbt_u64_ut3 *gim = args.gim;

  t2 used_eb_args = {.p1 = NULL, .p2 = used_eb};
  wordarray_free_0 (used_eb_args);
  t1 dirty_space_args = {.p1 = NULL, .p2 = dirty_space};
  wordarray_free_1 (dirty_space_args);
  
  return;
}
