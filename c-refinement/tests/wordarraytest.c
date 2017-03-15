/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include <adt.h>
struct SysState_t {
    char dummy;
};
typedef struct SysState_t SysState;
static inline void dummyFunction(void)
{
    return;
}
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
enum tag_t {
    TAG_ENUM_Error,
    TAG_ENUM_Success
};
typedef enum tag_t tag_t;
enum t126 {
    FUN_ENUM_caller
};
typedef enum t126 t126;
enum t129 {
    FUN_ENUM_test_file_read_next_u32
};
typedef enum t129 t129;
enum t132 {
    FUN_ENUM_cogent_debug
};
typedef enum t132 t132;
enum t135 {
    FUN_ENUM_cogent_assert
};
typedef enum t135 t135;
enum t138 {
    FUN_ENUM_wordarray_cmp
};
typedef enum t138 t138;
enum t141 {
    FUN_ENUM_wordarray_create_0
};
typedef enum t141 t141;
enum t144 {
    FUN_ENUM_wordarray_free_0
};
typedef enum t144 t144;
enum t147 {
    FUN_ENUM_safe_add32,
    FUN_ENUM_safe_sub32
};
typedef enum t147 t147;
enum t150 {
    FUN_ENUM_align32,
    FUN_ENUM_min_u32
};
typedef enum t150 t150;
enum t153 {
    FUN_ENUM_wordarray_get_0
};
typedef enum t153 t153;
enum t156 {
    FUN_ENUM_wordarray_put_0
};
typedef enum t156 t156;
enum t159 {
    FUN_ENUM_safe_add64,
    FUN_ENUM_safe_sub64
};
typedef enum t159 t159;
enum t162 {
    FUN_ENUM_align64
};
typedef enum t162 t162;
enum t165 {
    FUN_ENUM_test_file_close
};
typedef enum t165 t165;
enum t168 {
    FUN_ENUM_test_file_open
};
typedef enum t168 t168;
enum t171 {
    FUN_ENUM_u16_to_u32
};
typedef enum t171 t171;
enum t174 {
    FUN_ENUM_u16_to_u64
};
typedef enum t174 t174;
enum t177 {
    FUN_ENUM_u16_to_u8
};
typedef enum t177 t177;
enum t180 {
    FUN_ENUM_cogent_debug_u16
};
typedef enum t180 t180;
enum t183 {
    FUN_ENUM_cogent_high_16_bits,
    FUN_ENUM_cogent_low_16_bits,
    FUN_ENUM_u32_to_u16
};
typedef enum t183 t183;
enum t186 {
    FUN_ENUM_cogent_log2
};
typedef enum t186 t186;
enum t189 {
    FUN_ENUM_u32_to_u64
};
typedef enum t189 t189;
enum t192 {
    FUN_ENUM_u32_to_u8
};
typedef enum t192 t192;
enum t195 {
    FUN_ENUM_cogent_debug_u32,
    FUN_ENUM_cogent_debug_u32_hex,
    FUN_ENUM_cogent_debug_u32_oct
};
typedef enum t195 t195;
enum t198 {
    FUN_ENUM_u64_to_u32
};
typedef enum t198 t198;
enum t201 {
    FUN_ENUM_cogent_debug_u64,
    FUN_ENUM_cogent_debug_u64_hex
};
typedef enum t201 t201;
enum t204 {
    FUN_ENUM_u8_to_u16
};
typedef enum t204 t204;
enum t207 {
    FUN_ENUM_u8_to_u32
};
typedef enum t207 t207;
enum t210 {
    FUN_ENUM_u8_to_u64
};
typedef enum t210 t210;
enum t213 {
    FUN_ENUM_cogent_debug_u8
};
typedef enum t213 t213;
enum t216 {
    FUN_ENUM_random_u32
};
typedef enum t216 t216;
enum t219 {
    FUN_ENUM_test_stack_probe,
    FUN_ENUM_test_time_end,
    FUN_ENUM_test_time_start
};
typedef enum t219 t219;
struct WordArray_u8 {
    int len;
    u8* values;
};
typedef struct WordArray_u8 WordArray_u8;
struct t1 {
    WordArray_u8* p1;
    WordArray_u8* p2;
};
typedef struct t1 t1;
struct WordArray_u32 {
    int len;
    u32* values;
};
typedef struct WordArray_u32 WordArray_u32;
struct t2 {
    WordArray_u32* p1;
    u32 p2;
};
typedef struct t2 t2;
struct t3 {
    WordArray_u32* arr;
    u32 idx;
    u32 val;
};
typedef struct t3 t3;
struct t4 {
    tag_t tag;
    WordArray_u32* Error;
    WordArray_u32* Success;
};
typedef struct t4 t4;
struct t5 {
    File* p1;
    u32 p2;
};
typedef struct t5 t5;
struct t6 {
    tag_t tag;
    File* Error;
    t5 Success;
};
typedef struct t6 t6;
struct t7 {
    SysState* p1;
    File* p2;
};
typedef struct t7 t7;
struct t8 {
    char* p1;
    char* p2;
};
typedef struct t8 t8;
struct t9 {
    SysState* p1;
    t8 p2;
};
typedef struct t9 t9;
struct t10 {
    tag_t tag;
    SysState* Error;
    t7 Success;
};
typedef struct t10 t10;
struct t11 {
    SysState* p1;
    u32 p2;
};
typedef struct t11 t11;
struct t12 {
    SysState* p1;
    WordArray_u32* p2;
};
typedef struct t12 t12;
struct t13 {
    tag_t tag;
    SysState* Error;
    t12 Success;
};
typedef struct t13 t13;
struct t18 {
    u32 p1;
    u32 p2;
};
typedef struct t18 t18;
struct t40 {
    u64 p1;
    u64 p2;
};
typedef struct t40 t40;
struct t61 {
    tag_t tag;
    unit_t Error;
    u32 Success;
};
typedef struct t61 t61;
struct t64 {
    tag_t tag;
    unit_t Error;
};
typedef struct t64 t64;
struct t67 {
    tag_t tag;
    u32 Success;
};
typedef struct t67 t67;
struct t75 {
    tag_t tag;
    unit_t Error;
    u64 Success;
};
typedef struct t75 t75;
struct t80 {
    tag_t tag;
    u64 Success;
};
typedef struct t80 t80;
struct t119 {
    tag_t tag;
    WordArray_u32* Error;
};
typedef struct t119 t119;
struct t123 {
    tag_t tag;
    SysState* Error;
};
typedef struct t123 t123;
static inline u64 u8_to_u64(u8);
static inline u32 u8_to_u32(u8);
static inline u16 u8_to_u16(u8);
static inline u32 u64_to_u32(u64);
static inline u8 u32_to_u8(u32);
static inline u64 u32_to_u64(u32);
static inline u16 u32_to_u16(u32);
static inline u8 u16_to_u8(u16);
static inline u32 u16_to_u32(u16);
static inline unit_t test_time_start(unit_t);
static inline unit_t test_time_end(unit_t);
static inline unit_t test_stack_probe(unit_t);
static inline u32 random_u32(unit_t);
static inline u32 cogent_log2(u32);
static inline unit_t cogent_debug_u64_hex(u64);
static inline unit_t cogent_debug_u64(u64);
static inline unit_t cogent_debug_u32_oct(u32);
static inline unit_t cogent_debug_u32_hex(u32);
static inline unit_t cogent_debug_u32(u32);
static inline unit_t cogent_debug(char*);
static inline unit_t cogent_assert(bool_t);
static inline bool_t wordarray_cmp(t1);
static inline u32 wordarray_get_0(t2);
static inline t4 wordarray_put_0(t3);
static inline t6 test_file_read_next_u32(File*);
static inline SysState* test_file_close(t7);
static inline t10 test_file_open(t9);
static inline t13 wordarray_create_0(t11);
static inline SysState* wordarray_free_0(t12);
static inline u64 u16_to_u64(u16);
static inline u32 min_u32(t18);
static inline u16 cogent_low_16_bits(u32);
static inline u16 cogent_high_16_bits(u32);
static inline unit_t cogent_debug_u8(u8);
static inline unit_t cogent_debug_u16(u16);
static inline u64 align64(t40);
static inline u32 align32(t18);
static inline t61 safe_add32(t18);
static inline t75 safe_add64(t40);
static inline t61 safe_sub32(t18);
static inline t75 safe_sub64(t40);
static inline SysState* caller(SysState*);
static inline SysState* dispatch_t126(t126 a127, SysState* a128)
{
    return caller(a128);
}
static inline t6 dispatch_t129(t129 a130, File* a131)
{
    return test_file_read_next_u32(a131);
}
static inline unit_t dispatch_t132(t132 a133, char* a134)
{
    return cogent_debug(a134);
}
static inline unit_t dispatch_t135(t135 a136, bool_t a137)
{
    return cogent_assert(a137);
}
static inline bool_t dispatch_t138(t138 a139, t1 a140)
{
    return wordarray_cmp(a140);
}
static inline t13 dispatch_t141(t141 a142, t11 a143)
{
    return wordarray_create_0(a143);
}
static inline SysState* dispatch_t144(t144 a145, t12 a146)
{
    return wordarray_free_0(a146);
}
static inline t61 dispatch_t147(t147 a148, t18 a149)
{
    switch (a148) {
        
        
      case FUN_ENUM_safe_add32:
        return safe_add32(a149);
        
      default:
        return safe_sub32(a149);
    }
}
static inline u32 dispatch_t150(t150 a151, t18 a152)
{
    switch (a151) {
        
        
      case FUN_ENUM_align32:
        return align32(a152);
        
      default:
        return min_u32(a152);
    }
}
static inline u32 dispatch_t153(t153 a154, t2 a155)
{
    return wordarray_get_0(a155);
}
static inline t4 dispatch_t156(t156 a157, t3 a158)
{
    return wordarray_put_0(a158);
}
static inline t75 dispatch_t159(t159 a160, t40 a161)
{
    switch (a160) {
        
        
      case FUN_ENUM_safe_add64:
        return safe_add64(a161);
        
      default:
        return safe_sub64(a161);
    }
}
static inline u64 dispatch_t162(t162 a163, t40 a164)
{
    return align64(a164);
}
static inline SysState* dispatch_t165(t165 a166, t7 a167)
{
    return test_file_close(a167);
}
static inline t10 dispatch_t168(t168 a169, t9 a170)
{
    return test_file_open(a170);
}
static inline u32 dispatch_t171(t171 a172, u16 a173)
{
    return u16_to_u32(a173);
}
static inline u64 dispatch_t174(t174 a175, u16 a176)
{
    return u16_to_u64(a176);
}
static inline u8 dispatch_t177(t177 a178, u16 a179)
{
    return u16_to_u8(a179);
}
static inline unit_t dispatch_t180(t180 a181, u16 a182)
{
    return cogent_debug_u16(a182);
}
static inline u16 dispatch_t183(t183 a184, u32 a185)
{
    switch (a184) {
        
        
      case FUN_ENUM_cogent_high_16_bits:
        return cogent_high_16_bits(a185);
        
        
      case FUN_ENUM_cogent_low_16_bits:
        return cogent_low_16_bits(a185);
        
      default:
        return u32_to_u16(a185);
    }
}
static inline u32 dispatch_t186(t186 a187, u32 a188)
{
    return cogent_log2(a188);
}
static inline u64 dispatch_t189(t189 a190, u32 a191)
{
    return u32_to_u64(a191);
}
static inline u8 dispatch_t192(t192 a193, u32 a194)
{
    return u32_to_u8(a194);
}
static inline unit_t dispatch_t195(t195 a196, u32 a197)
{
    switch (a196) {
        
        
      case FUN_ENUM_cogent_debug_u32:
        return cogent_debug_u32(a197);
        
        
      case FUN_ENUM_cogent_debug_u32_hex:
        return cogent_debug_u32_hex(a197);
        
      default:
        return cogent_debug_u32_oct(a197);
    }
}
static inline u32 dispatch_t198(t198 a199, u64 a200)
{
    return u64_to_u32(a200);
}
static inline unit_t dispatch_t201(t201 a202, u64 a203)
{
    switch (a202) {
        
        
      case FUN_ENUM_cogent_debug_u64:
        return cogent_debug_u64(a203);
        
      default:
        return cogent_debug_u64_hex(a203);
    }
}
static inline u16 dispatch_t204(t204 a205, u8 a206)
{
    return u8_to_u16(a206);
}
static inline u32 dispatch_t207(t207 a208, u8 a209)
{
    return u8_to_u32(a209);
}
static inline u64 dispatch_t210(t210 a211, u8 a212)
{
    return u8_to_u64(a212);
}
static inline unit_t dispatch_t213(t213 a214, u8 a215)
{
    return cogent_debug_u8(a215);
}
static inline u32 dispatch_t216(t216 a217, unit_t a218)
{
    return random_u32(a218);
}
static inline unit_t dispatch_t219(t219 a220, unit_t a221)
{
    switch (a220) {
        
        
      case FUN_ENUM_test_stack_probe:
        return test_stack_probe(a221);
        
        
      case FUN_ENUM_test_time_end:
        return test_time_end(a221);
        
      default:
        return test_time_start(a221);
    }
}
typedef WordArray_u8 CString;
typedef u32 ErrCode;
typedef u32 WordArrayIndex;
typedef t18 align32_arg;
typedef u32 align32_ret;
typedef t40 align64_arg;
typedef u64 align64_ret;
typedef SysState* caller_arg;
typedef SysState* caller_ret;
typedef bool_t cogent_assert_arg;
typedef unit_t cogent_assert_ret;
typedef char* cogent_debug_arg;
typedef unit_t cogent_debug_ret;
typedef u16 cogent_debug_u16_arg;
typedef unit_t cogent_debug_u16_ret;
typedef u32 cogent_debug_u32_arg;
typedef u32 cogent_debug_u32_hex_arg;
typedef unit_t cogent_debug_u32_hex_ret;
typedef u32 cogent_debug_u32_oct_arg;
typedef unit_t cogent_debug_u32_oct_ret;
typedef unit_t cogent_debug_u32_ret;
typedef u64 cogent_debug_u64_arg;
typedef u64 cogent_debug_u64_hex_arg;
typedef unit_t cogent_debug_u64_hex_ret;
typedef unit_t cogent_debug_u64_ret;
typedef u8 cogent_debug_u8_arg;
typedef unit_t cogent_debug_u8_ret;
typedef u32 cogent_high_16_bits_arg;
typedef u16 cogent_high_16_bits_ret;
typedef u32 cogent_log2_arg;
typedef u32 cogent_log2_ret;
typedef u32 cogent_low_16_bits_arg;
typedef u16 cogent_low_16_bits_ret;
typedef t18 min_u32_arg;
typedef u32 min_u32_ret;
typedef unit_t random_u32_arg;
typedef u32 random_u32_ret;
typedef t18 safe_add32_arg;
typedef t61 safe_add32_ret;
typedef t40 safe_add64_arg;
typedef t75 safe_add64_ret;
typedef t18 safe_sub32_arg;
typedef t61 safe_sub32_ret;
typedef t40 safe_sub64_arg;
typedef t75 safe_sub64_ret;
typedef t7 test_file_close_arg;
typedef SysState* test_file_close_ret;
typedef t9 test_file_open_arg;
typedef t10 test_file_open_ret;
typedef File* test_file_read_next_u32_arg;
typedef t6 test_file_read_next_u32_ret;
typedef unit_t test_stack_probe_arg;
typedef unit_t test_stack_probe_ret;
typedef unit_t test_time_end_arg;
typedef unit_t test_time_end_ret;
typedef unit_t test_time_start_arg;
typedef unit_t test_time_start_ret;
typedef u16 u16_to_u32_arg;
typedef u32 u16_to_u32_ret;
typedef u16 u16_to_u64_arg;
typedef u64 u16_to_u64_ret;
typedef u16 u16_to_u8_arg;
typedef u8 u16_to_u8_ret;
typedef u32 u32_to_u16_arg;
typedef u16 u32_to_u16_ret;
typedef u32 u32_to_u64_arg;
typedef u64 u32_to_u64_ret;
typedef u32 u32_to_u8_arg;
typedef u8 u32_to_u8_ret;
typedef u64 u64_to_u32_arg;
typedef u32 u64_to_u32_ret;
typedef u8 u8_to_u16_arg;
typedef u16 u8_to_u16_ret;
typedef u8 u8_to_u32_arg;
typedef u32 u8_to_u32_ret;
typedef u8 u8_to_u64_arg;
typedef u64 u8_to_u64_ret;
typedef t1 wordarray_cmp_arg;
typedef bool_t wordarray_cmp_ret;
typedef t11 wordarray_create_0_arg;
typedef t13 wordarray_create_0_ret;
typedef t12 wordarray_free_0_arg;
typedef SysState* wordarray_free_0_ret;
typedef t2 wordarray_get_0_arg;
typedef u32 wordarray_get_0_ret;
typedef t3 wordarray_put_0_arg;
typedef t4 wordarray_put_0_ret;
static inline u64 u16_to_u64(u16 a14)
{
    u16 r15 = a14;
    u32 r16 = u16_to_u32(r15);
    
    return u32_to_u64(r16);
}
static inline u32 min_u32(t18 a17)
{
    bool_t r19 = (bool_t) {.boolean = a17.p1 < a17.p2};
    u32 r20;
    
    if (r19.boolean) {
        r20 = a17.p1;
    } else {
        r20 = a17.p2;
    }
    return r20;
}
static inline u16 cogent_low_16_bits(u32 a21)
{
    u32 r22 = a21;
    u16 r23 = 65535U;
    u32 r24 = (u32) r23;
    u32 r25 = r22 & r24;
    
    return u32_to_u16(r25);
}
static inline u16 cogent_high_16_bits(u32 a26)
{
    u32 r27 = a26;
    u32 r28 = 4294901760UL;
    u32 r29 = r27 & r28;
    u8 r30 = 16U;
    u32 r31 = u8_to_u32(r30);
    u32 r32 = r31 >= 32U ? 0U : r29 >> r31;
    
    return u32_to_u16(r32);
}
static inline unit_t cogent_debug_u8(u8 a33)
{
    u8 r34 = a33;
    u32 r35 = u8_to_u32(r34);
    
    return cogent_debug_u32(r35);
}
static inline unit_t cogent_debug_u16(u16 a36)
{
    u16 r37 = a36;
    u32 r38 = u16_to_u32(r37);
    
    return cogent_debug_u32(r38);
}
static inline u64 align64(t40 a39)
{
    u64 r41 = a39.p1 % a39.p2;
    u8 r42 = 0U;
    u64 r43 = (u64) r42;
    bool_t r44 = (bool_t) {.boolean = r41 != r43};
    u64 r45;
    
    if (r44.boolean) {
        u64 r46 = a39.p1 + a39.p2;
        u64 r47 = a39.p1 % a39.p2;
        
        r45 = r46 - r47;
    } else {
        r45 = a39.p1;
    }
    return r45;
}
static inline u32 align32(t18 a48)
{
    u32 r49 = a48.p1 % a48.p2;
    u8 r50 = 0U;
    u32 r51 = (u32) r50;
    bool_t r52 = (bool_t) {.boolean = r49 != r51};
    u32 r53;
    
    if (r52.boolean) {
        u32 r54 = a48.p1 + a48.p2;
        u32 r55 = a48.p1 % a48.p2;
        
        r53 = r54 - r55;
    } else {
        r53 = a48.p1;
    }
    return r53;
}
static inline t61 safe_add32(t18 a56)
{
    u32 r57 = a56.p1 + a56.p2;
    bool_t r58 = (bool_t) {.boolean = r57 < a56.p1};
    bool_t r59 = (bool_t) {.boolean = r57 < a56.p2};
    bool_t r60 = (bool_t) {.boolean = r58.boolean || r59.boolean};
    t61 r62;
    
    if (r60.boolean) {
        unit_t r63 = (unit_t) {.dummy = 0U};
        t64 r65 = (t64) {.tag = TAG_ENUM_Error, .Error = r63};
        t61 r66;
        
        r66.tag = r65.tag;
        r66.Error = r65.Error;
        r62 = r66;
    } else {
        t67 r68 = (t67) {.tag = TAG_ENUM_Success, .Success = r57};
        t61 r69;
        
        r69.tag = r68.tag;
        r69.Success = r68.Success;
        r62 = r69;
    }
    return r62;
}
static inline t75 safe_add64(t40 a70)
{
    u64 r71 = a70.p1 + a70.p2;
    bool_t r72 = (bool_t) {.boolean = r71 < a70.p1};
    bool_t r73 = (bool_t) {.boolean = r71 < a70.p2};
    bool_t r74 = (bool_t) {.boolean = r72.boolean || r73.boolean};
    t75 r76;
    
    if (r74.boolean) {
        unit_t r77 = (unit_t) {.dummy = 0U};
        t64 r78 = (t64) {.tag = TAG_ENUM_Error, .Error = r77};
        t75 r79;
        
        r79.tag = r78.tag;
        r79.Error = r78.Error;
        r76 = r79;
    } else {
        t80 r81 = (t80) {.tag = TAG_ENUM_Success, .Success = r71};
        t75 r82;
        
        r82.tag = r81.tag;
        r82.Success = r81.Success;
        r76 = r82;
    }
    return r76;
}
static inline t61 safe_sub32(t18 a83)
{
    u32 r84 = a83.p1 - a83.p2;
    bool_t r85 = (bool_t) {.boolean = r84 > a83.p1};
    t61 r86;
    
    if (r85.boolean) {
        unit_t r87 = (unit_t) {.dummy = 0U};
        t64 r88 = (t64) {.tag = TAG_ENUM_Error, .Error = r87};
        t61 r89;
        
        r89.tag = r88.tag;
        r89.Error = r88.Error;
        r86 = r89;
    } else {
        t67 r90 = (t67) {.tag = TAG_ENUM_Success, .Success = r84};
        t61 r91;
        
        r91.tag = r90.tag;
        r91.Success = r90.Success;
        r86 = r91;
    }
    return r86;
}
static inline t75 safe_sub64(t40 a92)
{
    u64 r93 = a92.p1 - a92.p2;
    bool_t r94 = (bool_t) {.boolean = r93 > a92.p1};
    t75 r95;
    
    if (r94.boolean) {
        unit_t r96 = (unit_t) {.dummy = 0U};
        t64 r97 = (t64) {.tag = TAG_ENUM_Error, .Error = r96};
        t75 r98;
        
        r98.tag = r97.tag;
        r98.Error = r97.Error;
        r95 = r98;
    } else {
        t80 r99 = (t80) {.tag = TAG_ENUM_Success, .Success = r93};
        t75 r100;
        
        r100.tag = r99.tag;
        r100.Success = r99.Success;
        r95 = r100;
    }
    return r95;
}
static inline SysState* caller(SysState* a101)
{
    SysState* r102 = a101;
    u8 r103 = 4U;
    u32 r104 = (u32) r103;
    t11 r105 = (t11) {.p1 = r102, .p2 = r104};
    t13 r106 = wordarray_create_0(r105);
    SysState* r107;
    
    if (r106.tag == TAG_ENUM_Success) {
        u8 r108 = 0U;
        u32 r109 = u8_to_u32(r108);
        u8 r110 = 42U;
        u32 r111 = u8_to_u32(r110);
        t3 r112 = (t3) {.arr = r106.Success.p2, .idx = r109, .val = r111};
        t4 r113 = wordarray_put_0(r112);
        
        if (r113.tag == TAG_ENUM_Success) {
            u8 r114 = 0U;
            u32 r115 = (u32) r114;
            t2 r116 = (t2) {.p1 = r113.Success, .p2 = r115};
            u32 r117 = wordarray_get_0(r116);
            t12 r118 = (t12) {.p1 = r106.Success.p1, .p2 = r113.Success};
            
            r107 = wordarray_free_0(r118);
        } else {
            t119 r120 = {.tag =r113.tag, .Error =r113.Error};
            WordArray_u32* r121 = r120.Error;
            t12 r122 = (t12) {.p1 = r106.Success.p1, .p2 = r121};
            
            r107 = wordarray_free_0(r122);
        }
    } else {
        t123 r124 = {.tag =r106.tag, .Error =r106.Error};
        SysState* r125 = r124.Error;
        
        r107 = r125;
    }
    return r107;
}
struct unit_t unit;
#include <adt_platform.c>
t13 wordarray_create_0(t11 args)
{
    SysState* h = args.p1;
    u32 size = args.p2;
    t13 ret;
    WordArray_u32* array = ret.Success.p2;
    
    array = malloc(sizeof(*array));
    if (array == NULL) {
        ret.tag = TAG_ENUM_Error;
        ret.Error = h;
    } else {
        array->values = calloc(size, sizeof(*array->values));
        if (array->values == NULL) {
            free(array);
            ret.tag = TAG_ENUM_Error;
            ret.Error = h;
        } else {
            array->len = size;
            ret.tag = TAG_ENUM_Success;
            ret.Success.p1 = h;
            ret.Success.p2 = array;
        }
    }
    return ret;
}
SysState* wordarray_free_0(t12 args)
{
    WordArray_u32* array = args.p2;
    
    if (array->values) {
        free(array->values);
    }
    free(array);
    return args.p1;
}
#include <adt.h>
static inline u16 u8_to_u16(u8 x)
{
    return (u16) x;
}
static inline u32 u8_to_u32(u8 x)
{
    return (u32) x;
}
static inline u64 u8_to_u64(u8 x)
{
    return (u64) x;
}
static inline u8 u16_to_u8(u16 x)
{
    return (u8) x;
}
static inline u32 u16_to_u32(u16 x)
{
    return (u32) x;
}
static inline u8 u32_to_u8(u32 x)
{
    return (u8) x;
}
static inline u16 u32_to_u16(u32 x)
{
    return (u16) x;
}
static inline u64 u32_to_u64(u32 x)
{
    return (u64) x;
}
static inline u32 u64_to_u32(u64 x)
{
    return (u32) x;
}
static inline unit_t test_stack_probe(unit_t arg)
{
    return arg;
}
u32 wordarray_get_0(t2 args)
{
    if (args.p2 >= args.p1->len) {
        return 0;
    }
    return args.p1->values[args.p2];
}
t4 wordarray_put_0(t3 args)
{
    t4 ret;
    
    if (args.idx >= args.arr->len) {
        ret.tag = TAG_ENUM_Error;
        ret.Error = args.arr;
    } else {
        args.arr->values[args.idx] = args.val;
        ret.tag = TAG_ENUM_Success;
        ret.Success = args.arr;
    }
    return ret;
}
bool_t wordarray_cmp(wordarray_cmp_arg args)
{
    WordArray_u8* a = args.p1;
    WordArray_u8* b = args.p2;
    bool_t ret;
    int i;
    
    if (a->len != b->len) {
        ret.boolean = 0;
        return ret;
    }
    for (i = 0; i < a->len; i++) {
        if (a->values[i] != b->values[i]) {
            ret.boolean = 0;
            return ret;
        }
    }
    ret.boolean = 1;
    return ret;
}
int main(void)
{
    dispatch_t126(FUN_ENUM_caller, 0);
    return 0;
}


