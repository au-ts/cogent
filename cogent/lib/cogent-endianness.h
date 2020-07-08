#ifndef __COGENT_ENDIANNESS_H__
#define __COGENT_ENDIANNESS_H__

const int ENDIANNESS_TEST = 1;
#define IS_BIG_ENDIAN (*(char *)&ENDIANNESS_TEST == 0)

u16 swap_u16(u16 v) {
  return (v << 8) | (v >> 8);
}

u32 swap_u32(u32 v) {
  v = ((v << 8) & 0xFF00FF00) | ((v >> 8) & 0xFF00FF);
  return (v << 16) | (v >> 16);
}

u64 swap_u64(u64 v) {
  v = ((v << 8) & 0xFF00FF00FF00FF00) | ((v >> 8) & 0x00FF00FF00FF00FF);
  v = ((v << 16) & 0xFFFF0000FFFF0000) | ((v >> 16) & 0x0000FFFF0000FFFF);
  return (v << 32) | (v >> 32);
}

u16 be_u16(u16 v) {
  return IS_BIG_ENDIAN ? v : swap_u16(v);
}

u32 be_u32(u32 v) {
  return IS_BIG_ENDIAN ? v : swap_u32(v);
}

u64 be_u64(u64 v) {
  return IS_BIG_ENDIAN ? v : swap_u64(v);
}

u16 le_u16(u16 v) {
  return IS_BIG_ENDIAN ? swap_u16(v) : v;
}

u32 le_u32(u32 v) {
  return IS_BIG_ENDIAN ? swap_u32(v) : v;
}

u64 le_u64(u64 v) {
  return IS_BIG_ENDIAN ? swap_u64(v) : v;
}

#endif /* __COGENT_ENDIANNESS_H__ */
