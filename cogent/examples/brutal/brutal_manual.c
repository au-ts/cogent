// This file is manually written. It tries to match exactly the same language interface
// between Cogent and C.

// Simplifications made:
// 1. Multiple arguments to functions are allowed
// 2. Not using bool_t type in cogent-defns.h
// 3. Using NULLable pointer instead of variant type
// 4. Using break in a for-loop


#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <cogent-defns.h>

typedef void *SysState;

// *****************************************************************
//   Cogent part.
// *****************************************************************

struct get_block_ret {
  SysState *p1;
  char *p2;
};
typedef struct get_block_ret get_block_ret_t;

struct Stuff {
  u32 a;
  u32 b;
  u32 c;
};
typedef struct Stuff Stuff_t;

struct Entry {
  u32 len;
  Stuff_t stuff;
  char* name;
};
typedef struct Entry Entry_t;


get_block_ret_t get_block (SysState);
Entry_t *get_entry_at_offset (char*, u64);
int is_entry (char*, Entry_t*);
int cstring_cmp(char*, char*);
Stuff_t *stuff_ptr(Entry_t *);


struct findStuff_ret {
  SysState *p1;
  Stuff_t *p2;
};
typedef struct findStuff_ret findStuff_ret_t;

findStuff_ret_t findStuff (SysState *sys, char *name) {
  get_block_ret_t ret_block = get_block(sys);
  sys = ret_block.p1;
  char *blk = ret_block.p2;

  u64 offset = 0;
  for (;;) {
    Entry_t *e = get_entry_at_offset (blk, offset);
    if (e->len == 0 || !is_entry(blk, e))
      break;

    if (cstring_cmp(name, e->name))
      return (findStuff_ret_t){ .p1 = sys, .p2 = stuff_ptr(e) };
    offset = offset + e->len;
  }
  return (findStuff_ret_t){ .p1 = sys, .p2 = NULL};
}


// *****************************************************************
//   Below is the same as the main.ac file, with minor difference.
// *****************************************************************


#define SIZE 4096


char block[SIZE]; // Contains Entry's jammed together; terminated by
                  // len==0.


get_block_ret_t get_block (SysState args) {
  return (get_block_ret_t){ .p1 = args, .p2 = block };
}

Entry_t *get_entry_at_offset (char *block, u64 offset) {
  return (Entry_t*)((uintptr_t)block + offset);
}

int is_entry (char *block, Entry_t *e) {
  return ((uintptr_t)e - (uintptr_t)block) < SIZE;
}

int cstring_cmp(char *s1, char *s2) {
  return !strcmp(s1, s2);
}

Stuff_t *stuff_ptr(Entry_t *e) {
  return &e->stuff;
}

int in_range(Entry_t *e, unsigned long nlen) {
  unsigned long p;

  p = (uintptr_t)e + offsetof(Entry_t, name) + nlen;

  return (p - (uintptr_t)block) < SIZE;
}

/* Initialise our block of entries. */
/* Not translated into Cogent. */
void init(void) {
  FILE *fp;
  Entry_t *e;
  int a, b, c, len;
  char buf[80];

  memset(block, 0, SIZE);

  if ((fp = fopen("entries.txt", "r")) != NULL) {
    e = (Entry_t *)block;
    while (fscanf(fp, "%s%d%d%d\n", buf, &a, &b, &c) == 4) {
      len = strlen(buf)+1;
      if (!in_range(e, len)) {
        break;
      }
      // Point to the next location 
      e->name = (char*)((uintptr_t)e + offsetof(Entry_t, name) + sizeof(char*));
      strcpy(e->name, buf);
      e->stuff.a = a;
      e->stuff.b = b;
      e->stuff.c = c;
      e->len = ((uintptr_t)e->name + len) - (uintptr_t)e;
      e = (Entry_t *) ((uintptr_t)e + e->len);
    }
    fclose(fp);
  }
}

int main(void){
  struct findStuff_ret ret;
  init();
  char *str = {"wombat"};
  ret = findStuff(NULL, str);
  if (ret.p2) {
    printf("Wombat's b is %d.\n", ret.p2->b);
  } else {
    printf("Wombat was not found.\n");
  }
  return 0;
}


