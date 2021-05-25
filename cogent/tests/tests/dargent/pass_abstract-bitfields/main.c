
#include <stdio.h>
#include <stdlib.h>

#include <cogent-defns.h>

typedef u8 U2;
typedef u8 U4;


u8 u2_to_u8 (U2 x) {
  return x;
}

u8 u4_to_u8 (U4 x) {
  return x;
}

U2 u8_to_u2 (u8 x) {
  return (x & 0x03);
}

U4 u8_to_u4 (u8 x) {
  return (x & 0x0F);
}

struct R {
  char f1 : 1;
  char f2 : 2;
  char    : 1;
  char f3 : 4;
};

typedef struct R R;

R* foo (R* r) {
  if (r->f1) {
    r->f3 &= 0x0c;
  }
  else {
    r->f2 ++;
  }
  return r;
}


int main () {
  // sizeof(unsigned int) == 4
  unsigned int* x1 = malloc (sizeof (unsigned int));
  unsigned int* x2 = malloc (sizeof (unsigned int));
  *x1 = 0x6E;
  *x2 = 0xBD;
  foo ((R*)x1);
  foo ((R*)x2);
  printf("(0x6E) x1 = 0x%X; (0xBD) x2 = 0x%X\n", *x1, *x2);
  return 0;
}
