#include "pass_map2.c"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>


int main ()
{
  t1* arr1 = malloc(4 * sizeof (t1));
  u8* arr2 = malloc (3 * sizeof (char));
  arr1[0] = (t1) {.f1 = 0, .f2 = 0};
  arr1[1] = (t1) {.f1 = 1, .f2 = 1};
  arr1[2] = (t1) {.f1 = 2, .f2 = 0};
  arr1[3] = (t1) {.f1 = 3, .f2 = 1};
  *arr2 = 4;
  *(arr2 + 1) = 5;
  *(arr2 + 2) = 6;
  int i;
  for (i = 0; i != 4; i++) {
    printf("arr1[%d] = {%d, %d};\n", i, arr1[i].f1, arr1[i].f2.boolean);
  }
  for (i = 0; i != 3; i++) {
    printf("arr2[%d] = %d;\n", i, arr2[i]);
  }
  t2* arg_1 = malloc (sizeof (t2));
  *arg_1 = (t2) {.p1 = arr1, .p2 = arr2};
  t3* arg = malloc (sizeof (t3));
  *arg = (t3) {.arrs = *arg_1, .b = 1};
  foo (arg);  // Theoretically, we need to assign the result of `foo(arg)' to
              // a variable, to maintain the functional semantics. In this test,
              // we intentionally don't do it to manifest that it is indeed updated
              // in-place. / zilinc
  printf ("-------------------------------\n");
  for (i = 0; i != 4; i++) {
    printf("arr1[%d] = {%d, %d};\n", i, arr1[i].f1, arr1[i].f2.boolean);
  }
  for (i = 0; i != 3; i++) {
    printf("arr2[%d] = %d;\n", i, arr2[i]);
  }

  for (i = 0; i != 4; i++) {
    printf("arg.arrs.p1[%d] = {%d,_};\n", i, arg->arrs.p1[i].f1);
  }
  for (i = 0; i != 3; i++) {
    printf("arg.arrs.p2[%d] = %d;\n", i, arg->arrs.p2[i]);
  }

  return 0;
}
