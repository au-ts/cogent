#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "pass_array-put.c"

int main() {
  char* arr = (char*) malloc(3 * sizeof (char));
  if (!arr) {
    printf("failed to allocate\n");
    return 1;
  }
  arr[0] = 34;
  arr[1] = 35;
  arr[2] = 36;

  printf ("Initial arr: %u %u %u\n", arr[0], arr[1], arr[2]);
  arr = bar (arr);
  printf ("After bar arr: %u %u %u\n", arr[0], arr[1], arr[2]);
  arr = foo (arr);
  printf ("After foo arr: %u %u %u\n", arr[0], arr[1], arr[2]);

  free (arr);
  return 0;
}
