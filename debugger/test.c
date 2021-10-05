#include <stdio.h>

int main() {
  /* $VAR: counter */
  
  int i = 0;
  int j = 1;
  /* Hi */
  while (i < 10) {
    printf("i = %d\n", i);
    i++;
  }
  printf("%d\n", j);
  
  return 0;
}