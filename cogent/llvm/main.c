#include <stdlib.h>

typedef struct {
  char a;
  char b;
} arg;

extern char foo( arg * );


int main(){
  arg * a = malloc(sizeof(arg));
  a->a = 1;
  a->b = 2;
  char res = foo(a);
  free(a);
  return res;
}
