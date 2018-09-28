#include <stdlib.h>
#include <stdio.h>
#include <time.h>

int main ()
{
  int ret = 0;
  srand(time(NULL));   // should only be called once
  unsigned int s;
  int i = 0;
  for (i; i < 100; i++) {
    s = (unsigned int)rand();
    void *p = malloc (s * sizeof (char));
    if (!p) { ret = 1; printf ("malloc failed!\n"); break; }
    printf ("malloced size of %u\n", s);
    free (p);
  }
  return ret;
}
