#include <string.h>

int foo () {
  int a[1000];
  int b[1000];
  

  int i = 0;
  int s = 0;
  for (i; i < 1000; i++) {
    b[i] = a[i];
    s += b[i];
  }

  return s;
}

int bar () {
  int a[1000];
  int b[1000];

  int s = 0;
  memcpy (b, a, 1000);
  int i = 0;
  for (i; i < 1000; i++)
    s += b[i];
  return s;
}

int main () {
  int x = 0;
  for (int j = 0; j < 100000; j++)
    x += bar ();
    // foo ();
  return x;
}
