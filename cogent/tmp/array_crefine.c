

int foo (void) {

  int n1 = 3;
  int n2, n3;
  n2 = n1 * 2 + 3;
  n3 = n1 + n2;
  int arr[3] = {n1,n2,n3};

}

int bar (void) {

  int n1 = 3;
  int n2, n3;
  n2 = n1 * 2 + 3;
  n3 = n1 + n2;
  int arr[3];
  arr[0] = n1;
  arr[1] = n2;
  arr[2] = n3;

}


int quux () {
  int q = 0;
  for (int i = 0; i < 3; i++) {
    q = i + 1;
  }
  return q;
}
