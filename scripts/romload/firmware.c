#include <stdio.h>
#include <stdlib.h>

int x1 = 1000;
int x2 = 2000;

void main()
{
  int z;
  x1 = 50;
  x2 = 50;

  printf("hello\n");
  z = (x1 + x2);
  if (z == 100)
    printf("TEST PASSED\n");
  else
    printf("TEST FAILED, z=%d\n", z);
  exit(0);
}

