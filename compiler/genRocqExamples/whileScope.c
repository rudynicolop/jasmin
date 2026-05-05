#include <stdio.h>

int main(void) {
  int local = -1;

  for (int i = 0; i < 5; i++) {
    int local = i;
    printf("local in while: %d\n", local);
  }

  printf("local in while: %d\n", local);

  // Compiler error: error: ‘local’ undeclared (first use in this function)
  /* printf("local after: %p\n", &local); */
}
