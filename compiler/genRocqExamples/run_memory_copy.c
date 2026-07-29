#include <stdint.h>
#include <stdio.h>

/*
In order to invoke this file properly with [memory_copy.jazz]:
- Compile [memory_copy.jazz] via [./jasminc -o memory_copy.s memory_copy.jazz]
- Then run [gcc run_memory_copy.c memory_copy.s -o runMemoryCopy]
- Then invoke [./runMemoryCopy]

Zam!
 */

const int SIZE = 8;

/* In Jasmin, we just copy 32-bit words, not caring about the sign.
   Here in C, we can pretend that the values are singned 32-bit integers! */
extern void jmemcpy(int32_t *target, int32_t *source, int64_t size);

int main(void) {
  int32_t source[] = {2, -4, -8, 16, -32, 66, 666, -42};
  int32_t target[SIZE];
  jmemcpy(target, source, SIZE);

  for (int i = 0; i < SIZE; i++) {
    printf("%d ", target[i]);
  }

  return 0;
}
