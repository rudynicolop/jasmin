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

extern void jmemcpy(uint64_t *target, uint64_t *source, uint64_t size);

int main(void) {
  uint64_t source[] = {2, 4, 8, 16, 32, 66, 666, 42};
  uint64_t target[SIZE];
  jmemcpy(target, source, SIZE);

  for (int i = 0; i < SIZE; i++) {
    printf("%lu ", (unsigned long)target[i]);
  }

  return 0;
}
