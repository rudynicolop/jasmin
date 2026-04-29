#include <stdint.h>
#include <stdio.h>

/*
In order to invoke this file properly with [succJazz.jazz]:
- Compile [succJazz.jazz]
- Then run [gcc call_succ.c succJazz.s -o callingSuccJazz]
- Then invoke [./callingSuccJazz]

Zam!
 */

extern uint32_t successor(uint32_t x);

int main(void) {
  printf("%d\n", successor(42));
  return 0;
}
