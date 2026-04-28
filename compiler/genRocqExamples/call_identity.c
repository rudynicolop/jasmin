#include <stdint.h>
#include <stdio.h>

extern uint32_t identity(uint32_t x);
/*
In order to invoke this file properly with [identity.jazz]:
- Compile [identity.jazz]
- Then run [gcc call_identity.c identity.s -o callingIdentity]
- Then invoke [./callingIdentity]

Zam!
 */

int main(void) {
  printf("%d\n", identity(42));
  return 0;
}
