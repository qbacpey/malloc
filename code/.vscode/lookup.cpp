#include <cstdio>

#define B2(n) n, n + 1, n + 1, n + 2
#define B4(n) B2(n), B2(n + 1), B2(n + 1), B2(n + 2)
#define B6(n) B4(n), B4(n + 1), B4(n + 1), B4(n + 2)

unsigned int lookuptable[64] = {B4(0), B4(1), B4(1), B4(2)};

int main() {
  for (int i = 0; i != 64; i++) {
    printf("%d, ", lookuptable[i]);
  }
  return 0;
}