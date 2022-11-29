#include <gmpxx.h>

#if __GNU_MP_RELEASE < 60100
#error "GMP version too old (version >= 6.1 required)"
#endif

int main()
{
  mpz_class i = 0;
  return 0;
}
