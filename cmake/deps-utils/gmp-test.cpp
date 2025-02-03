/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for required GMP version.
 */
#include <gmpxx.h>

#if __GNU_MP_RELEASE < 60100
#error "GMP version too old (version >= 6.1 required)"
#endif

int main()
{
  mpz_class i = 0;
  return 0;
}
