/******************************************************************************
 * Top contributors (to current version):
 *   Pedro Saccomani
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test that the LibPoly libraries provide the functions used by cvc5 that are
 * not available in older versions. The declarations are given here instead of
 * including the LibPoly headers, since the headers may belong to a different
 * installation than the libraries, which is exactly what this test detects.
 */

#include <cstddef>
#include <vector>

extern "C" {
struct lp_upolynomial_struct;
void lp_upolynomial_signed_remainder_sequence(
    const lp_upolynomial_struct* f,
    const lp_upolynomial_struct* g,
    lp_upolynomial_struct*** S,
    std::size_t* size);
}

namespace poly {
class UPolynomial;
std::vector<UPolynomial> signed_remainder_sequence(const UPolynomial& p,
                                                   const UPolynomial& q);
}  // namespace poly

int main()
{
  // Stored into volatiles so that the references to the functions are not
  // optimized away (a function address is never null, so any check on it is
  // folded), which would make the link succeed even if they are missing.
  void* volatile c =
      reinterpret_cast<void*>(&lp_upolynomial_signed_remainder_sequence);
  void* volatile cxx = reinterpret_cast<void*>(&poly::signed_remainder_sequence);
  (void)c;
  (void)cxx;
  return 0;
}
