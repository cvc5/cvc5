/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Incremental approximation scheme for pi.
 */

#include "theory/arith/nl/transcendental/approximate_pi.h"

#include "base/check.h"

namespace cvc5 {
namespace internal {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

ApproximatePi::ApproximatePi()
{
  for (uint64_t i = 0; i < s_initial_refinement; ++i)
  {
    refine();
  }
}

void ApproximatePi::refine()
{
  Assert(d_next_k < 1 << 28);

  Integer k(d_next_k);

  Integer num = Integer(120) * k.pow(2) + Integer(151) * k + Integer(47);
  Integer den = Integer(512) * k.pow(4) + Integer(1024) * k.pow(3)
                + Integer(712) * k.pow(2) + Integer(194) * k + Integer(15);
  den = den.multiplyByPow2(d_next_k * 4);

  Rational summand(num, den);

  d_lower += summand;
  d_upper =
      d_lower + Rational(Integer(1), Integer(1).multiplyByPow2(d_next_k * 4));

  ++d_next_k;
}

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace internal
}  // namespace cvc5
