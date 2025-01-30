/******************************************************************************
 * Top contributors (to current version):
 *   Martin Brain, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */
#include "theory/fp/theory_fp_utils.h"

#include "smt/logic_exception.h"

namespace cvc5::internal {
namespace theory {
namespace fp {
namespace utils {

Integer getCardinality(const TypeNode& type)
{
  Assert(type.getKind() == Kind::FLOATINGPOINT_TYPE);

  FloatingPointSize fps = type.getConst<FloatingPointSize>();

  /*
   * 1                    NaN
   * 2*1                  Infinities
   * 2*1                  Zeros
   * 2*2^(s-1)            Subnormal
   * 2*((2^e)-2)*2^(s-1)  Normal
   *
   *  = 1 + 2*2 + 2*((2^e)-1)*2^(s-1)
   *  =       5 + ((2^e)-1)*2^s
   */

  return Integer(5)
         + Integer(2).pow(fps.significandWidth())
               * (Integer(2).pow(fps.exponentWidth()) - Integer(1));
}

void checkForExperimentalFloatingPointType(const Node& n)
{
  TypeNode type = n.getType();
  if (type.isFloatingPoint())
  {
    uint32_t exp_sz = type.getFloatingPointExponentSize();
    uint32_t sig_sz = type.getFloatingPointSignificandSize();
    if (!((exp_sz == 8 && sig_sz == 24) || (exp_sz == 11 && sig_sz == 53)))
    {
      std::stringstream ss;
      ss << "FP term " << n << " with type whose size is " << exp_sz << "/"
         << sig_sz
         << " is not supported, only Float32 (8/24) or Float64 (11/53) types "
            "are supported in default mode. Try the experimental solver via "
            "--fp-exp. Note: There are known issues with the experimental "
            "solver, use at your own risk.";
      throw LogicException(ss.str());
    }
  }
}

}  // namespace utils
}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal
