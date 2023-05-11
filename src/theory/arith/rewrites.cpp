/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inference information utility.
 */

#include "theory/arith/rewrites.h"

#include <iostream>

namespace cvc5::internal {
namespace theory {
namespace arith {

const char* toString(Rewrite r)
{
  switch (r)
  {
    case Rewrite::NONE: return "NONE";
    case Rewrite::CONST_EVAL: return "CONST_EVAL";
    case Rewrite::MOD_TOTAL_BY_CONST: return "MOD_TOTAL_BY_CONST";
    case Rewrite::DIV_TOTAL_BY_CONST: return "DIV_TOTAL_BY_CONST";
    case Rewrite::DIV_MOD_BY_ZERO: return "DIV_MOD_BY_ZERO";
    case Rewrite::MOD_BY_ONE: return "MOD_BY_ONE";
    case Rewrite::DIV_BY_ONE: return "DIV_BY_ONE";
    case Rewrite::DIV_MOD_PULL_NEG_DEN: return "DIV_MOD_PULL_NEG_DEN";
    case Rewrite::MOD_OVER_MOD: return "MOD_OVER_MOD";
    case Rewrite::MOD_CHILD_MOD: return "MOD_CHILD_MOD";
    case Rewrite::DIV_OVER_MOD: return "DIV_OVER_MOD";
    case Rewrite::INT_EXT_CONST: return "INT_EXT_CONST";
    case Rewrite::INT_EXT_INT: return "INT_EXT_INT";
    case Rewrite::INT_EXT_PI: return "INT_EXT_PI";
    case Rewrite::INT_EXT_TO_REAL: return "INT_EXT_TO_REAL";
    case Rewrite::INEQ_BV_TO_NAT_ELIM: return "INEQ_BV_TO_NAT_ELIM";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, Rewrite r)
{
  out << toString(r);
  return out;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
