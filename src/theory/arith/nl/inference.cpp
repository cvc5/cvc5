/*********************                                                        */
/*! \file inference.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inference enumeration.
 **/

#include "theory/arith/nl/inference.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

const char* toString(Inference i)
{
  switch (i)
  {
    case Inference::CONGRUENCE: return "CONGRUENCE";
    case Inference::SHARED_TERM_VALUE_SPLIT: return "SHARED_TERM_VALUE_SPLIT";
    case Inference::SPLIT_ZERO: return "SPLIT_ZERO";
    case Inference::SIGN: return "SIGN";
    case Inference::COMPARISON: return "COMPARISON";
    case Inference::INFER_BOUNDS: return "INFER_BOUNDS";
    case Inference::INFER_BOUNDS_NT: return "INFER_BOUNDS_NT";
    case Inference::FACTOR: return "FACTOR";
    case Inference::RES_INFER_BOUNDS: return "RES_INFER_BOUNDS";
    case Inference::TANGENT_PLANE: return "TANGENT_PLANE";
    case Inference::T_PURIFY_ARG: return "T_PURIFY_ARG";
    case Inference::T_INIT_REFINE: return "T_INIT_REFINE";
    case Inference::T_PI_BOUND: return "T_PI_BOUND";
    case Inference::T_MONOTONICITY: return "T_MONOTONICITY";
    case Inference::T_SECANT: return "T_SECANT";
    case Inference::T_TANGENT: return "T_TANGENT";
    case Inference::IAND_INIT_REFINE: return "IAND_INIT_REFINE";
    case Inference::IAND_VALUE_REFINE: return "IAND_VALUE_REFINE";
    case Inference::CAD_CONFLICT: return "CAD_CONFLICT";
    case Inference::CAD_EXCLUDED_INTERVAL: return "CAD_EXCLUDED_INTERVAL";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, Inference i)
{
  out << toString(i);
  return out;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
