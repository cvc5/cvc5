/*********************                                                        */
/*! \file inference_id.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inference enumeration.
 **/

#include "theory/arith/inference_id.h"

namespace CVC4 {
namespace theory {
namespace arith {

const char* toString(InferenceId i)
{
  switch (i)
  {
    case InferenceId::NL_CONGRUENCE: return "CONGRUENCE";
    case InferenceId::NL_SHARED_TERM_VALUE_SPLIT: return "SHARED_TERM_VALUE_SPLIT";
    case InferenceId::NL_SPLIT_ZERO: return "SPLIT_ZERO";
    case InferenceId::NL_SIGN: return "SIGN";
    case InferenceId::NL_COMPARISON: return "COMPARISON";
    case InferenceId::NL_INFER_BOUNDS: return "INFER_BOUNDS";
    case InferenceId::NL_INFER_BOUNDS_NT: return "INFER_BOUNDS_NT";
    case InferenceId::NL_FACTOR: return "FACTOR";
    case InferenceId::NL_RES_INFER_BOUNDS: return "RES_INFER_BOUNDS";
    case InferenceId::NL_TANGENT_PLANE: return "TANGENT_PLANE";
    case InferenceId::NL_T_PURIFY_ARG: return "T_PURIFY_ARG";
    case InferenceId::NL_T_INIT_REFINE: return "T_INIT_REFINE";
    case InferenceId::NL_T_PI_BOUND: return "T_PI_BOUND";
    case InferenceId::NL_T_MONOTONICITY: return "T_MONOTONICITY";
    case InferenceId::NL_T_SECANT: return "T_SECANT";
    case InferenceId::NL_T_TANGENT: return "T_TANGENT";
    case InferenceId::NL_IAND_INIT_REFINE: return "IAND_INIT_REFINE";
    case InferenceId::NL_IAND_VALUE_REFINE: return "IAND_VALUE_REFINE";
    case InferenceId::NL_CAD_CONFLICT: return "CAD_CONFLICT";
    case InferenceId::NL_CAD_EXCLUDED_INTERVAL: return "CAD_EXCLUDED_INTERVAL";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, InferenceId i)
{
  out << toString(i);
  return out;
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
