/*********************                                                        */
/*! \file inference_id.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer, Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inference enumeration.
 **/

#include "theory/inference_id.h"

namespace CVC4 {
namespace theory {

const char* toString(InferenceId i)
{
  switch (i)
  {
    case InferenceId::ARITH_NL_CONGRUENCE: return "CONGRUENCE";
    case InferenceId::ARITH_NL_SHARED_TERM_VALUE_SPLIT: return "SHARED_TERM_VALUE_SPLIT";
    case InferenceId::ARITH_NL_SPLIT_ZERO: return "SPLIT_ZERO";
    case InferenceId::ARITH_NL_SIGN: return "SIGN";
    case InferenceId::ARITH_NL_COMPARISON: return "COMPARISON";
    case InferenceId::ARITH_NL_INFER_BOUNDS: return "INFER_BOUNDS";
    case InferenceId::ARITH_NL_INFER_BOUNDS_NT: return "INFER_BOUNDS_NT";
    case InferenceId::ARITH_NL_FACTOR: return "FACTOR";
    case InferenceId::ARITH_NL_RES_INFER_BOUNDS: return "RES_INFER_BOUNDS";
    case InferenceId::ARITH_NL_TANGENT_PLANE: return "TANGENT_PLANE";
    case InferenceId::ARITH_NL_T_PURIFY_ARG: return "T_PURIFY_ARG";
    case InferenceId::ARITH_NL_T_INIT_REFINE: return "T_INIT_REFINE";
    case InferenceId::ARITH_NL_T_PI_BOUND: return "T_PI_BOUND";
    case InferenceId::ARITH_NL_T_MONOTONICITY: return "T_MONOTONICITY";
    case InferenceId::ARITH_NL_T_SECANT: return "T_SECANT";
    case InferenceId::ARITH_NL_T_TANGENT: return "T_TANGENT";
    case InferenceId::ARITH_NL_IAND_INIT_REFINE: return "IAND_INIT_REFINE";
    case InferenceId::ARITH_NL_IAND_VALUE_REFINE: return "IAND_VALUE_REFINE";
    case InferenceId::ARITH_NL_IAND_SUM_REFINE: return "IAND_SUM_REFINE";
    case InferenceId::ARITH_NL_IAND_BITWISE_REFINE: return "IAND_BITWISE_REFINE";
    case InferenceId::ARITH_NL_CAD_CONFLICT: return "CAD_CONFLICT";
    case InferenceId::ARITH_NL_CAD_EXCLUDED_INTERVAL: return "CAD_EXCLUDED_INTERVAL";
    case InferenceId::ARITH_NL_ICP_CONFLICT: return "ICP_CONFLICT";
    case InferenceId::ARITH_NL_ICP_PROPAGATION: return "ICP_PROPAGATION";
    case Inference::BAG_NON_NEGATIVE_COUNT: return "BAG_NON_NEGATIVE_COUNT";
    case Inference::BAG_MK_BAG_SAME_ELEMENT: return "BAG_MK_BAG_SAME_ELEMENT";
    case InferenceId::BAG_MK_BAG: return "BAG_MK_BAG";
    case InferenceId::BAG_EQUALITY: return "BAG_EQUALITY";
    case InferenceId::BAG_DISEQUALITY: return "BAG_DISEQUALITY";
    case InferenceId::BAG_EMPTY: return "BAG_EMPTY";
    case InferenceId::BAG_UNION_DISJOINT: return "BAG_UNION_DISJOINT";
    case InferenceId::BAG_UNION_MAX: return "BAG_UNION_MAX";
    case InferenceId::BAG_INTERSECTION_MIN: return "BAG_INTERSECTION_MIN";
    case InferenceId::BAG_DIFFERENCE_SUBTRACT: return "BAG_DIFFERENCE_SUBTRACT";
    case InferenceId::BAG_DIFFERENCE_REMOVE: return "BAG_DIFFERENCE_REMOVE";
    case InferenceId::BAG_DUPLICATE_REMOVAL: return "BAG_DUPLICATE_REMOVAL";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, InferenceId i)
{
  out << toString(i);
  return out;
}

}  // namespace theory
}  // namespace CVC4
