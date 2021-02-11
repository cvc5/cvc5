/*********************                                                        */
/*! \file inference_id.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Gereon Kremer, Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Inference enumeration.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__INFERENCE_ID_H
#define CVC4__THEORY__INFERENCE_ID_H

#include <map>
#include <vector>

#include "util/safe_print.h"

namespace CVC4 {
namespace theory {

/**
 * Types of inferences used in the procedure
 */
enum class InferenceId
{
  //-------------------- core
  // simple congruence x=y => f(x)=f(y)
  ARITH_NL_CONGRUENCE,
  // shared term value split (for naive theory combination)
  ARITH_NL_SHARED_TERM_VALUE_SPLIT,
  //-------------------- incremental linearization solver
  // splitting on zero (NlSolver::checkSplitZero)
  ARITH_NL_SPLIT_ZERO,
  // based on sign (NlSolver::checkMonomialSign)
  ARITH_NL_SIGN,
  // based on comparing (abs) model values (NlSolver::checkMonomialMagnitude)
  ARITH_NL_COMPARISON,
  // based on inferring bounds (NlSolver::checkMonomialInferBounds)
  ARITH_NL_INFER_BOUNDS,
  // same as above, for inferences that introduce new terms
  ARITH_NL_INFER_BOUNDS_NT,
  // factoring (NlSolver::checkFactoring)
  ARITH_NL_FACTOR,
  // resolution bound inferences (NlSolver::checkMonomialInferResBounds)
  ARITH_NL_RES_INFER_BOUNDS,
  // tangent planes (NlSolver::checkTangentPlanes)
  ARITH_NL_TANGENT_PLANE,
  //-------------------- transcendental solver
  // purification of arguments to transcendental functions
  ARITH_NL_T_PURIFY_ARG,
  // initial refinement (TranscendentalSolver::checkTranscendentalInitialRefine)
  ARITH_NL_T_INIT_REFINE,
  // pi bounds
  ARITH_NL_T_PI_BOUND,
  // monotonicity (TranscendentalSolver::checkTranscendentalMonotonic)
  ARITH_NL_T_MONOTONICITY,
  // tangent refinement (TranscendentalSolver::checkTranscendentalTangentPlanes)
  ARITH_NL_T_TANGENT,
  // secant refinement, the dual of the above inference
  ARITH_NL_T_SECANT,
  //-------------------- iand solver
  // initial refinements (IAndSolver::checkInitialRefine)
  ARITH_NL_IAND_INIT_REFINE,
  // value refinements (IAndSolver::checkFullRefine)
  ARITH_NL_IAND_VALUE_REFINE,
  // sum refinements (IAndSolver::checkFullRefine)
  ARITH_NL_IAND_SUM_REFINE,
  // bitwise refinements (IAndSolver::checkFullRefine)
  ARITH_NL_IAND_BITWISE_REFINE,
  //-------------------- cad solver
  // conflict / infeasible subset obtained from cad
  ARITH_NL_CAD_CONFLICT,
  // excludes an interval for a single variable
  ARITH_NL_CAD_EXCLUDED_INTERVAL,
  //-------------------- icp solver
  // conflict obtained from icp
  ARITH_NL_ICP_CONFLICT,
  // propagation / contraction of variable bounds from icp
  ARITH_NL_ICP_PROPAGATION,
  //-------------------- unknown


  BAG_NON_NEGATIVE_COUNT,
  BAG_MK_BAG_SAME_ELEMENT,
  BAG_MK_BAG,
  BAG_EQUALITY,
  BAG_DISEQUALITY,
  BAG_EMPTY,
  BAG_UNION_DISJOINT,
  BAG_UNION_MAX,
  BAG_INTERSECTION_MIN,
  BAG_DIFFERENCE_SUBTRACT,
  BAG_DIFFERENCE_REMOVE,
  BAG_DUPLICATE_REMOVAL,

  UNKNOWN,
};

/**
 * Converts an inference to a string. Note: This function is also used in
 * `safe_print()`. Changing this functions name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param i The inference
 * @return The name of the inference
 */
const char* toString(InferenceId i);

/**
 * Writes an inference name to a stream.
 *
 * @param out The stream to write to
 * @param i The inference to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, InferenceId i);

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__INFERENCE_H */
