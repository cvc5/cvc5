/*********************                                                        */
/*! \file inference_id.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Inference enumeration for arithmetic.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__INFERENCE_ID_H
#define CVC4__THEORY__ARITH__INFERENCE_ID_H

#include <map>
#include <vector>

#include "util/safe_print.h"

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * Types of inferences used in the procedure
 */
enum class InferenceId : uint32_t
{
  //-------------------- core
  // simple congruence x=y => f(x)=f(y)
  NL_CONGRUENCE,
  // shared term value split (for naive theory combination)
  NL_SHARED_TERM_VALUE_SPLIT,
  //-------------------- incremental linearization solver
  // splitting on zero (NlSolver::checkSplitZero)
  NL_SPLIT_ZERO,
  // based on sign (NlSolver::checkMonomialSign)
  NL_SIGN,
  // based on comparing (abs) model values (NlSolver::checkMonomialMagnitude)
  NL_COMPARISON,
  // based on inferring bounds (NlSolver::checkMonomialInferBounds)
  NL_INFER_BOUNDS,
  // same as above, for inferences that introduce new terms
  NL_INFER_BOUNDS_NT,
  // factoring (NlSolver::checkFactoring)
  NL_FACTOR,
  // resolution bound inferences (NlSolver::checkMonomialInferResBounds)
  NL_RES_INFER_BOUNDS,
  // tangent planes (NlSolver::checkTangentPlanes)
  NL_TANGENT_PLANE,
  //-------------------- transcendental solver
  // purification of arguments to transcendental functions
  NL_T_PURIFY_ARG,
  // initial refinement (TranscendentalSolver::checkTranscendentalInitialRefine)
  NL_T_INIT_REFINE,
  // pi bounds
  NL_T_PI_BOUND,
  // monotonicity (TranscendentalSolver::checkTranscendentalMonotonic)
  NL_T_MONOTONICITY,
  // tangent refinement (TranscendentalSolver::checkTranscendentalTangentPlanes)
  NL_T_TANGENT,
  // secant refinement, the dual of the above inference
  NL_T_SECANT,
  //-------------------- iand solver
  // initial refinements (IAndSolver::checkInitialRefine)
  NL_IAND_INIT_REFINE,
  // value refinements (IAndSolver::checkFullRefine)
  NL_IAND_VALUE_REFINE,
  //-------------------- cad solver
  // conflict / infeasible subset obtained from cad
  NL_CAD_CONFLICT,
  // excludes an interval for a single variable
  NL_CAD_EXCLUDED_INTERVAL,
  //-------------------- icp solver
  // conflict obtained from icp
  NL_ICP_CONFLICT,
  // propagation / contraction of variable bounds from icp
  NL_ICP_PROPAGATION,
  //-------------------- unknown
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

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__INFERENCE_H */
