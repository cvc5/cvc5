/*********************                                                        */
/*! \file inference.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Inference enumeration for non-linear arithmetic.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__NL__INFER_INFO_H
#define CVC4__THEORY__ARITH__NL__INFER_INFO_H

#include <map>
#include <vector>

#include "util/safe_print.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

/**
 * Types of inferences used in the procedure
 */
enum class Inference : uint32_t
{
  //-------------------- core
  // simple congruence x=y => f(x)=f(y)
  CONGRUENCE,
  // shared term value split (for naive theory combination)
  SHARED_TERM_VALUE_SPLIT,
  //-------------------- incremental linearization solver
  // splitting on zero (NlSolver::checkSplitZero)
  SPLIT_ZERO,
  // based on sign (NlSolver::checkMonomialSign)
  SIGN,
  // based on comparing (abs) model values (NlSolver::checkMonomialMagnitude)
  COMPARISON,
  // based on inferring bounds (NlSolver::checkMonomialInferBounds)
  INFER_BOUNDS,
  // same as above, for inferences that introduce new terms
  INFER_BOUNDS_NT,
  // factoring (NlSolver::checkFactoring)
  FACTOR,
  // resolution bound inferences (NlSolver::checkMonomialInferResBounds)
  RES_INFER_BOUNDS,
  // tangent planes (NlSolver::checkTangentPlanes)
  TANGENT_PLANE,
  //-------------------- transcendental solver
  // purification of arguments to transcendental functions
  T_PURIFY_ARG,
  // initial refinement (TranscendentalSolver::checkTranscendentalInitialRefine)
  T_INIT_REFINE,
  // pi bounds
  T_PI_BOUND,
  // monotonicity (TranscendentalSolver::checkTranscendentalMonotonic)
  T_MONOTONICITY,
  // tangent refinement (TranscendentalSolver::checkTranscendentalTangentPlanes)
  T_TANGENT,
  // secant refinement, the dual of the above inference
  T_SECANT,
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
const char* toString(Inference i);

/**
 * Writes an inference name to a stream.
 *
 * @param out The stream to write to
 * @param i The inference to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, Inference i);

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__NL__INFER_INFO_H */
