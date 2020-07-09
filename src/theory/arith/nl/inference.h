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
  CONGRUENCE,
  SPLIT_ZERO,
  SIGN,
  COMPARISON,
  INFER_BOUNDS,
  INFER_BOUNDS_NT,
  FACTOR,
  RES_INFER_BOUNDS,
  TANGENT_PLANE,
  T_PURIFY_ARG,
  T_INIT_REFINE,
  T_PI_BOUND,
  T_MONOTONICITY,
  T_SECANT,
  T_TANGENT,
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
