/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The status of a rewrite rule proof reconstruction attempt
 */

#include "cvc5_public.h"

#ifndef CVC5__REWRITER__REWRITE_PROOF_STATUS__H
#define CVC5__REWRITER__REWRITE_PROOF_STATUS__H

#include "expr/node.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * Identifiers for the status of a DSL proof reconstruction goal.
 */
enum class RewriteProofStatus : uint32_t
{
  FAIL = 0,
  // The following rules can be generated temporarily during reconstruction.
  // We convert them into ProofRule during proof finalization.
  REFL,
  EVAL,
  TRANS,
  CONG,
  CONG_EVAL,
  TRUE_ELIM,
  TRUE_INTRO,
  ARITH_POLY_NORM,
  ACI_NORM,
  ABSORB,
  FLATTEN,
  // we have a DSL proof rule that proves this goal.
  DSL,
  // obtained by >1 applications of a DSL fixed point rule
  DSL_FIXED_POINT,
  // we have a THEORY_REWRITE that proves this goal.
  THEORY_REWRITE
};

/**
 * Converts a rewrite proof status to a string.
 * @param s The rewrite proof status
 * @return The name of the rewrite proof status
 */
const char* toString(RewriteProofStatus s);
/**
 * Writes a rewrite proof status to a stream.
 *
 * @param out The stream to write to
 * @param s The rewrite proof status to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, RewriteProofStatus s);

}  // namespace rewriter
}  // namespace cvc5::internal

#endif
