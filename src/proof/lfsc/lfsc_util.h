/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for LFSC proofs.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__LFSC__LFSC_UTIL_H
#define CVC5__PROOF__LFSC__LFSC_UTIL_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "proof/proof_letify.h"

namespace cvc5::internal {
namespace proof {

/**
 * LFSC rules. The enum below contains all rules that don't correspond to a
 * PfRule, e.g. congruence in LFSC does not have the same form as congruence
 * in the internal calculus.
 */
enum class LfscRule : uint32_t
{
  //----------- translated rules

  // We defined LFSC versions for rules that either don't exist in the internal
  // calculus, or have a different set of arugments/children.

  // an ASSUME corresponding to a function definition in the input SMT query
  DEFINITION,
  // scope has a different structure, e.g. uses lambdas
  SCOPE,
  // must distinguish equalities and disequalities
  NEG_SYMM,
  // congruence is done via a higher-order variant of congruence
  CONG,
  // we use unrolled binary versions of and intro
  AND_INTRO1,
  AND_INTRO2,
  // needed as a helper for SCOPE
  NOT_AND_REV,
  PROCESS_SCOPE,
  // arithmetic
  ARITH_SUM_UB,
  // sequences uses a different form of the concat conflict rule which takes
  // an explicit disequality
  CONCAT_CONFLICT_DEQ,

  // form of quantifier rules varies from internal calculus
  INSTANTIATE,
  SKOLEMIZE,
  BETA_REDUCE,

  // a lambda with argument
  LAMBDA,
  // a proof-let "plet"
  PLET,
  //----------- unknown
  UNKNOWN,
};

/**
 * Converts a lfsc rule to a string. Note: This function is also used in
 * `safe_print()`. Changing this function name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param id The lfsc rule
 * @return The name of the lfsc rule
 */
const char* toString(LfscRule id);

/**
 * Writes a lfsc rule name to a stream.
 *
 * @param out The stream to write to
 * @param id The lfsc rule to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, LfscRule id);
/** Get LFSC rule from a node */
LfscRule getLfscRule(Node n);
/** Get LFSC rule from a node, return true if success and store in lr */
bool getLfscRule(Node n, LfscRule& lr);
/** Make node for LFSC rule */
Node mkLfscRuleNode(LfscRule r);

/** Helper class used for letifying LFSC proofs. */
class LfscProofLetifyTraverseCallback : public ProofLetifyTraverseCallback
{
 public:
  bool shouldTraverse(const ProofNode* pn) override;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
