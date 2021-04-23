/*********************                                                        */
/*! \file lfsc_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lfsc proof nodes
 **/

#include "cvc5_private.h"

#ifndef CVC4__PROOF__LFSC__LFSC_UTIL_H
#define CVC4__PROOF__LFSC__LFSC_UTIL_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "proof/proof_letify.h"

namespace cvc5 {
namespace proof {

/**
work steps:
1. make new rules in the lfsc signature
2. add to LfscRule enum
3. print in toString
4. convert PfRule to LfscRule in the postprocessor
5. Add printing code to computeProofArgs
*/

/**
 * LFSC rules
 */
enum class LfscRule : uint32_t
{
  //----------- translated rules

  // We defined LFSC versions for rules that either don't exist in the internal
  // calculus, or have a different set of arugments/children.

  // scope has a different structure, e.g. uses lambdas
  SCOPE,
  // must distinguish equalities and disequalities
  NEG_SYMM,
  // congruence is done via a higher-order variant of congruence
  CONG,
  // we use unrolled binary versions of and elim / intro
  AND_ELIM1,
  AND_ELIM2,
  AND_INTRO1,
  AND_INTRO2,
  // needed as a helper for SCOPE
  NOT_AND_REV,
  PROCESS_SCOPE,
  // arithmetic
  ARITH_SUM_UB,

  // form of quantifier rules varies from internal calculus
  INSTANTIATE,
  SKOLEMIZE,

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
LfscRule getLfscRule(Node n);
bool getLfscRule(Node n, LfscRule& lr);
Node mkLfscRuleNode(LfscRule r);

/** Helper class used for letifying LFSC proofs. */
class LfscProofLetifyTraverseCallback : public ProofLetifyTraverseCallback
{
 public:
  bool shouldTraverse(const ProofNode* pn) override;
};

}  // namespace proof
}  // namespace cvc5

#endif
