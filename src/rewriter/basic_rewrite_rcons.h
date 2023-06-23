/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for basic (non-DSL-dependent) automatic reconstructing proofs of
 * THEORY_REWRITE steps.
 */

#include "cvc5_private.h"

#ifndef CVC5__REWRITER__BASIC_REWRITE_RCONS_H
#define CVC5__REWRITER__BASIC_REWRITE_RCONS_H

#include <unordered_set>

#include "expr/node.h"
#include "proof/proof.h"
#include "proof/proof_node_manager.h"
#include "smt/env_obj.h"
#include "theory/builtin/proof_checker.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * The module for basic (non-DSL-dependent) automatic reconstructing proofs of
 * THEORY_REWRITE steps. It handles special cases that are independent
 * of the user-provided DSL rules, including EVALUATE, REFL, BETA_REDUCE.
 */
class BasicRewriteRCons : protected EnvObj
{
 public:
  BasicRewriteRCons(Env& env);
  ~BasicRewriteRCons() {}
  /**
   * Try to prove (= a b), where a ---> b was a theory rewrite from theory
   * tid with the given method. If this method returns true, then a proof
   * of (= a b) was added to cdp.
   */
  bool prove(CDProof* cdp, Node a, Node b, theory::TheoryId tid, MethodId mid);

 private:
  /**
   * Try rule r, return true if eq could be proven by r with arguments args.
   * If this method returns true, a proof of eq was added to cdp.
   */
  bool tryRule(CDProof* cdp, Node eq, PfRule r, const std::vector<Node>& args);
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif
