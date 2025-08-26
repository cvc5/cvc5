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
 * Rewrite proof generator utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__REWRITE_PROOF_GENERATOR_H
#define CVC5__PROOF__REWRITE_PROOF_GENERATOR_H

#include "proof/method_id.h"
#include "proof/proof_generator.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class ProofNode;
class ProofNodeManager;

/**
 * This class is used as a (lazy) proof generator for macro rewrite steps
 * (e.g. proof rule MACRO_SR_EQ_INTRO). Its getProofFor method is assumed to
 * always prove equalities by rewrites for the given method id.
 */
class RewriteProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  /**
   * @param env Reference to the environment
   * @param id The method id, which determines the method of rewriting this
   * proof generator proves equalites for.
   */
  RewriteProofGenerator(Env& env, MethodId id = MethodId::RW_REWRITE);
  virtual ~RewriteProofGenerator();
  /**
   * Get proof for fact. It should be that fact is an equality of the form
   * t = t', where t' is d_env.rewriteViaMethod(t, d_id).
   * If this is not the case, nullptr is returned and an assertion is thrown
   * in debug mode.
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** identify */
  std::string identify() const override;

 private:
  /** The method id */
  MethodId d_id;
  /** Proof args */
  std::vector<Node> d_pargs;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__REWRITE_PROOF_GENERATOR_H */
