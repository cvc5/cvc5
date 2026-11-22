/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Eliminates higher-order define-fun equalities from CPC proofs.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__EO__EO_DEFINE_FUN_ELIM_H
#define CVC5__PROOF__EO__EO_DEFINE_FUN_ELIM_H

#include <memory>
#include <unordered_map>
#include <unordered_set>

#include "expr/node.h"
#include "proof/proof_node.h"
#include "smt/env_obj.h"
#include "smt/proof_manager.h"

namespace cvc5::internal {
namespace proof {

/**
 * Converts a closed proof whose definitions include higher-order equalities
 * (= f (lambda x t)) into one where each such definition is instead the
 * assumption (forall x (= (f x) t)), and no lambda terms occur.
 *
 * Applications of lambdas are beta-reduced in every term of the proof.
 * The derivations specific to definitions are rewritten:
 * - ASSUME (= f (lambda x t)) becomes ASSUME (forall x (= (f x) t)),
 * - TRANS of the above with CONG over the lambda (rewriting its body) becomes
 *   EQ_RESOLVE with CONG over the quantified formula,
 * - HO_CONG (f a) = ((lambda x t) b) becomes INSTANTIATE (plus CONG/TRANS if
 *   a and b differ),
 * - BETA_REDUCE steps become REFL.
 *
 * If any lambda remains (e.g. f occurs not fully applied), conversion fails
 * and the caller should use the original proof.
 */
class EoDefineFunElim : protected EnvObj
{
 public:
  EoDefineFunElim(Env& env);
  /**
   * @param pf The proof, closed according to psm.
   * @param psm The scope mode.
   * @return the converted proof, or nullptr if conversion was not applicable
   * or failed.
   */
  std::shared_ptr<ProofNode> process(std::shared_ptr<ProofNode> pf,
                                     ProofScopeMode psm);

 private:
  /** Beta-reduce all lambda applications, convert definition equalities */
  Node convert(const Node& n);
  /** Convert proof */
  std::shared_ptr<ProofNode> convertProof(std::shared_ptr<ProofNode> pn);
  /** Convert the proof of a definition (= f (lambda x t)) */
  std::shared_ptr<ProofNode> convertDefProof(std::shared_ptr<ProofNode> pn);
  /**
   * Prove t[as/vars] = t[bs/vars], given proofs of as_i = bs_i, by
   * congruence over the structure of t.
   */
  std::shared_ptr<ProofNode> proveCongSubst(
      const Node& t,
      const std::vector<Node>& vars,
      const std::vector<Node>& as,
      const std::vector<Node>& bs,
      const std::vector<std::shared_ptr<ProofNode>>& pfs,
      std::unordered_map<Node, std::shared_ptr<ProofNode>>& cache);
  /** Is n of the form (= f (lambda x t)) where f is a defined symbol? */
  bool isDefEq(const Node& n) const;
  /** Make node, mark failure if null */
  std::shared_ptr<ProofNode> mk(
      ProofRule r,
      const std::vector<std::shared_ptr<ProofNode>>& children,
      const std::vector<Node>& args,
      const Node& expected);
  /** The defined symbols */
  std::unordered_set<Node> d_defSyms;
  /** Term cache */
  std::unordered_map<Node, Node> d_cache;
  /** Proof cache */
  std::unordered_map<const ProofNode*, std::shared_ptr<ProofNode>> d_pcache;
  /** Whether conversion failed */
  bool d_failed;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
