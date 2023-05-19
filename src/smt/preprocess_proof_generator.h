/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for proofs for preprocessing in an SMT engine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PREPROCESS_PROOF_GENERATOR_H
#define CVC5__SMT__PREPROCESS_PROOF_GENERATOR_H

#include "context/cdhashmap.h"
#include "proof/lazy_proof.h"
#include "proof/proof.h"
#include "proof/proof_generator.h"
#include "proof/proof_set.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class LazyCDProof;
class ProofNodeManager;

namespace smt {

/**
 * This is a proof generator that manages proofs for a set of formulas that
 * may be replaced over time. This set of formulas is implicit; formulas that
 * are not notified as assertions to this class are treated as assumptions.
 *
 * The main use case of this proof generator is for proofs of preprocessing,
 * although it can be used in other scenarios where proofs for an evolving set
 * of formulas is maintained. In the remainder of the description here, we
 * describe its role as a proof generator for proofs of preprocessing.
 *
 * This class has two main interfaces during solving:
 * (1) notifyNewAssert, for assertions that are not part of the input and are
 * added to the assertion pipeline by preprocessing passes,
 * (2) notifyPreprocessed, which is called when a preprocessing pass rewrites
 * an assertion into another.
 * Notice that input assertions do not need to be provided to this class.
 *
 * Its getProofFor method produces a proof for a preprocessed assertion
 * whose free assumptions are intended to be input assertions, which are
 * implictly all assertions that are not notified to this class.
 */
class PreprocessProofGenerator : protected EnvObj, public ProofGenerator
{
  typedef context::CDHashMap<Node, TrustNode> NodeTrustNodeMap;

 public:
  /**
   * @param env Reference to the environment
   * @param c The context this class depends on
   * @param name The name of this generator (for debugging)
   * @param ra The proof rule to use when no generator is provided for new
   * assertions
   * @param rpp The proof rule to use when no generator is provided for
   * preprocessing steps.
   */
  PreprocessProofGenerator(Env& env,
                           context::Context* c = nullptr,
                           std::string name = "PreprocessProofGenerator",
                           PfRule ra = PfRule::PREPROCESS_LEMMA,
                           PfRule rpp = PfRule::PREPROCESS);
  ~PreprocessProofGenerator() {}
  /**
   * Notify that n is an input (its proof is ASSUME).
   */
  void notifyInput(Node n);
  /**
   * Notify that n is a new assertion, where pg can provide a proof of n.
   */
  void notifyNewAssert(Node n, ProofGenerator* pg);
  /**  Notify a new assertion, trust node version. */
  void notifyNewTrustedAssert(TrustNode tn);
  /**
   * Notify that n was replaced by np due to preprocessing, where pg can
   * provide a proof of the equality n=np.
   */
  void notifyPreprocessed(Node n, Node np, ProofGenerator* pg);
  /** Notify preprocessed, trust node version */
  void notifyTrustedPreprocessed(TrustNode tnp);
  /**
   * Get proof for f, which returns a proof based on proving an equality based
   * on transitivity of preprocessing steps, and then using the original
   * assertion with EQ_RESOLVE to obtain the proof of the ending assertion f.
   */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Identify */
  std::string identify() const override;
  /**
   * Allocate a helper proof. This returns a fresh lazy proof object that
   * remains alive in the context. This feature is used to construct
   * helper proofs for preprocessing, e.g. to support the skeleton of proofs
   * that connect AssertionPipeline::conjoin steps.
   */
  LazyCDProof* allocateHelperProof();

 private:
  /**
   * Possibly check pedantic failure for null proof generator provided
   * to this class.
   */
  void checkEagerPedantic(PfRule r);
  /** A dummy context used by this class if none is provided */
  context::Context d_context;
  /** The context used here */
  context::Context* d_ctx;
  /**
   * The trust node that was the source of each node constructed during
   * preprocessing. For each n, d_src[n] is a trust node whose node is n. This
   * can either be:
   * (1) A trust node REWRITE proving (n_src = n) for some n_src, or
   * (2) A trust node LEMMA proving n.
   */
  NodeTrustNodeMap d_src;
  /** A context-dependent list of LazyCDProof, allocated for conjoin steps */
  CDProofSet<LazyCDProof> d_helperProofs;
  /**
   * A cd proof for input assertions, this is an empty proof that intentionally
   * returns (ASSUME f) for all f.
   */
  CDProof d_inputPf;
  /** Name for debugging */
  std::string d_name;
  /** The trust rule for new assertions with no provided proof generator */
  PfRule d_ra;
  /** The trust rule for rewrites with no provided proof generator */
  PfRule d_rpp;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
