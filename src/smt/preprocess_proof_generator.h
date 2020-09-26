/*********************                                                        */
/*! \file preprocess_proof_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for proofs for preprocessing in an SMT engine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__PREPROCESS_PROOF_GENERATOR_H
#define CVC4__SMT__PREPROCESS_PROOF_GENERATOR_H

#include <map>

#include "expr/proof_generator.h"
#include "expr/proof_node_manager.h"
#include "theory/trust_node.h"

namespace CVC4 {
namespace smt {

/**
 * A proof generator storing proofs of preprocessing. This has two main
 * interfaces during solving:
 * (1) notifyNewAssert, for assertions that are not part of the input and are
 * added by preprocessing passes,
 * (2) notifyPreprocessed, which is called when a preprocessing pass rewrites
 * an assertion into another.
 * Notice that input assertions do not need to be provided to this class.
 *
 * Its getProofFor method produces a proof for a preprocessed assertion
 * whose free assumptions are intended to be input assertions, which are
 * implictly all assertions that are not notified to this class.
 */
class PreprocessProofGenerator : public ProofGenerator
{
 public:
  PreprocessProofGenerator(ProofNodeManager* pnm);
  ~PreprocessProofGenerator() {}
  /**
   * Notify that n is a new assertion, where pg can provide a proof of n.
   */
  void notifyNewAssert(Node n, ProofGenerator* pg);
  /**
   * Notify that n was replaced by np due to preprocessing, where pg can
   * provide a proof of the equality n=np.
   */
  void notifyPreprocessed(Node n, Node np, ProofGenerator* pg);
  /**
   * Get proof for f, which returns a proof based on proving an equality based
   * on transitivity of preprocessing steps, and then using the original
   * assertion with EQ_RESOLVE to obtain the proof of the ending assertion f.
   */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Identify */
  std::string identify() const override;

 private:
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /**
   * The trust node that was the source of each node constructed during
   * preprocessing. For each n, d_src[n] is a trust node whose node is n. This
   * can either be:
   * (1) A trust node REWRITE proving (n_src = n) for some n_src, or
   * (2) A trust node LEMMA proving n.
   */
  std::map<Node, theory::TrustNode> d_src;
};

}  // namespace smt
}  // namespace CVC4

#endif
