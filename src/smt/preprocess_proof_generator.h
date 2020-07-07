/*********************                                                        */
/*! \file preprocess_proof_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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

class PreprocessProofGenerator : public ProofGenerator
{
 public:
  PreprocessProofGenerator(ProofNodeManager * pnm);
  ~PreprocessProofGenerator(){}
  /** 
   * Notify that n is a new assertion, where pg can provide a proof of n.
   */
  void notifyNewAssert(Node n, ProofGenerator * pg);
  /** 
   * Notify that n was replaced by np due to preprocessing, where pg can
   * provide a proof of the equality n=np.
   */
  void notifyPreprocessed(Node n, Node np, ProofGenerator * pg);
  /** Get proof for */
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
   * (1) A trust node REWRITE proving (n_src = n), or
   * (2) A trust node LEMMA proving n.
   */
  std::map<Node, theory::TrustNode > d_src;
};
  
}  // namespace smt
}  // namespace CVC4

#endif
