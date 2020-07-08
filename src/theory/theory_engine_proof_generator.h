/*********************                                                        */
/*! \file theory_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory engine proof generator
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY_ENGINE_PROOF_GENERATOR_H
#define CVC4__THEORY_ENGINE_PROOF_GENERATOR_H

#include <memory>

#include "context/cdhashmap.h"
#include "context/context.h"
#include "expr/lazy_proof.h"
#include "expr/proof_generator.h"
#include "expr/proof_node_manager.h"
#include "theory/trust_node.h"

namespace CVC4 {

/**
 * A simple proof generator class used by the theory engine. This class
 * stores proofs for TheoryEngine::getExplanation.
 *
 * Notice that this class could be made general purpose. Its main feature is
 * storing lazy proofs for facts in a context-dependent manner.
 */
class TheoryEngineProofGenerator : public ProofGenerator
{
  typedef context::
      CDHashMap<Node, std::shared_ptr<LazyCDProof>, NodeHashFunction>
          NodeLazyCDProofMap;

 public:
  TheoryEngineProofGenerator(ProofNodeManager* pnm, context::UserContext* u);
  ~TheoryEngineProofGenerator() {}
  /**
   * Make trust explanation. Called when lpf has a proof of lit from free
   * assumptions in exp.
   *
   * This stores lpf in the map d_proofs below and returns the trust node for
   * this propagation, which has TrustNodeKind TrustNodeKind::PROP_EXP. If this
   * explanation already exists, then the previous explanation is taken, which
   * also suffices for proving the implication.
   */
  theory::TrustNode mkTrustExplain(TNode lit,
                                   Node exp,
                                   std::shared_ptr<LazyCDProof> lpf);
  /**
   * Get proof for, which expects implications corresponding to explained
   * propagations (=> exp lit) registered by the above method. This currently
   * involves calling the mkScope method of ProofNodeManager internally, which
   * returns a closed proof.
   */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Identify this generator (for debugging, etc..) */
  std::string identify() const override;

 private:
  /** The proof manager, used for allocating new ProofNode objects */
  ProofNodeManager* d_pnm;
  /** Map from formulas to lazy CD proofs */
  NodeLazyCDProofMap d_proofs;
};

}  // namespace CVC4

#endif /* CVC4__THEORY_ENGINE_PROOF_GENERATOR_H */
