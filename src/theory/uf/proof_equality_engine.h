/*********************                                                        */
/*! \file proof_equality_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The proof-producing equality engine
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__UF__PROOF_EQUALITY_ENGINE_H
#define CVC4__THEORY__UF__PROOF_EQUALITY_ENGINE_H

#include <map>
#include <vector>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "expr/proof.h"
#include "expr/proof_node.h"
#include "expr/proof_node_manager.h"
#include "theory/proof_generator.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace eq {

/**
 * A layer on top of an EqualityEngine. The goal of this class is manage the
 * use of an EqualityEngine object in such a way that the proper proofs are
 * internally constructed, and can be retrieved from this class when
 * necessary.
 *
 * It tracks the reason for why all facts are added to an EqualityEngine in a
 * SAT-context dependent manner in a context-dependent (CDProof) object.
 *
 * It is an eager proof generator (see theory/proof_generator.h), in that
 * it stores (copies) of proofs for lemmas when it is required to do so.
 *
 * A theory that is proof producing and uses the equality engine may use this
 * class to manage proofs that are justified by its underlying equality engine.
 */
class ProofEqEngine : public EagerProofGenerator
{
  typedef context::CDHashMap<Node, std::shared_ptr<ProofNode>, NodeHashFunction>
      NodeProofMap;

 public:
  ProofEqEngine(context::Context* c,
                context::UserContext* u,
                EqualityEngine& ee,
                ProofNodeManager* pnm,
                bool pfEnabled = true);
  ~ProofEqEngine() {}
  /** Assert predicate lit by assumption */
  bool assertAssume(Node lit);
  /**
   * Assert the predicate lit by proof step id, given explanation exp and
   * (optionally) arguments args.
   *
   */
  bool assertFact(Node lit, PfRule id, const std::vector<Node>& exp);
  bool assertFact(Node lit,
                  PfRule id,
                  const std::vector<Node>& exp,
                  const std::vector<Node>& args);
  /**
   * Get proven lemma from contradictory facts. This method is called when
   * the proof rule with premises exp and arguments args implies a contradiction
   * by proof rule id.
   *
   * This method returns the corresponding conflict resulting from adding this
   * step, and ensures that a proof has been stored internally so that this
   * class may respond to a call to ProofGenerator::getProof(...).
   */
  TrustNode assertConflict(PfRule id, const std::vector<Node>& exp);
  TrustNode assertConflict(PfRule id,
                            const std::vector<Node>& exp,
                            const std::vector<Node>& args);

 protected:
  /**
   * Make proof for fact lit, or nullptr if it does not exist. It must be the
   * case that lit was either:
   * (1) Passed as the first argument to either a variant of assertAssume or
   * assertFact in the current SAT context,
   * (2) lit is false and a call was made to assertConflict in the current SAT
   * context.
   */
  std::shared_ptr<ProofNode> mkProofForFact(Node lit) const;
  /** Assert internal */
  void assertInternal(Node pred, bool polarity, TNode reason);
  /**
   * Make the conjunction of nodes in a. Returns true if a is empty, and a
   * single literal if a has size 1.
   */
  Node mkAnd(const std::vector<Node>& a);
  Node mkAnd(const std::vector<TNode>& a);

 private:
  /** Reference to the equality engine */
  eq::EqualityEngine& d_ee;
  /** common nodes */
  Node d_true;
  Node d_false;
  /** The SAT-context-dependent proof object */
  CDProof d_proof;
  /**
   * The keep set of this class. This set is maintained to ensure that
   * facts and their explanations are reference counted. Since facts and their
   * explanations are SAT-context-dependent, this set is also
   * SAT-context-dependent.
   */
  NodeSet d_keep;
  /**
   * Whether proofs are enabled. If this flag is false, then this class acts
   * as a simplified interface to the EqualityEngine, without proofs.
   */
  bool d_pfEnabled;
  /** Explain
   *
   * This adds to assumps the set of facts that were asserted to this
   * class in the current SAT context by calls to assertAssume that are
   * required for showing lit.
   *
   * This additionally registers the equality proof steps required to
   * regress the explanation of lit.
   */
  void explainWithProof(Node lit, std::vector<TNode>& assumps);
};

}  // namespace eq
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__PROOF_MANAGER_H */
