/*********************                                                        */
/*! \file trust_substitutions.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Mathias Preiner, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Trust substitutions
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__TRUST_SUBSTITUTIONS_H
#define CVC4__THEORY__TRUST_SUBSTITUTIONS_H

#include "context/cdlist.h"
#include "context/context.h"
#include "expr/lazy_proof.h"
#include "expr/proof_node_manager.h"
#include "expr/term_conversion_proof_generator.h"
#include "theory/eager_proof_generator.h"
#include "theory/substitutions.h"
#include "theory/theory_proof_step_buffer.h"
#include "theory/trust_node.h"

namespace CVC4 {
namespace theory {

/**
 * A layer on top of SubstitutionMap that tracks proofs.
 */
class TrustSubstitutionMap
{
 public:
  TrustSubstitutionMap(context::Context* c, ProofNodeManager* pnm, std::string name="TrustSubstitutionMap", PfRule trustId=PfRule::TRUST,
                    MethodId ids = MethodId::SB_DEFAULT);
  /** Gets a reference to the top-level substitution map */
  SubstitutionMap& get();
  /**
   * Add substitution x -> t, where pg can provide a closed proof of (= x t)
   * in the remainder of this user context.
   */
  void addSubstitution(TNode x, TNode t, ProofGenerator* pg = nullptr);
  /**
   * Add substitutions
   */
  void addSubstitutions(TrustSubstitutionMap& t);
  /**
   * Apply substitutions in this class to node n. Returns a trust node
   * proving n = n*sigma, where the proof generator is this class (when
   * proofs are enabled).
   */
  TrustNode apply(Node n, bool doRewrite = true);

 private:
  /** Are proofs enabled? */
  bool isProofEnabled() const;
  /**
   * Get current substitution. This returns a node of the form:
   *   (and (= x1 t1) ... (= xn tn))
   * where (x1, t1) ... (xn, tn) have been registered via addSubstitution above.
   * Moreover, it ensures that d_subsPg has a proof of the returned value.
   */
  Node getCurrentSubstitution();
  /** The substitution map */
  SubstitutionMap d_subs;
  /** A context-dependent list of trust nodes */
  context::CDList<TrustNode> d_tsubs;
  /** Theory proof step buffer */
  std::unique_ptr<TheoryProofStepBuffer> d_tspb;
  /** A lazy proof for substitution steps */
  std::unique_ptr<LazyCDProof> d_subsPg;
  /** A lazy proof for apply steps */
  std::unique_ptr<LazyCDProof> d_applyPg;
  /** Whether the substitution is up-to-date */
  context::CDO<Node> d_currentSubs;
  /** Name for debugging */
  std::string d_name;
  /** 
   * The placeholder trusted PfRule identifier for calls to addSubstitution
   * that are not given proof generators.
   */
  PfRule d_trustId;
  /** The method id for which form of substitution to apply */
  MethodId d_ids;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__TRUST_SUBSTITUTIONS_H */
