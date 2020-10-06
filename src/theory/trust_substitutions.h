/*********************                                                        */
/*! \file trust_substitutions.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
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

#include "context/context.h"
#include "expr/proof_node_manager.h"
#include "theory/substitutions.h"
#include "theory/trust_node.h"

namespace CVC4 {
namespace theory {

/**
 * A layer on top of SubstitutionMap that tracks proofs.
 */
class TrustSubstitutionMap
{
 public:
  TrustSubstitutionMap(context::Context* c, ProofNodeManager* pnm);
  /** Gets a reference to the underlying substitution map */
  SubstitutionMap& get();
  /**
   * Add substitution x -> t, where pg can provide a closed proof of (= x t)
   * in the remainder of this user context.
   */
  void addSubstitution(TNode x, TNode t, ProofGenerator* pg = nullptr);
  /**
   * Add substitution x -> t, which was derived from the proven field of
   * trust node tn. In other words, (= x t) is the solved form of
   * tn.getProven(). This method is a helper function for methods (e.g.
   * ppAssert) that put literals into solved form. It should be the case
   * that (= x t) and tn.getProven() can be shown equivalent by rewriting.
   *
   * This ensures that we add a substitution with a proof
   * based on transforming the tn.getProven() to (= x t) if tn has a
   * non-null proof generator; otherwise if tn has no proof generator
   * we simply add the substitution.
   */
  void addSubstitutionSolved(TNode x, TNode t, TrustNode tn);
  /**
   * Apply substitutions in this class to node n. Returns a trust node
   * proving n = n*sigma, where the proof generator is provided by this class
   * (when proofs are enabled).
   */
  TrustNode apply(Node n, bool doRewrite = true);

 private:
  /** Are proofs enabled? */
  bool isProofEnabled() const;
  /** The substitution map */
  SubstitutionMap d_subs;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__TRUST_SUBSTITUTIONS_H */
