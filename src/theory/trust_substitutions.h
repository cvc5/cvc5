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

#include "context/context.h"
#include "expr/proof_node_manager.h"
#include "expr/term_conversion_proof_generator.h"
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
  TrustNode apply(Node n);

 private:
  /** Are proofs enabled? */
  bool isProofEnabled() const;
  /** The substitution map */
  SubstitutionMap d_subs;
  /** The term conversion proof generator */
  std::unique_ptr<TConvProofGenerator> d_subsPg;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__TRUST_SUBSTITUTIONS_H */
