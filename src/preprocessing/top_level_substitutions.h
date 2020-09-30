/*********************                                                        */
/*! \file top_level_substitutions.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Mathias Preiner, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Top-level substitutions
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__TOP_LEVEL_SUBSTITUTIONS_H
#define CVC4__PREPROCESSING__TOP_LEVEL_SUBSTITUTIONS_H

#include "context/context.h"
#include "expr/proof_node_manager.h"
#include "expr/term_conversion_proof_generator.h"
#include "theory/substitutions.h"
#include "theory/trust_node.h"

namespace CVC4 {
namespace preprocessing {

/**
 * Stores a substitution corresponding to a set of equalities that have been
 * inferred from the input at the top level, e.g. the substitution holds
 * globally.
 */
class TopLevelSubstitutions
{
 public:
  TopLevelSubstitutions(context::UserContext* u, ProofNodeManager* pnm);
  /** Gets a reference to the top-level substitution map */
  theory::SubstitutionMap& get();
  /**
   * Add substitution x -> t, where pg can provide a closed proof of (= x t)
   * in the remainder of this user context.
   */
  void addSubstitution(TNode x, TNode t, ProofGenerator* pg = nullptr);
  /**
   * Apply substitutions in this class to node n. Returns a trust node
   * proving n = n*sigma, where the proof generator is this class (when
   * proofs are enabled).
   */
  theory::TrustNode apply(Node n);

 private:
  /** The top level substitutions */
  theory::SubstitutionMap d_subs;
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** The term conversion proof generator */
  std::unique_ptr<TConvProofGenerator> d_subsPg;
};

}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__TOP_LEVEL_SUBSTITUTIONS_H */
