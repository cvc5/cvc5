/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Trust substitutions.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__TRUST_SUBSTITUTIONS_H
#define CVC5__THEORY__TRUST_SUBSTITUTIONS_H

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "proof/conv_proof_generator.h"
#include "proof/eager_proof_generator.h"
#include "proof/lazy_proof.h"
#include "proof/proof_node_manager.h"
#include "proof/proof_set.h"
#include "proof/theory_proof_step_buffer.h"
#include "proof/trust_node.h"
#include "theory/substitutions.h"

namespace cvc5::internal {
namespace theory {

/**
 * A layer on top of SubstitutionMap that tracks proofs.
 */
class TrustSubstitutionMap : protected EnvObj, public ProofGenerator
{
  using NodeUIntMap = context::CDHashMap<Node, size_t>;

 public:
  TrustSubstitutionMap(Env& env,
                       context::Context* c,
                       std::string name = "TrustSubstitutionMap",
                       PfRule trustId = PfRule::PREPROCESS_LEMMA,
                       MethodId ids = MethodId::SB_DEFAULT);
  /** Gets a reference to the underlying substitution map */
  SubstitutionMap& get();
  /**
   * Add substitution x -> t, where pg can provide a closed proof of (= x t)
   * in the remainder of this user context.
   */
  void addSubstitution(TNode x, TNode t, ProofGenerator* pg = nullptr);
  /**
   * Add substitution x -> t from a single proof step with rule id, no children
   * and arguments args.
   */
  void addSubstitution(TNode x,
                       TNode t,
                       PfRule id,
                       const std::vector<Node>& children,
                       const std::vector<Node>& args);
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
   *
   * @return The proof generator that can prove (= x t).
   */
  ProofGenerator* addSubstitutionSolved(TNode x, TNode t, TrustNode tn);
  /**
   * Add substitutions from trust substitution map t. This adds all
   * substitutions from the map t and carries over its information about proofs.
   */
  void addSubstitutions(TrustSubstitutionMap& t);
  /**
   * Apply substitutions in this class to node n. Returns a trust node
   * proving n = n*sigma, where the proof generator is provided by this class
   * (when proofs are enabled). If a non-null rewriter is provided, the result
   * of the substitution is rewritten.
   */
  TrustNode applyTrusted(Node n, Rewriter* r = nullptr);
  /** Same as above, without proofs */
  Node apply(Node n, Rewriter* r = nullptr);

  /** Get the proof for formula f */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Identify */
  std::string identify() const override;

 private:
  /** Are proofs enabled? */
  bool isProofEnabled() const;
  /**
   * Get the substitution up to index
   */
  Node getSubstitution(size_t index);
  /** The context used here */
  context::Context* d_ctx;
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
  /**
   * A context-dependent list of LazyCDProof, allocated for internal steps.
   */
  std::unique_ptr<CDProofSet<LazyCDProof>> d_helperPf;
  /** Name for debugging */
  std::string d_name;
  /**
   * The placeholder trusted PfRule identifier for calls to addSubstitution
   * that are not given proof generators.
   */
  PfRule d_trustId;
  /** The method id for which form of substitution to apply */
  MethodId d_ids;
  /**
   * Map from solved equalities to the size of d_tsubs at the time they
   * were concluded. Notice this is required so that we can reconstruct
   * proofs for substitutions after they have become invalidated by later
   * calls to addSubstitution. For example, if we call:
   *   addSubstitution x -> y
   *   addSubstitution z -> w
   *   apply f(x), returns f(y)
   *   addSubstitution y -> w
   * We map (= (f x) (f y)) to index 2, since we only should apply the first
   * two substitutions but not the third when asked to prove this equality.
   */
  NodeUIntMap d_eqtIndex;
  /** Debugging, catches potential for infinite loops */
  std::unordered_set<Node> d_proving;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__TRUST_SUBSTITUTIONS_H */
