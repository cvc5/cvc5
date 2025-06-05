/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Martin Brain
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Operator elimination for arithmetic.
 */

#pragma once

#include <map>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "expr/skolem_manager.h"
#include "proof/proof_generator.h"
#include "smt/env_obj.h"
#include "theory/logic_info.h"
#include "theory/skolem_lemma.h"

namespace cvc5::internal {

class TConvProofGenerator;

namespace theory {
namespace arith {

class OperatorElim : protected EnvObj, public ProofGenerator
{
 public:
  OperatorElim(Env& env);
  ~OperatorElim() {}
  /** Eliminate operators in this term.
   *
   * Eliminate operators in term n. If n has top symbol that is not a core
   * one (including division, int division, mod, to_int, is_int, syntactic sugar
   * transcendental functions), then we replace it by a form that eliminates
   * that operator. This may involve the introduction of witness terms.
   *
   * @param n The node to eliminate
   * @param lems The lemmas that we wish to add concerning n. It is the
   * responsbility of the caller to process these lemmas.
   * @param partialOnly Whether we only want to eliminate partial operators.
   * @return the trust node of kind REWRITE encapsulating the eliminated form
   * of n and a proof generator for proving this equivalence.
   */
  TrustNode eliminate(Node n,
                      std::vector<SkolemLemma>& lems,
                      bool partialOnly = false);
  /**
   * Get axiom for term n. This returns the axiom that this class uses to
   * eliminate the term n, which is determined by its top-most symbol.
   */
  static Node getAxiomFor(NodeManager* nm, const Node& n);
  /**
   * Get proof for formula f, which should have been generated as a lemma
   * via eliminate above, or as a rewrite performed by eliminate.
   */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Identify this, for proof generator interface */
  std::string identify() const override;

 private:
  /**
   * Function symbols used to implement:
   * (1) Uninterpreted division-by-zero semantics.  Needed to deal with partial
   * division function ("/"),
   * (2) Uninterpreted int-division-by-zero semantics.  Needed to deal with
   * partial function "div",
   * (3) Uninterpreted mod-zero semantics.  Needed to deal with partial
   * function "mod".
   *
   * If the option arithNoPartialFun() is enabled, then the range of this map
   * stores Skolem constants instead of Skolem functions, meaning that the
   * function-ness of e.g. division by zero is ignored.
   *
   * Note that this cache is used only for performance reasons. Conceptually,
   * these skolem functions actually live in SkolemManager.
   */
  std::map<SkolemId, Node> d_arithSkolem;
  /**
   * Map from the lemmas we sent to the term that they were introduced for.
   * This is tracked only for proofs.
   */
  context::CDHashMap<Node, Node> d_lemmaMap;
  /**
   * Eliminate operators in term n. If n has top symbol that is not a core
   * one (including division, int division, mod, to_int, is_int, syntactic sugar
   * transcendental functions), then we replace it by a form that eliminates
   * that operator. This may involve the introduction of witness terms.
   *
   * One exception to the above rule is that we may leave certain applications
   * like (/ 4 1) unchanged, since replacing this by 4 changes its type from
   * real to int. This is important for some subtyping issues during
   * expandDefinition. Moreover, applications like this can be eliminated
   * trivially later by rewriting.
   *
   * This method is called both during expandDefinition and during ppRewrite.
   *
   * @param nm Pointer to the node manager
   * @param n The node to eliminate operators from.
   * @param lems The lemmas storing (L, k) where L is the lemma and k is the 
   * attached skolem it is associated with.
   * @param partialOnly Whether we are only eliminating partial operators.
   * @param wasNonLinear Set to true if n requires a non-linear logic.
   * @return The (single step) eliminated form of n.
   */
  static Node eliminateOperators(NodeManager* nm,
                                 Node n,
                                 std::vector<std::pair<Node, Node>>& lems,
                                 bool partialOnly,
                                 bool& wasNonLinear);
  /**
   * Get the skolem lemma for lem, based on whether we are proof producing.
   * A skolem lemma is a wrapper around lem that also tracks its associated
   * skolem k.
   *
   * @param lem The lemma that axiomatizes the behavior of k
   * @param k The skolem
   * @param n The term we introduced the skolem for
   * @return the skolem lemma corresponding to lem, annotated with k.
   */
  SkolemLemma mkSkolemLemma(const Node& lem, const Node& k, const Node& n);
  /** get arithmetic skolem application
   *
   * By default, this returns the term f( n ), where f is the Skolem function
   * for the identifier asi.
   */
  static Node getArithSkolemApp(NodeManager* nm, Node n, SkolemId asi);
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
