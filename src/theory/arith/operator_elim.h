/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Martin Brain, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Operator elimination for arithmetic.
 */

#pragma once

#include <map>

#include "expr/node.h"
#include "expr/skolem_manager.h"
#include "proof/eager_proof_generator.h"
#include "theory/logic_info.h"
#include "theory/skolem_lemma.h"

namespace cvc5 {

class TConvProofGenerator;

namespace theory {
namespace arith {

class OperatorElim : public EagerProofGenerator
{
 public:
  OperatorElim(ProofNodeManager* pnm, const LogicInfo& info);
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
  static Node getAxiomFor(Node n);

 private:
  /** Logic info of the owner of this class */
  const LogicInfo& d_info;
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
  std::map<SkolemFunId, Node> d_arithSkolem;
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
   * @param n The node to eliminate operators from.
   * @return The (single step) eliminated form of n.
   */
  Node eliminateOperators(Node n,
                          std::vector<SkolemLemma>& lems,
                          TConvProofGenerator* tg,
                          bool partialOnly);
  /** get arithmetic skolem
   *
   * Returns the Skolem in the above map for the given id, creating it if it
   * does not already exist.
   */
  Node getArithSkolem(SkolemFunId asi);
  /**
   * Make the witness term, which creates a witness term based on the skolem
   * manager with this class as a proof generator.
   */
  Node mkWitnessTerm(Node v,
                     Node pred,
                     const std::string& prefix,
                     const std::string& comment,
                     std::vector<SkolemLemma>& lems);
  /** get arithmetic skolem application
   *
   * By default, this returns the term f( n ), where f is the Skolem function
   * for the identifier asi.
   *
   * If the option arithNoPartialFun is enabled, this returns f, where f is
   * the Skolem constant for the identifier asi.
   */
  Node getArithSkolemApp(Node n, SkolemFunId asi);

  /**
   * Called when a non-linear term n is given to this class. Throw an exception
   * if the logic is linear.
   */
  void checkNonLinearLogic(Node term);
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
