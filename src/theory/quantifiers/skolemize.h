/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for skolemization.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SKOLEMIZE_H
#define CVC5__THEORY__QUANTIFIERS__SKOLEMIZE_H

#include <unordered_map>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "expr/type_node.h"
#include "proof/eager_proof_generator.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class DTypeConstructor;

namespace theory {
namespace quantifiers {

class QuantifiersState;
class TermRegistry;

/** Skolemization utility
 *
 * This class constructs Skolemization lemmas.
 * Given a quantified formula q = (forall x. P),
 * its skolemization lemma is of the form:
 *   (~ forall x. P ) => ~P * { x -> d_skolem_constants[q] }
 *
 * This class also incorporates techniques for
 * skolemization with "inductive strenghtening", see
 * Section 2 of Reynolds et al., "Induction for SMT
 * Solvers", VMCAI 2015. In the case that x is an inductive
 * datatype or an integer, then we may strengthen the conclusion
 * based on weak well-founded induction. For example, for
 * quantification on lists, a skolemization with inductive
 * strengthening is a lemma of this form:
 *   (~ forall x : List. P( x ) ) =>
 *   ~P( k ) ^ ( is-cons( k ) => P( tail( k ) ) )
 * For the integers it is:
 *   (~ forall x : Int. P( x ) ) =>
 *   ~P( k ) ^ ( x>0 => P( x-1 ) )
 *
 *
 * Inductive strenghtening is not enabled by
 * default and can be enabled by option:
 *   --quant-ind
 */
class Skolemize : protected EnvObj
{
  typedef context::CDHashMap<Node, Node> NodeNodeMap;

 public:
  Skolemize(Env& env, QuantifiersState& qs, TermRegistry& tr);
  ~Skolemize() {}
  /** skolemize quantified formula q
   * If the return value ret of this function is non-null, then ret is a trust
   * node corresponding to a new skolemization lemma we generated for q. These
   * lemmas are constructed once per user-context.
   */
  TrustNode process(Node q);
  /** get the skolem constants */
  static std::vector<Node> getSkolemConstants(const Node& q);
  /** get the i^th skolem constant for quantified formula q */
  static Node getSkolemConstant(const Node& q, size_t i);
  /** make skolemized body
   *
   * This returns the skolemized body n of a
   * quantified formula q with inductive strenghtening,
   * where typically n is q[1].
   *
   * The skolem constants/functions we generate by this
   * skolemization are added to sk.
   *
   * The argument fvs are used if we are
   * performing skolemization within a nested quantified
   * formula. In this case, skolem constants we introduce
   * must be parameterized based on the types of fvs and must be
   * applied to fvs.
   *
   * The last two arguments sub and sub_vars are used for
   * to carry the body and indices of other induction
   * variables if a quantified formula to skolemize
   * has multiple induction variables. See page 5
   * of Reynolds et al., VMCAI 2015.
   */
  static Node mkSkolemizedBodyInduction(const Options& opts,
                                        Node q,
                                        Node n,
                                        std::vector<TNode>& fvs,
                                        std::vector<Node>& sk,
                                        Node& sub,
                                        std::vector<unsigned>& sub_vars);
  /** get skolem constants for quantified formula q */
  bool getSkolemConstantsInduction(Node q, std::vector<Node>& skolems);
  /** get the skolemized body for quantified formula q
   *
   * For example, if q is forall x. P( x ), this returns the formula P( k ) for
   * a fresh Skolem constant k.
   */
  Node getSkolemizedBodyInduction(Node q);
  /** is n a variable that we can apply inductive strenghtening to? */
  static bool isInductionTerm(const Options& opts, Node n);
  /**
   * Get skolemization vectors, where for each quantified formula that was
   * skolemized, this is the list of skolems that were used to witness the
   * negation of that quantified formula (which is equivalent to an existential
   * one).
   *
   * This is used for the command line option
   *   --dump-instantiations
   * which prints an informal justification of steps taken by the quantifiers
   * module.
   */
  void getSkolemTermVectors(std::map<Node, std::vector<Node> >& sks) const;

 private:
  /** Are proofs enabled? */
  bool isProofEnabled() const;
  /** get self selectors
   * For datatype constructor dtc with type dt,
   * this collects the set of datatype selector applications,
   * applied to term n, whose return type in ntn, and stores
   * them in the vector selfSel.
   */
  static void getSelfSel(const DType& dt,
                         const DTypeConstructor& dc,
                         Node n,
                         TypeNode ntn,
                         std::vector<Node>& selfSel);
  /** Reference to the quantifiers state */
  QuantifiersState& d_qstate;
  /** Reference to the term registry */
  TermRegistry& d_treg;
  /** quantified formulas that have been skolemized */
  NodeNodeMap d_skolemized;
  /** map from quantified formulas to the list of skolem constants */
  std::unordered_map<Node, std::vector<Node>> d_skolem_constants;
  /** map from quantified formulas to their skolemized body */
  std::unordered_map<Node, Node> d_skolem_body;
  /** Eager proof generator for skolemization lemmas */
  std::unique_ptr<EagerProofGenerator> d_epg;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__SKOLEMIZE_H */
