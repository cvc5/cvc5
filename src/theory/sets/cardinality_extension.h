/*********************                                                        */
/*! \file cardinality_extension.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An extension of the theory sets for handling cardinality constraints
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SETS__CARDINALITY_EXTENSION_H
#define CVC4__THEORY__SETS__CARDINALITY_EXTENSION_H

#include "context/cdhashset.h"
#include "context/context.h"
#include "theory/sets/inference_manager.h"
#include "theory/sets/solver_state.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace sets {

class TheorySetsPrivate;

/** 
 * This class implements a variant of the procedure from Bansal et al, IJCAR
 * 2016. It is used during a full effort check in the following way:
 *    reset(); { registerTerm(n,lemmas); | n in CardTerms }  check();
 * where CardTerms is the set of all applications of CARD in the current
 * context.
 * 
 * The remaining methods are used for model construction. 
 * 
 * This variant of the procedure takes inspiration from the procedure
 * for word equations in Liang et al, CAV 2014. In that procedure, "normal
 * forms" are generated for String terms by recursively expanding
 * concatentations modulo equality. This procedure similarly maintains
 * normal forms, where the normal form for Set terms is a set of Venn regions.
 */
class CardinalityExtension
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
 public:
  /**
   * Constructs a new instance of the cardinality solver w.r.t. the provided
   * contexts.
   */
  CardinalityExtension(TheorySetsPrivate& p,
                       SolverState& s,
                       InferenceManager& im,
                       eq::EqualityEngine& e,
                       context::Context* c,
                       context::UserContext* u);

  ~CardinalityExtension() {}
  /** reset
   * 
   * Called at the beginning of a full effort check. This resets the data
   * structures used by this class during a full effort check.
   */
  void reset();
  /** register term
   * 
   * Register that the term n exists in the current context, where n is an
   * application of CARD.
   */
  void registerTerm(Node n);
  /** check
   * 
   * Invoke a full effort check of the cardinality solver. At a high level,
   * this asserts inferences via the inference manager object d_im. If no
   * inferences are made, then the current set of assertions is satisfied
   * with respect to constraints involving set cardinality.
   * 
   * This method applies various inference schemas in succession until an
   * inference is made. These inference schemas are given in the private
   * methods of this class (e.g. checkMinCard, checkCardBuildGraph, etc.).
   */
  void check();
  /** Is model value basic?
   *   
   * This returns true if equivalence class eqc is a "leaf" in the cardinality
   * graph. In this case, its model value is simply 
   */
  bool isModelValueBasic(Node eqc);
  /** get model elements
   *
   * This method updates els so that it is the set of elements that occur in eqc
   * in the model we are building. Notice that els may already have elements 
   * in it (from explicit memberships from the base set solver for leaf nodes
   * of the cardinality graph). This method is used during the collectModelInfo
   * method of theory of sets.
   * 
   * The argument mvals maps set equivalence classes to their model values. 
   * Due to our model construction algorithm, it can be assumed that all
   * sets in the normal form of eqc occur in the domain of mvals by the order
   * in which sets are assigned.
   */
  void mkModelValueElementsFor(Node eqc,
                               std::vector<Node>& els,
                               const std::map<Node, Node>& mvals);
  /** get ordered sets equivalence classes
   *
   * Get the ordered set of equivalence classes computed by this class. This
   * ordering ensures the invariant mentioned above mkModelValueElementsFor.
   * 
   * This ordering ensures that all children of a node in the cardinality
   * graph computed by this class occur before it in this list.
   */
  const std::vector<Node>& getOrderedSetsEqClasses() { return d_oSetEqc; }

 private:
  /** constants */
  Node d_zero;
  /** the empty vector */
  std::vector<Node> d_emp_exp;
  /** the theory of sets which owns this */
  TheorySetsPrivate& d_parent;
  /** Reference to the state object for the theory of sets */
  SolverState& d_state;
  /** Reference to the inference manager for the theory of sets */
  InferenceManager& d_im;
  /** Reference to the equality engine of theory of sets */
  eq::EqualityEngine& d_ee;
  /** register cardinality term
   * 
   * This method add nodes to lemmas corresponding to the definition of
   * the cardinality of set term n. For example, if n is A^B (denoting set
   * intersection as ^), then we consider the lemmas card(A^B)>=0,
   * card(A) = card(A\B) + card(A^B) and card(B) = card(B\A) + card(A^B). 
   * 
   * The exact form of this lemma is modified such that proxy variables are
   * introduced for set terms as needed (see SolverState::getProxy).
   */
  void registerCardinalityTerm(Node n, std::vector<Node>& lemmas);
  /** check register
   * 
   * This ensures that all (non-redundant, relevant) non-variable set terms in
   * the current context have been passed to registerCardinalityTerm. In other
   * words, this ensures that the cardinality graph for these terms can be
   * constructed since the cardinality relationships for these terms have been
   * elaborated as lemmas.
   * 
   * Notice a term is redundant in a context if it is congruent to another
   * term; it is not relevant if no cardinality constraints exist for its type.
   */
  void checkRegister(std::vector<Node>& lemmas);
  /** check minimum cardinality
   * 
   * This adds lemmas to the argument of the method of the form
   *   distinct(x1,...,xn) ^ member(x1,S) ^ ... ^ member(xn,S) => card(S) >= n
   * This lemma enforces the rules GUESS_LOWER_BOUND and PROPAGATE_MIN_SIZE
   * from Bansal et. al IJCAR 2016.
   * 
   * Notice that member(x1,S) is implied to hold in the current context. This
   * means that it may be the case that member(x,T) ^ T = S are asserted
   * literals. Furthermore, x1, ..., xn reside in distinct equivalence classes
   * but are not necessarily entailed to be distinct.
   */
  void checkMinCard(std::vector<Node>& lemmas);
  /** check cardinality cycles
   * 
   * The purpose of this inference schema is 
   * 
   * TODO
   * 
   * This method is inspired by the checkCycles inference schema in the theory
   * of strings.
   */
  void checkCardCycles(std::vector<Node>& lemmas);
  /** 
   * 
   * TODO
   */
  void checkCardCyclesRec(Node eqc,
                          std::vector<Node>& curr,
                          std::vector<Node>& exp,
                          std::vector<Node>& lemmas);
  /** check normal forms
   * 
   * This method attempts to assign "normal forms" to all set equivalence
   * classes whose types have cardinality constraints. Normal forms are
   * defined recursively.
   * 
   * A "normal form" of an equivalence class E is a set of Venn regions
   * { S1, ..., Sn } where the "flat form" of each non-variable set T in E
   * is e
   * 
   * A "flat form" of a set term T
   * 
   * TODO
   * 
   * The argument intro_sets is updated to contain the set of new set terms that
   * the procedure is requesting to introduce for the purpose of forcing the
   * flat forms of two equivalent sets to become identical.
   */
  void checkNormalForms(std::vector<Node>& intro_sets);
  /** 
   * Called for each equivalence class, in order of d_oSetEqc, by the above
   * function.
   */
  void checkNormalForm(Node eqc, std::vector<Node>& intro_sets);
  /** element types of sets for which cardinality is enabled */
  std::map<TypeNode, bool> d_t_card_enabled;
  /** 
   * This maps equivalence classes r to an application of cardinality of the
   * form card( t ), where t = r holds in the current context.
   */
  std::map<Node, Node> d_eqc_to_card_term;
  /** 
   * User-context-dependent set of set terms for which we have called
   * registerCardinalityTerm on.
   */
  NodeSet d_card_processed;
  /** the ordered set of equivalence classes, see checkCardCycles */
  std::vector<Node> d_oSetEqc;
  std::map<Node, std::vector<Node> > d_card_parent;
  std::map<Node, std::map<Node, std::vector<Node> > > d_ff;
  std::map<Node, std::vector<Node> > d_nf;
  /** The local base node map
   * 
   * This maps set terms to the "local base node" of its cardinality graph.
   * The local base node of S is the intersection node that is either S itself
   * or is adjacent to S in the cardinality graph. This maps 
   * 
   * For example, the ( A ^ B ) is the local base of each of the sets (A \ B), 
   * ( A ^ B ), and (B \ A).
   */
  std::map<Node, Node> d_localBase;
}; /* class CardinalityExtension */

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H */
