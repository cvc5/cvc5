/*********************                                                        */
/*! \file cardinality_extension.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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
#include "theory/type_set.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace sets {

/**
 * This class implements a variant of the procedure from Bansal et al, IJCAR
 * 2016. It is used during a full effort check in the following way:
 *    reset(); { registerTerm(n,lemmas); | n in CardTerms }  check();
 * where CardTerms is the set of all applications of CARD in the current
 * context.
 *
 * The remaining public methods are used during model construction, i.e.
 * the collectModelInfo method of the theory of sets.
 *
 * The procedure from Bansal et al IJCAR 2016 introduces the notion of a
 * "cardinality graph", where the nodes of this graph are sets and (directed)
 * edges connect sets to their Venn regions wrt to other sets. For example,
 * if (A \ B) is a term in the current context, then the node A is
 * connected via an edge to child (A \ B). The node (A ^ B) is a child
 * of both A and B. The notion of a cardinality graph is loosely followed
 * in the procedure implemented by this class.
 *
 * The main difference wrt Bansal et al IJCAR 2016 is that the nodes of the
 * cardinality graph considered by this class are not arbitrary set terms, but
 * are instead representatives of equivalence classes. For more details, see
 * documentation of the inference schemas in the private methods of this class.
 *
 * This variant of the procedure takes inspiration from the procedure
 * for word equations in Liang et al, CAV 2014. In that procedure, "normal
 * forms" are generated for String terms by recursively expanding
 * concatentations modulo equality. This procedure similarly maintains
 * normal forms, where the normal form for Set terms is a set of (equivalence
 * class representatives of) Venn regions that do not contain the empty set.
 */
class CardinalityExtension
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  /**
   * Constructs a new instance of the cardinality solver w.r.t. the provided
   * contexts.
   */
  CardinalityExtension(SolverState& s,
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
   * graph.
   */
  bool isModelValueBasic(Node eqc);
  /** get model elements
   *
   * This method updates els so that it is the set of elements that occur in
   * an equivalence class (whose representative is eqc) in the model we are
   * building. Notice that els may already have elements in it (from explicit
   * memberships from the base set solver for leaf nodes of the cardinality
   * graph). This method is used during the collectModelInfo method of theory
   * of sets.
   *
   * The argument v is the Valuation utility of the theory of sets, which is
   * used by this method to query the value assigned to cardinality terms by
   * the theory of arithmetic.
   *
   * The argument mvals maps set equivalence classes to their model values.
   * Due to our model construction algorithm, it can be assumed that all
   * sets in the normal form of eqc occur in the domain of mvals by the order
   * in which sets are assigned.
   */
  void mkModelValueElementsFor(Valuation& v,
                               Node eqc,
                               std::vector<Node>& els,
                               const std::map<Node, Node>& mvals,
                               TheoryModel* model);
  /** get ordered sets equivalence classes
   *
   * Get the ordered set of equivalence classes computed by this class. This
   * ordering ensures the invariant mentioned above mkModelValueElementsFor.
   *
   * This ordering ensures that all children of a node in the cardinality
   * graph computed by this class occur before it in this list.
   */
  const std::vector<Node>& getOrderedSetsEqClasses() { return d_oSetEqc; }

  /**
   * get the slack elements generated for each finite type. This function is
   * called by TheorySetsPrivate::collectModelInfo to ask the TheoryModel to
   * exclude these slack elements from the members in all sets of that type.
   */
  const std::map<TypeNode, std::vector<TNode> >& getFiniteTypeSlackElements()
      const
  {
    return d_finite_type_slack_elements;
  }
  /**
   * get non-slack members in all sets of the given finite type. This function
   * is called by TheorySetsPrivate::collectModelInfo to specify the exclusion
   * sets for TheoryModel
   */
  const std::vector<Node>& getFiniteTypeMembers(TypeNode typeNode);

 private:
  /** constants */
  Node d_true;
  Node d_zero;
  /** the empty vector */
  std::vector<Node> d_emp_exp;
  /** Reference to the state object for the theory of sets */
  SolverState& d_state;
  /** Reference to the inference manager for the theory of sets */
  InferenceManager& d_im;
  /** Reference to the equality engine of theory of sets */
  eq::EqualityEngine& d_ee;
  /** register cardinality term
   *
   * This method add lemmas corresponding to the definition of
   * the cardinality of set term n. For example, if n is A^B (denoting set
   * intersection as ^), then we consider the lemmas card(A^B)>=0,
   * card(A) = card(A\B) + card(A^B) and card(B) = card(B\A) + card(A^B).
   *
   * The exact form of this lemma is modified such that proxy variables are
   * introduced for set terms as needed (see SolverState::getProxy).
   */
  void registerCardinalityTerm(Node n);
  /** check register
   *
   * This ensures that all (non-redundant, relevant) non-variable set terms in
   * the current context have been passed to registerCardinalityTerm. In other
   * words, this ensures that the cardinality graph for these terms can be
   * constructed since the cardinality relationships for these terms have been
   * elaborated as lemmas.
   *
   * Notice a term is redundant in a context if it is congruent to another
   * term that is already in the context; it is not relevant if no cardinality
   * constraints exist for its type.
   */
  void checkRegister();
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
  void checkMinCard();
  /** check cardinality cycles
   *
   * The purpose of this inference schema is to construct two data structures:
   *
   * (1) d_card_parent, which maps set terms (A op B) for op in { \, ^ } to
   * equivalence class representatives of their "parents", where:
   *   parent( A ^ B ) = A, B
   *   parent( A \ B ) = A
   * Additionally, (A union B) is a parent of all three of the above sets
   * if it exists as a term in the current context. As exceptions,
   * if A op B = A, then A is not a parent of A ^ B and similarly for B.
   * If A ^ B is empty, then it has no parents.
   *
   * We say the cardinality graph induced by the current set of equalities
   * is an (irreflexive, acyclic) graph whose nodes are equivalence classes and
   * which contains a (directed) edge r1 to r2 if there exists a term t2 in r2
   * that has some parent t1 in r1.
   *
   * (2) d_oSetEqc, an ordered set of equivalence classes whose types are set.
   * These equivalence classes have the property that if r1 is a descendant
   * of r2 in the cardinality graph, then r1 must come before r2 in d_oSetEqc.
   *
   * This inference schema may make various inferences while building these
   * two data structures if the current equality arrangement of sets is not
   * as expected. For example, it will infer equalities between sets based on
   * the emptiness and equalities of sets in adjacent children in the
   * cardinality graph, to give some examples:
   *   (A \ B = empty) => A = A ^ B
   *   A^B = B => B \ A = empty
   *   A union B = A ^ B => A \ B = empty AND B \ A = empty
   * and so on.
   *
   * It will also recognize when a cycle occurs in the cardinality graph, in
   * which case an equality chain between sets can be inferred. For an example,
   * see checkCardCyclesRec below.
   *
   * This method is inspired by the checkCycles inference schema in the theory
   * of strings.
   */
  void checkCardCycles();
  /**
   * Helper function for above. Called when wish to process equivalence class
   * eqc.
   *
   * Argument curr contains the equivalence classes we are currently processing,
   * which are descendants of eqc in the cardinality graph, where eqc is the
   * representative of some equivalence class.
   *
   * Argument exp contains an explanation of why the chain of children curr
   * are descedants of . For example, say we are in context with equivalence
   * classes:
   *   { A, B, C^D }, { D, B ^ C,  A ^ E }
   * We may recursively call this method via the following steps:
   *   eqc = D, curr = {}, exp = {}
   *   eqc = A, curr = { D }, exp = { D = B^C }
   *   eqc = A, curr = { D, A }, exp = { D = B^C, A = C^D }
   * after which we discover a cycle in the cardinality graph. We infer
   * that A must be equal to D, where exp is an explanation of the cycle.
   */
  void checkCardCyclesRec(Node eqc,
                          std::vector<Node>& curr,
                          std::vector<Node>& exp);
  /** check normal forms
   *
   * This method attempts to assign "normal forms" to all set equivalence
   * classes whose types have cardinality constraints. Normal forms are
   * defined recursively.
   *
   * A "normal form" of an equivalence class [r] (where [r] denotes the
   * equivalence class whose representative is r) is a set of representatives
   * U = { r1, ..., rn }. If there exists at least one set in [r] that has a
   * "flat form", then all sets in the equivalence class have flat form U.
   * If no set in U has a flat form, then U = { r } if r does not contain
   * the empty set, and {} otherwise. Notice that the choice of representative
   * r is determined by the equality engine.
   *
   * A "flat form" of a set term T is the union of the normal forms of the
   * equivalence classes that contain sets whose parent is T.
   *
   * In terms of the cardinality graph, the "flat form" of term t is the set
   * of leaves of t that are descendants of it in the cardinality graph induced
   * by the current set of assertions. Notice a flat form is only defined if t
   * has children. If all terms in an equivalence class E with flat forms have
   * the same flat form, then E is added as a node to the cardinality graph with
   * edges connecting to all equivalence classes with terms that have a parent
   * in E.
   *
   * In the following inference schema, the argument intro_sets is updated to
   * contain the set of new set terms that the procedure is requesting to
   * introduce for the purpose of forcing the flat forms of two equivalent sets
   * to become identical. If any equivalence class cannot be assigned a normal
   * form, then the resulting intro_sets is guaranteed to be non-empty.
   *
   * As an example, say we have a context with equivalence classes:
   *   {A, D}, {C, A^B}, {E, C^D}, {C\D}, {D\C}, {A\B}, {empty, B\A},
   * where assume the first term in each set is its representative. An ordered
   * list d_oSetEqc for this context:
   *   A, C, E, C\D, D\C, A\B, empty, ...
   * The normal form of {empty, B\A} is {}, since it contains the empty set.
   * The normal forms for each of the singleton equivalence classes are
   * themselves.
   * The flat form of each of E and C^D does not exist, hence the normal form
   * of {E, C^D} is {E}.
   * The flat form of C is {E, C\D}, noting that C^D and C\D are terms whose
   * parent is C, hence {E, C\D} is the normal form for class {C, A^B}.
   * The flat form of A is {E, C\D, A\B} and the flat form of D is {E, D\C}.
   * Hence, no normal form can be assigned to class {A, D}. Instead this method
   * will e.g. add (C\D)^E to intro_sets, which will force the solver
   * to explore a model where the Venn regions (C\D)^E (C\D)\E and E\(C\D) are
   * considered while constructing flat forms. Splitting on whether these sets
   * are empty will eventually lead to a model where the flat forms of A and D
   * are the same.
   */
  void checkNormalForms(std::vector<Node>& intro_sets);
  /**
   * Called for each equivalence class, in order of d_oSetEqc, by the above
   * function.
   */
  void checkNormalForm(Node eqc, std::vector<Node>& intro_sets);

  /**
   * Add cardinality lemmas for the univset of each type with cardinality terms.
   * The lemmas are explained below.
   */
  void checkCardinalityExtended();
  /**
   * This function adds the following lemmas for type t for each S
   * where S is a (representative) set term of type t, and for each negative
   * member x not in S:
   * 1- (=> true (<= (card (as univset t)) n) where n is the
   * cardinality of t, which may be symbolic
   * 2- (=> true (subset S (as univset t)) where S is a set
   * term of type t
   * 3- (=> (not (member negativeMember S))) (member
   * negativeMember (as univset t)))
   */
  void checkCardinalityExtended(TypeNode& t);

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
  /** The ordered set of equivalence classes, see checkCardCycles. */
  std::vector<Node> d_oSetEqc;
  /**
   * This maps set terms to the set of representatives of their "parent" sets,
   * see checkCardCycles.
   */
  std::map<Node, std::vector<Node> > d_card_parent;
  /**
   * Maps equivalence classes + set terms in that equivalence class to their
   * "flat form" (see checkNormalForms).
   */
  std::map<Node, std::map<Node, std::vector<Node> > > d_ff;
  /** Maps equivalence classes to their "normal form" (see checkNormalForms). */
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

  /**
   * a map to store proxy nodes for the universe sets
   */
  std::map<Node, Node> d_univProxy;

  /**
   * collect the elements in all sets of finite types in model, and
   * store them in the field d_finite_type_elements
   */
  void collectFiniteTypeSetElements(TheoryModel* model);
  /**
   * a map to store the non-slack elements encountered so far in all finite
   * types
   */
  std::map<TypeNode, std::vector<Node> > d_finite_type_elements;
  /**
   * a map to store slack elements in all finite types
   */
  std::map<TypeNode, std::vector<TNode> > d_finite_type_slack_elements;
  /** This boolean determines whether we already collected finite type constants
   *  present in the current model.
   *  Default value is false
   */
  bool d_finite_type_constants_processed;

  /*
   * a map that stores skolem nodes n that satisfies the constraint
   * (<= (card t) n) where t is an infinite type
   */
  std::map<TypeNode, Node> d_infiniteTypeUnivCardSkolems;

}; /* class CardinalityExtension */

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

#endif
