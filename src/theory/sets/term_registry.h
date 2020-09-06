/*********************                                                        */
/*! \file solver_state.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets state object
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SETS__THEORY_SOLVER_STATE_H
#define CVC4__THEORY__SETS__THEORY_SOLVER_STATE_H

#include <map>
#include <vector>

#include "context/cdhashset.h"
#include "theory/sets/skolem_cache.h"
#include "theory/theory_state.h"
#include "theory/uf/equality_engine.h"
#include "theory/sets/inference_manager.h"
#include "theory/sets/solver_state.h"

namespace CVC4 {
namespace theory {
namespace sets {

class TheorySetsPrivate;

/** Sets state
 *
 * The purpose of this class is to:
 * (1) Maintain information concerning the current set of assertions during a
 * full effort check,
 * (2) Maintain a database of commonly used terms.
 *
 * During a full effort check, the solver for theory of sets should call:
 *   reset; ( registerEqc | registerTerm )*
 * to initialize the information in this class regarding full effort checks.
 * Other query calls are then valid for the remainder of the full effort check.
 */
class TermRegistry
{
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeMap;

 public:
  TermRegistry(SolverState& state, InferenceManager& im);
  //-------------------------------- initialize per check
  /** reset, clears the data structures maintained by this class. */
  void reset();
  /** register equivalence class whose type is tn */
  void registerEqc(TypeNode tn, Node r);
  /** register term n of type tnn in the equivalence class of r */
  void registerTerm(Node r, TypeNode tnn, Node n);
  //-------------------------------- end initialize per check
  /**
   * Get the equivalence class of the empty set of type tn, or null if it does
   * not exist as a term in the current context.
   */
  Node getEmptySetEqClass(TypeNode tn) const;
  /**
   * Get the equivalence class of the universe set of type tn, or null if it
   * does not exist as a term in the current context.
   */
  Node getUnivSetEqClass(TypeNode tn) const;
  /**
   * Get the singleton set in the equivalence class of representative r if it
   * exists, or null if none exists.
   */
  Node getSingletonEqClass(Node r) const;
  /** get binary operator term (modulo equality)
   *
   * This method returns a non-null node n if and only if a term n that is
   * congruent to <k>(r1,r2) exists in the current context.
   */
  Node getBinaryOpTerm(Kind k, Node r1, Node r2) const;
  /**
   * Returns a term that is congruent to n in the current context.
   *
   * To ensure that inferences and processing is not redundant,
   * this class computes congruence over all terms that exist in the current
   * context. If a set of terms f( t1 ), ... f( tn ) are pairwise congruent
   * (call this a "congruence class"), it selects one of these terms as a
   * representative. All other terms return the representative term from
   * its congruence class.
   */
  Node getCongruent(Node n) const;
  /**
   * This method returns true if n is not the representative of its congruence
   * class.
   */
  bool isCongruent(Node n) const;

  /** Get the list of all equivalence classes of set terms */
  const std::vector<Node>& getSetsEqClasses() const { return d_set_eqc; }
  /** Get the list of all equivalence classes of set terms that have element
   * type t */
  const std::vector<Node> getSetsEqClasses(const TypeNode& t) const;

  /**
   * Get the list of non-variable sets that exists in the equivalence class
   * whose representative is r.
   */
  const std::vector<Node>& getNonVariableSets(Node r) const;
  /**
   * Get a variable set in the equivalence class with representative r, or null
   * if none exist.
   */
  Node getVariableSet(Node r) const;
  /** Get comprehension sets in equivalence class with representative r */
  const std::vector<Node>& getComprehensionSets(Node r) const;
  /** Get (positive) members of the set equivalence class r
   *
   * The members are return as a map, which maps members to their explanation.
   * For example, if x = y, (member 5 y), (member 6 x), then getMembers(x)
   * returns the map [ 5 -> (member 5 y), 6 -> (member 6 x)].
   */
  const std::map<Node, Node>& getMembers(Node r) const;
  /** Get negative members of the set equivalence class r, similar to above */
  const std::map<Node, Node>& getNegativeMembers(Node r) const;
  /** Is the (positive) members list of set equivalence class r non-empty? */
  bool hasMembers(Node r) const;
  /** Get binary operator index
   *
   * This returns a mapping from binary operator kinds (INTERSECT, SETMINUS,
   * UNION) to index of terms of that kind. Each kind k maps to a map whose
   * entries are of the form [r1 -> r2 -> t], where t is a term in the current
   * context, and t is of the form <k>(t1,t2) where t1=r1 and t2=r2 hold in the
   * current context. The term t is the representative of its congruence class.
   */
  const std::map<Kind, std::map<Node, std::map<Node, Node> > >&
  getBinaryOpIndex() const;
  /** get operator list
   *
   * This returns a mapping from set kinds to a list of terms of that kind
   * that exist in the current context. Each of the terms in the range of this
   * map is a representative of its congruence class.
   */
  const std::map<Kind, std::vector<Node> >& getOperatorList() const;
  /** Get the list of all comprehension sets in the current context */
  const std::vector<Node>& getComprehensionSets() const;

  // --------------------------------------- commonly used terms
  /** Get type constraint skolem
   *
   * The sets theory solver outputs equality lemmas of the form:
   *   n = d_tc_skolem[n][tn]
   * where the type of d_tc_skolem[n][tn] is tn, and the type
   * of n is not a subtype of tn. This is required to handle benchmarks like
   *   test/regress/regress0/sets/sets-of-sets-subtypes.smt2
   * where for s : (Set Int) and t : (Set Real), we have that
   *   ( s = t ^ y in t ) implies ( exists k : Int. y = k )
   * The type constraint Skolem for (y, Int) is the skolemization of k above.
   */
  Node getTypeConstraintSkolem(Node n, TypeNode tn);
  /** get the proxy variable for set n
   *
   * Proxy variables are used to communicate information that otherwise would
   * not be possible due to rewriting. For example, the literal
   *   card( singleton( 0 ) ) = 1
   * is rewritten to true. Instead, to communicate this fact (e.g. to other
   * theories), we require introducing a proxy variable x for singleton( 0 ).
   * Then:
   *   card( x ) = 1 ^ x = singleton( 0 )
   * communicates the equivalent of the above literal.
   */
  Node getProxy(Node n);
  /** Get the empty set of type tn */
  Node getEmptySet(TypeNode tn);
  /** Get the universe set of type tn if it exists or create a new one */
  Node getUnivSet(TypeNode tn);
  /**
   * Get the skolem cache of this theory, which manages a database of introduced
   * skolem variables used for various inferences.
   */
  SkolemCache& getSkolemCache() { return d_skCache; }
  // --------------------------------------- end commonly used terms
  /** debug print set */
  void debugPrintSet(Node s, const char* c) const;

 private:
  /** constants */
  Node d_true;
  Node d_false;
  /** the empty vector and map */
  std::vector<Node> d_emptyVec;
  std::map<Node, Node> d_emptyMap;
  /** The state */
  SolverState& d_state;
  /** The inference manager */
  InferenceManager& d_im;
  /** The list of all equivalence classes of type set in the current context */
  std::vector<Node> d_set_eqc;
  /** Maps types to the equivalence class containing empty set of that type */
  std::map<TypeNode, Node> d_eqc_emptyset;
  /** Maps types to the equivalence class containing univ set of that type */
  std::map<TypeNode, Node> d_eqc_univset;
  /** Maps equivalence classes to a singleton set that exists in it. */
  std::map<Node, Node> d_eqc_singleton;
  /** Map from terms to the representative of their congruence class */
  std::map<Node, Node> d_congruent;
  /** Map from equivalence classes to the list of non-variable sets in it */
  std::map<Node, std::vector<Node> > d_nvar_sets;
  /** Map from equivalence classes to the list of comprehension sets in it */
  std::map<Node, std::vector<Node> > d_compSets;
  /** Map from equivalence classes to a variable sets in it */
  std::map<Node, Node> d_var_set;
  // --------------------------------------- commonly used terms
  /** Map from set terms to their proxy variables */
  NodeMap d_proxy;
  /** Backwards map of above */
  NodeMap d_proxy_to_term;
  /** Cache of type constraint skolems (see getTypeConstraintSkolem) */
  std::map<Node, std::map<TypeNode, Node> > d_tc_skolem;
  /** Map from types to empty set of that type */
  std::map<TypeNode, Node> d_emptyset;
  /** Map from types to universe set of that type */
  std::map<TypeNode, Node> d_univset;
  // --------------------------------------- end commonly used terms
  // -------------------------------- term indices
  /** Term index for MEMBER
   *
   * A term index maps equivalence class representatives to the representative
   * of their congruence class.
   *
   * For example, the term index for member may contain an entry
   * [ r1 -> r2 -> (member t1 t2) ] where r1 and r2 are representatives of their
   * equivalence classes, (member t1 t2) is the representative of its congruence
   * class, and r1=t1 and r2=t2 hold in the current context.
   */
  std::map<Node, std::map<Node, Node> > d_members_index;
  /** Term index for SINGLETON */
  std::map<Node, Node> d_singleton_index;
  /** Indices for the binary kinds INTERSECT, SETMINUS and UNION. */
  std::map<Kind, std::map<Node, std::map<Node, Node> > > d_bop_index;
  /** A list of comprehension sets */
  std::vector<Node> d_allCompSets;
  // -------------------------------- end term indices
  std::map<Kind, std::vector<Node> > d_op_list;
  /** the skolem cache */
  SkolemCache d_skCache;
}; /* class TheorySetsPrivate */

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SETS__THEORY_SOLVER_STATE_H */
