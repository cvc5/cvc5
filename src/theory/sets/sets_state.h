/*********************                                                        */
/*! \file theory_sets_private.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory implementation.
 **
 ** Sets theory implementation.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SETS__THEORY_SETS_STATE_H
#define CVC4__THEORY__SETS__THEORY_SETS_STATE_H

#include <vector>
#include <map>

#include "theory/uf/equality_engine.h"
#include "context/cdhashset.h"

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
 * to initialize the information in this class regarding (1).
 * 
 */
class SetsState {
  typedef context::CDHashMap< Node, Node, NodeHashFunction > NodeMap;
public:
  SetsState(TheorySetsPrivate& p,
                 eq::EqualityEngine& e,
                    context::Context* c,
                    context::UserContext* u);
  /** reset */
  void reset();
  /** register equivalence class whose type is tn */
  void registerEqc(TypeNode tn, Node r);
  /** register term n of type tnn in the equivalence class of r */
  void registerTerm(Node r, TypeNode tnn, Node n);
  /** Is formula n entailed to have polarity pol in the current context? */
  bool isEntailed( Node n, bool pol );
  /** 
   * Is the disequality between sets s and t entailed in the current context?
   */
  bool isSetDisequalityEntailed( Node s, Node t );
  /** Is a=b according to equality reasoning? */
  bool areEqual( Node a, Node b );
  /** Is a!=b according to equality reasoning? */
  bool areDisequal( Node a, Node b );
  /** 
   * Get the equivalence class of the empty set of type tn, or null if it does
   * not exist as a term in the current context.
   */
  Node getEmptySetEqClass( TypeNode tn ) const;
  /** 
   * Get the equivalence class of the universe set of type tn, or null if it
   * does not exist as a term in the current context.
   */
  Node getUnivSetEqClass( TypeNode tn ) const;
  /** 
   * Get the singleton set in the equivalence class of representative r if it
   * exists, or null if none exists.
   */
  Node getSingletonEqClass( Node r ) const;
  /** get binary operator term (modulo equality)
   * 
   * This method returns a non-null node n if and only if a term n that is
   * congruent to <k>(r1,r2) exists in the current context.
   */
  Node getBinaryOpTerm( Kind k, Node r1, Node r2 ) const;
  /** 
   * Returns a term that is congruent to n in the current context.
   * 
   * To ensure that inferences and processing is not redundant,
   * this class computes congruence over all terms that exist in the current
   * context. If a set of terms f( t1 ), ... f( tn ) are pairwise congruent
   * (call this a congruence class), it selects one of these terms as a
   * representative. All other terms return the representative term from
   * its congruence class.
   */
  Node getCongruent( Node n ) const;
  /** 
   * This method returns true if n is not the representative of its congruence
   * class.
   */
  bool isCongruent(Node n) const { return d_congruent.find(n)!=d_congruent.end(); }
  /** Get the list of all equivalence classes of set type */
  std::vector< Node >& getSetsEqClasses() { return d_set_eqc; }
  /** 
   * Get the list of non-variable sets that exists in the equivalence class
   * whose representative is r. 
   */
  std::vector< Node >& getNonVariableSets(Node r) { return d_nvar_sets[r]; }
  /** 
   * Get a variable set in the equivalence class with representative r, or null
   * if none exist.
   */
  Node getVariableSet(Node r) const;
  /** Get (positive) members of the set equivalence class r */
  std::map< Node, Node >& getMembers(Node r) { return d_pol_mems[0][r]; }
  /** Get negative members of the set equivalence class r */
  std::map< Node, Node >& getNegativeMembers(Node r) { return d_pol_mems[1][r]; }
  /** Is the members list of set equivalence class r non-empty? */
  bool hasMembers(Node r) const;
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
  Node getProxy( Node n );
  /** Get the empty set of type tn */
  Node getEmptySet( TypeNode tn );
  /** Get the universe set of type tn */
  Node getUnivSet( TypeNode tn );
  // --------------------------------------- end commonly used terms
private:
  /** constants */
  Node d_true;
  Node d_false;
  /** Reference to the parent theory of sets */
  TheorySetsPrivate& d_parent;
  /** Reference to the equality engine of theory of sets */
  eq::EqualityEngine& d_ee;
  /** Map from set terms to their proxy variables */
  NodeMap d_proxy;
  /** Backwards map of above */
  NodeMap d_proxy_to_term;
  /** The list of all equivalence classes of type set in the current context */
  std::vector< Node > d_set_eqc;
  /** Maps types to the equivalence class containing empty set of that type */
  std::map< TypeNode, Node > d_eqc_emptyset;
  /** Maps types to the equivalence class containing univ set of that type */
  std::map< TypeNode, Node > d_eqc_univset;
  std::map< Node, Node > d_eqc_singleton;
  std::map< TypeNode, Node > d_emptyset;
  std::map< TypeNode, Node > d_univset;
  /** Map from terms to the representative of their congruence class */
  std::map< Node, Node > d_congruent;
  /** Map from equivalence classes to the list of non-variable sets in that equivalence class */
  std::map< Node, std::vector< Node > > d_nvar_sets;
  std::map< Node, Node > d_var_set;
public: //FIXME
  std::map< Node, std::map< Node, Node > > d_pol_mems[2];
  // -------------------------------- term indices
  std::map< Node, std::map< Node, Node > > d_members_index;
  std::map< Node, Node > d_singleton_index;
  std::map< Kind, std::map< Node, std::map< Node, Node > > > d_bop_index;
  // -------------------------------- end term indices
  std::map< Kind, std::vector< Node > > d_op_list;
private:
  /** type constraint skolems (see getTypeConstraintSkolem) */
  std::map<Node, std::map<TypeNode, Node> > d_tc_skolem;  
  
  /** is set disequality entailed internal 
   * 
   * This returns true if disequality between sets a and b is entailed in the
   * current context. We use an incomplete test based on equality and membership
   * information.
   * 
   * eqE is the representative of the equivalence class of the empty set
   * whose type is the same as a and b.
   */
  bool isSetDisequalityEntailedInternal( Node a, Node b, Node re );
};/* class TheorySetsPrivate */


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__SETS__THEORY_SETS_STATE_H */
