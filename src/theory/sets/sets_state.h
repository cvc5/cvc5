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
  /** Is the disequality between sets s and t entailed in the current context?
   * 
   * FIXME
   */
  bool isSetDisequalityEntailed( Node s, Node t );
  /** Is a=b according to equality reasoning? */
  bool ee_areEqual( Node a, Node b );
  /** Is a!=b according to equality reasoning? */
  bool ee_areDisequal( Node a, Node b );
  /** 
   * Get the equivalence class of the empty set of type tn, or null if it does
   * not exist as a term in the current context.
   */
  Node getEmptySetEqClass( TypeNode tn ) const;
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
  
  /** get type constraint skolem for n and tn */
  Node getTypeConstraintSkolem(Node n, TypeNode tn);
  /** get the proxy variable for set n
   * 
   * FIXME
   */
  Node getProxy( Node n );
  /** Returns a term that is congruent to n in the current context */
  Node getCongruent( Node n );
  /** is congruent */
  bool isCongruent(Node n) const { return d_congruent.find(n)!=d_congruent.end(); }
  /** Get the empty set of type tn */
  Node getEmptySet( TypeNode tn );
  /** Get the universe set of type tn */
  Node getUnivSet( TypeNode tn );
  
  
  /** get sets equivalence classes */
  std::vector< Node >& getSetsEqClasses() { return d_set_eqc; }
  /** get non-variable sets for representative r */
  std::vector< Node >& getNonVariableSets(Node r) { return d_nvar_sets[r]; }
  /** get (positive) members */
  std::map< Node, Node >& getMembers(Node r) { return d_pol_mems[0][r]; }
  /** Are there members entailed for equivalence class r? */
  bool hasMembers(Node r) const;
private:
  /** constants */
  Node d_true;
  Node d_false;
  /** Reference to the equality engine of theory of sets */
  eq::EqualityEngine& d_ee;
  
  NodeMap d_proxy;
  NodeMap d_proxy_to_term;
  
  std::map< Node, std::vector< Node > > d_members_data;
  std::vector< Node > d_set_eqc;
  std::map< Node, bool > d_set_eqc_relevant;
  std::map< Node, std::vector< Node > > d_set_eqc_list;
  std::map< TypeNode, Node > d_eqc_emptyset;
  std::map< TypeNode, Node > d_eqc_univset;
  std::map< Node, Node > d_eqc_singleton;
  std::map< TypeNode, Node > d_emptyset;
  std::map< TypeNode, Node > d_univset;
  std::map< Node, Node > d_congruent;
  std::map< Node, std::vector< Node > > d_nvar_sets;
  std::map< Node, Node > d_var_set;
  std::map< Node, std::map< Node, Node > > d_pol_mems[2];
  std::map< Node, std::map< Node, Node > > d_members_index;
  std::map< Node, Node > d_singleton_index;
  std::map< Kind, std::map< Node, std::map< Node, Node > > > d_bop_index;
  std::map< Kind, std::vector< Node > > d_op_list;
  /** type constraint skolems
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
  std::map<Node, std::map<TypeNode, Node> > d_tc_skolem;  
};/* class TheorySetsPrivate */


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__SETS__THEORY_SETS_STATE_H */
