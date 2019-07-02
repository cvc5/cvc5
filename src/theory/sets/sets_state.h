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
  typedef context::CDHashMap< Node, int, NodeHashFunction> NodeIntMap;
public:
  SetsState(TheorySetsPrivate& p,
                 eq::EqualityEngine& e,
                    context::Context* c,
                    context::UserContext* u);
  /** Is formula n entailed to have polarity pol in the current context? */
  bool isEntailed( Node n, bool pol );
  /** Is x entailed to be a member of set s? */
  bool isMember( Node x, Node s );
  bool isSetDisequalityEntailed( Node s, Node t );
  /** Is a=b according to equality reasoning? */
  bool ee_areEqual( Node a, Node b );
  /** Is a!=b according to equality reasoning? */
  bool ee_areDisequal( Node a, Node b );
  /** is congruent */
  bool isCongruent(Node n) const { return d_congruent.find(n)!=d_congruent.end(); }
  
  
  /** get type constraint skolem for n and tn */
  Node getTypeConstraintSkolem(Node n, TypeNode tn);
  Node getProxy( Node n );
  Node getCongruent( Node n );
  Node getEmptySet( TypeNode tn );
  Node getUnivSet( TypeNode tn );
  
  
  /** get sets equivalence classes */
  std::vector< Node >& getSetsEqClasses() { return d_set_eqc; }
  /** get non-variable sets for representative r */
  std::vector< Node >& getNonVariableSets(Node r) { return d_nvar_sets[r]; }
private:
  /** constants */
  Node d_true;
  Node d_false;
  /** Reference to the equality engine of theory of sets */
  eq::EqualityEngine& d_ee;
  
  NodeMap d_proxy;
  NodeMap d_proxy_to_term;
  
  NodeIntMap d_members;
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
  std::map< Node, TypeNode > d_most_common_type;
  std::map< Node, Node > d_most_common_type_term;
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
