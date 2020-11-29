/*********************                                                        */
/*! \file equality_infer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief additional inference for equalities
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__EQUALITY_INFER_H
#define CVC4__THEORY__QUANTIFIERS__EQUALITY_INFER_H

#include <iostream>
#include <map>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/context.h"
#include "context/context_mm.h"
#include "theory/theory.h"


namespace CVC4 {
namespace theory {
namespace quantifiers {

class EqualityInference
{
  typedef context::CDHashMap< Node, Node, NodeHashFunction > NodeMap;
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  typedef context::CDList<Node> NodeList;
  typedef context::CDHashMap< Node, int, NodeHashFunction > NodeIntMap;
private:
  context::Context * d_c;
  Node d_one;
  Node d_true;
  class EqcInfo {
  public:
    EqcInfo(context::Context* c);
    ~EqcInfo(){}
    context::CDO< Node > d_rep;
    //whether the eqc of this info is a representative and d_rep can been computed successfully
    context::CDO< bool > d_valid;
    //whether the eqc of this info is a solved variable
    context::CDO< bool > d_solved;
    //master equivalence class (a union find)
    context::CDO< Node > d_master;
    //a vector of equalities t1=t2 for which eqNotifyMerge(t1,t2) was called that explains d_rep
    //NodeList d_rep_exp;
    //the list of other eqc where this variable may be appear
    //NodeList d_uselist;
  };

  /** track explanations */
  bool d_trackExplain;
  /** information necessary for equivalence classes */
  BoolMap d_elim_vars;
  std::map< Node, EqcInfo * > d_eqci;
  NodeMap d_rep_to_eqc;
  NodeIntMap d_rep_exp;
  std::map< Node, std::vector< Node > > d_rep_exp_data;
  /** set eqc rep */
  void setEqcRep( Node t, Node r, std::vector< Node >& exp_to_add, EqcInfo * eqci );
  /** use list */
  NodeIntMap d_uselist;
  std::map< Node, std::vector< Node > > d_uselist_data;
  void addToUseList( Node used, Node eqc );
  /** pending merges */
  NodeList d_pending_merges;
  NodeList d_pending_merge_exp;
  /** add to explanation */
  void addToExplanation( std::vector< Node >& exp, Node e );
  void addToExplanationEqc( std::vector< Node >& exp, Node eqc );
  void addToExplanationEqc( Node eqc, std::vector< Node >& exp_to_add );
  /** for setting master/slave */
  Node getMaster( Node t, EqcInfo * eqc, bool& updated, Node new_m = Node::null() );
  bool updateMaster( Node t1, Node t2, EqcInfo * eqc1, EqcInfo * eqc2 );
public:
  //second argument is whether explanations should be tracked
  EqualityInference(context::Context* c, bool trackExp = false);
  virtual ~EqualityInference();
  /** input : notification when equality engine is updated */
  void eqNotifyNewClass(TNode t);
  void eqNotifyMerge(TNode t1, TNode t2);
  /** output : inferred equalities */
  unsigned getNumPendingMerges() { return d_pending_merges.size(); }
  Node getPendingMerge( unsigned i ) { return d_pending_merges[i]; }  
  Node getPendingMergeExplanation( unsigned i );
};

}
}
}

#endif
