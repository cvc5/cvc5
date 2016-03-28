/*********************                                                        */
/*! \file equality_infer.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief additional inference for equalities
 **/

#include "cvc4_private.h"

#ifndef EQUALITY_INFER_H
#define EQUALITY_INFER_H

#include <ext/hash_set>
#include <iostream>
#include <map>
#include <vector>

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdhashmap.h"
#include "context/cdchunk_list.h"
#include "context/cdhashset.h"
#include "theory/theory.h"


namespace CVC4 {
namespace theory {
namespace quantifiers {

class EqualityInference
{
  typedef context::CDHashMap< Node, Node, NodeHashFunction > NodeMap;
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  typedef context::CDChunkList<Node> NodeList;
  typedef context::CDHashMap< Node, NodeList *, NodeHashFunction > NodeListMap;
private:
  context::Context * d_c;
  Node d_one;
  class EqcInfo {
  public:
    EqcInfo(context::Context* c);
    ~EqcInfo(){}
    context::CDO< Node > d_rep;
    context::CDO< bool > d_valid;
  };

  /** information necessary for equivalence classes */
  NodeMap d_elim_vars;
  std::map< Node, EqcInfo * > d_eqci;
  NodeMap d_rep_to_eqc;
  /** set eqc rep */
  void setEqcRep( Node t, Node r, EqcInfo * eqci );
  /** use list */
  NodeListMap d_uselist;
  void addToUseList( Node used, Node eqc );
public:
  EqualityInference(context::Context* c);
  virtual ~EqualityInference();
  /** notification when equality engine is updated */
  void eqNotifyNewClass(TNode t);
  void eqNotifyMerge(TNode t1, TNode t2);
  
  NodeList d_pending_merges;
};

}
}
}

#endif
