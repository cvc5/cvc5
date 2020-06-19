/*********************                                                        */
/*! \file static_fact_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Path-compressing, backtrackable union-find using an undo
 ** stack. Refactored from the UF union-find.
 **
 ** Path-compressing, backtrackable union-find using an undo stack
 ** rather than storing items in a CDMap<>.
 **/

#include <iostream>

#include "base/check.h"
#include "expr/node.h"
#include "theory/arrays/static_fact_manager.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arrays {

bool StaticFactManager::areEq(TNode a, TNode b) {
  return (find(a) == find(b));
}

bool StaticFactManager::areDiseq(TNode a, TNode b) {
  Node af = find(a);
  Node bf = find(b);
  Node left, right;
  unsigned i;
  for (i = 0; i < d_diseq.size(); ++i) {
    left = find(d_diseq[i][0]);
    right = find(d_diseq[i][1]);
    if ((left == af && right == bf) ||
        (left == bf && right == af)) {
      return true;
    }
  }
  return false;
}

void StaticFactManager::addDiseq(TNode eq) {
  Assert(eq.getKind() == kind::EQUAL);
  d_diseq.push_back(eq);
}

void StaticFactManager::addEq(TNode eq) {
  Assert(eq.getKind() == kind::EQUAL);
  Node a = find(eq[0]);
  Node b = find(eq[1]);

  if( a == b) {
    return;
  }

  /*
   * take care of the congruence closure part
   */

  // make "a" the one with shorter diseqList
  // CNodeTNodesMap::iterator deq_ia = d_disequalities.find(a);
  // CNodeTNodesMap::iterator deq_ib = d_disequalities.find(b);

  // if(deq_ia != d_disequalities.end()) {
  //   if(deq_ib == d_disequalities.end() ||
  //      (*deq_ia).second->size() > (*deq_ib).second->size()) {
  //     TNode tmp = a;
  //     a = b;
  //     b = tmp;
  //   }
  // }
  // a = find(a);
  // b = find(b);


  // b becomes the canon of a
  setCanon(a, b);

  // deq_ia = d_disequalities.find(a);
  // map<TNode, TNode> alreadyDiseqs;
  // if(deq_ia != d_disequalities.end()) {
  //   /*
  //    * Collecting the disequalities of b, no need to check for conflicts
  //    * since the representative of b does not change and we check all the things
  //    * in a's class when we look at the diseq list of find(a)
  //    */

  //   CNodeTNodesMap::iterator deq_ib = d_disequalities.find(b);
  //   if(deq_ib != d_disequalities.end()) {
  //     CTNodeListAlloc* deq = (*deq_ib).second;
  //     for(CTNodeListAlloc::const_iterator j = deq->begin(); j!=deq->end();
  //     j++) {
  //       TNode deqn = *j;
  //       TNode s = deqn[0];
  //       TNode t = deqn[1];
  //       TNode sp = find(s);
  //       TNode tp = find(t);
  //       Assert(sp == b || tp == b);
  //       if(sp == b) {
  //         alreadyDiseqs[tp] = deqn;
  //       } else {
  //         alreadyDiseqs[sp] = deqn;
  //       }
  //     }
  //   }

  //   /*
  //    * Looking for conflicts in the a disequality list. Note
  //    * that at this point a and b are already merged. Also has
  //    * the side effect that it adds them to the list of b (which
  //    * became the canonical representative)
  //    */

  //   CTNodeListAlloc* deqa = (*deq_ia).second;
  //   for(CTNodeListAlloc::const_iterator i = deqa->begin(); i!= deqa->end();
  //   i++) {
  //     TNode deqn = (*i);
  //     Assert(deqn.getKind() == kind::EQUAL || deqn.getKind() ==
  //     kind::IFF); TNode s = deqn[0]; TNode t = deqn[1]; TNode sp = find(s);
  //     TNode tp = find(t);

  //     if(find(s) == find(t)) {
  //       d_conflict = deqn;
  //       return;
  //     }
  //     Assert( sp == b || tp == b);

  //     // make sure not to add duplicates

  //     if(sp == b) {
  //       if(alreadyDiseqs.find(tp) == alreadyDiseqs.end()) {
  //         appendToDiseqList(b, deqn);
  //         alreadyDiseqs[tp] = deqn;
  //       }
  //     } else {
  //       if(alreadyDiseqs.find(sp) == alreadyDiseqs.end()) {
  //         appendToDiseqList(b, deqn);
  //         alreadyDiseqs[sp] = deqn;
  //       }
  //     }

  //   }
  // }

  // // TODO: check for equality propagations
  // // a and b are find(a) and find(b) here
  // checkPropagations(a,b);

  // if(a.getType().isArray()) {
  //   checkRowLemmas(a,b);
  //   checkRowLemmas(b,a);
  //   // note the change in order, merge info adds the list of
  //   // the 2nd argument to the first
  //   d_infoMap.mergeInfo(b, a);
  // }
}


}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
