/*********************                                                        */
/*! \file bv_subtheory_inequality.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__BV_SUBTHEORY__INEQUALITY_H
#define __CVC4__THEORY__BV__BV_SUBTHEORY__INEQUALITY_H

#include "theory/bv/bv_subtheory.h"
#include "theory/bv/bv_inequality_graph.h"
#include "context/cdhashset.h"

namespace CVC4 {
namespace theory {
namespace bv {

class InequalitySolver: public SubtheorySolver {
  struct Statistics {
    IntStat d_numCallstoCheck;
    Statistics();
    ~Statistics();
  };

  context::CDHashSet<Node, NodeHashFunction> d_assertionSet;
  InequalityGraph d_inequalityGraph;
  context::CDHashMap<Node, TNode, NodeHashFunction> d_explanations;
  context::CDO<bool> d_isComplete;
  __gnu_cxx::hash_map<TNode, bool, TNodeHashFunction> d_ineqTermCache;
  bool isInequalityOnly(TNode node);
  Statistics d_statistics;
public:
  InequalitySolver(context::Context* c, TheoryBV* bv)
    : SubtheorySolver(c, bv),
      d_assertionSet(c),
      d_inequalityGraph(c),
      d_explanations(c),
      d_isComplete(c, true),
      d_ineqTermCache(),
      d_statistics()
  {}

  bool check(Theory::Effort e);
  void propagate(Theory::Effort e);
  void explain(TNode literal, std::vector<TNode>& assumptions);
  bool isComplete() { return d_isComplete; }
  void collectModelInfo(TheoryModel* m, bool fullModel);
  Node getModelValue(TNode var);
  EqualityStatus getEqualityStatus(TNode a, TNode b);
  void assertFact(TNode fact);
};

}
}
}

#endif /* __CVC4__THEORY__BV__BV_SUBTHEORY__INEQUALITY_H */
