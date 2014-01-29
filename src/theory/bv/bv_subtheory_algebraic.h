/*********************                                                        */
/*! \file bv_subtheory_algebraic.h
** \verbatim
** Original author: Liana Hadarean 
** Major contributors: none
** Minor contributors (to current version): none
** This file is part of the CVC4 project.
** Copyright (c) 2009-2013  New York University and The University of Iowa
** See the file COPYING in the top-level source directory for licensing
** information.\endverbatim
**
** \brief Algebraic solver.
**
** Algebraic solver.
**/



#pragma once

#include "cvc4_private.h"
#include "theory/bv/bv_subtheory.h"

namespace CVC4 {
namespace theory {
namespace bv {

// TODO: move to util
class SubstitutionEx {
  struct SubstitutionElement {
    Node to;
    Node reason;
    SubstitutionElement()
      : to()
      , reason()
    {}
    
    SubstitutionElement(TNode t, TNode r)
      : to(t)
      , reason(r)
    {}
  };

  struct SubstitutionStackElement {
    TNode node;
    bool childrenAdded;
    SubstitutionStackElement(TNode n, bool ca = false)
      : node(n)
      , childrenAdded(ca)
    {}
  };

  typedef __gnu_cxx::hash_map<Node, SubstitutionElement, TNodeHashFunction> Substitutions;
  typedef __gnu_cxx::hash_map<Node, SubstitutionElement, TNodeHashFunction> SubstitutionsCache;

  Substitutions d_substitutions;
  SubstitutionsCache d_cache;
  bool d_cacheInvalid;

  Node getReason(TNode node) const;
  bool hasCache(TNode node) const;
  Node getCache(TNode node) const;
  void storeCache(TNode from, TNode to, Node rason);
  Node internalApply(TNode node);

public:
  SubstitutionEx();
  void addSubstitution(TNode from, TNode to, TNode reason);
  Node apply(TNode node);
  Node explain(TNode node) const;

};

class BVQuickCheck;

/**
 * AlgebraicSolver
 */
class AlgebraicSolver : public SubtheorySolver {
  typedef __gnu_cxx::hash_map<Node, Node, NodeHashFunction> NodeNodeMap;
  
  struct Statistics {
    IntStat d_numCallstoCheck;
    IntStat d_numSimplifiesToTrue;
    IntStat d_numSimplifiesToFalse;
    IntStat d_numUnsat;
    IntStat d_numSat;
    IntStat d_numUnknown;
    Statistics();
    ~Statistics();
  };

  
  BVQuickCheck* d_quickSolver;
  context::CDO<bool> d_isComplete;
  unsigned long d_budget;
  NodeNodeMap d_explanations;
  Statistics d_statistics;
  bool solve(TNode fact, SubstitutionEx& subst, TNode reason);
  bool quickCheck(std::vector<Node>& facts, SubstitutionEx& subst);
public:
  AlgebraicSolver(context::Context* c, TheoryBV* bv);
  ~AlgebraicSolver();

  void  preRegister(TNode node) {}
  bool  check(Theory::Effort e);
  void  explain(TNode literal, std::vector<TNode>& assumptions) {Unreachable("AlgebraicSolver does not propagate.\n");}
  EqualityStatus getEqualityStatus(TNode a, TNode b) { Unreachable();}
  void collectModelInfo(TheoryModel* m, bool fullModel) { Unreachable(); }
  Node getModelValue(TNode node) { Unreachable(); }
  bool isComplete();
};

}
}
}
