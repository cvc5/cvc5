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
#include "theory/substitutions.h"

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

  typedef __gnu_cxx::hash_map<Node, SubstitutionElement, NodeHashFunction> Substitutions;
  typedef __gnu_cxx::hash_map<Node, SubstitutionElement, NodeHashFunction> SubstitutionsCache;

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


struct WorklistElement {
  Node node;
  unsigned id;
  WorklistElement(Node n, unsigned i) : node(n), id(i) {}
  WorklistElement() : node(), id(-1) {}
}; 


typedef __gnu_cxx::hash_map<Node, Node, NodeHashFunction> NodeNodeMap;
typedef __gnu_cxx::hash_map<Node, unsigned, NodeHashFunction> NodeIdMap;
typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction> TNodeSet;


class ExtractSkolemizer {
  struct Extract {
    unsigned high;
    unsigned low;
    Extract(unsigned h, unsigned l) : high(h), low(l) {}
  };
    
  struct ExtractList {
    std::vector<Extract> extracts;
    bool overlap;
    ExtractList() : extracts(), overlap(false) {}
    void addExtract(Extract& e); 
  };
  typedef   __gnu_cxx::hash_map<Node, ExtractList, NodeHashFunction> VarExtractMap;
  
  VarExtractMap d_varToExtract;
  theory::SubstitutionMap d_skolemSubst;
  theory::SubstitutionMap d_skolemSubstRev;

  void storeSkolem(TNode node, TNode skolem);
  void storeExtract(TNode var, unsigned high, unsigned low);
  void collectExtracts(TNode node, TNodeSet& seen);
  Node skolemize(TNode);
  Node unSkolemize(TNode);

  Node mkSkolem(Node node);
public:
  ExtractSkolemizer(context::Context* ctx); 
  void skolemize(std::vector<WorklistElement>&);
  void unSkolemize(std::vector<WorklistElement>&);
}; 

class BVQuickCheck;
class QuickXPlain;
/**
 * AlgebraicSolver
 */
class AlgebraicSolver : public SubtheorySolver {
  
  struct Statistics {
    IntStat d_numCallstoCheck;
    IntStat d_numSimplifiesToTrue;
    IntStat d_numSimplifiesToFalse;
    IntStat d_numUnsat;
    IntStat d_numSat;
    IntStat d_numUnknown;
    TimerStat d_solveTime;
    BackedStat<double> d_useHeuristic;
    Statistics();
    ~Statistics();
  };

  BVQuickCheck* d_quickSolver;
  context::CDO<bool> d_isComplete;
  context::CDO<bool> d_isDifficult;
  
  unsigned long d_budget;
  std::vector<Node> d_explanations;
  TNodeSet d_inputAssertions;
  NodeIdMap d_ids;
  double d_numSolved;
  double d_numCalls;

  context::Context* d_ctx;
  QuickXPlain* d_quickXplain;
  
  Statistics d_statistics;

  bool solve(TNode fact, TNode reason, SubstitutionEx& subst);
  bool quickCheck(std::vector<Node>& facts, SubstitutionEx& subst);
  bool useHeuristic();
  void setConflict(TNode conflict);
  bool isSubstitutableIn(TNode node, TNode in);
  void processAssertions(std::vector<WorklistElement>& worklist, SubstitutionEx& subst);
  bool checkExplanation(TNode expl);
  void storeExplanation(TNode expl);
  void storeExplanation(unsigned id, TNode expl); 
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
  virtual void assertFact(TNode fact);
};

}
}
}
