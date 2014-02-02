/*********************                                                        */
/*! \file bv_quick_check.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Sandboxed sat solver for bv quickchecks.
 **
 ** Sandboxed sat solver for bv quickchecks.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BV_QUICK_CHECK_H
#define __CVC4__BV_QUICK_CHECK_H

#include <vector>
#include <ext/hash_map>

#include "expr/node.h"
#include "context/cdo.h"
#include "prop/sat_solver_types.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace bv {

typedef __gnu_cxx::hash_set<Node, NodeHashFunction> NodeSet;
typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction> TNodeSet;

class TLazyBitblaster; 

class BVQuickCheck {
  context::Context* d_ctx;
  TLazyBitblaster* d_bitblaster;
  Node d_conflict;
  context::CDO<bool> d_inConflict;

  void setConflict();

public:
  BVQuickCheck(const std::string& name);
  ~BVQuickCheck();
  bool inConflict();
  Node getConflict() { return d_conflict; }
  prop::SatValue checkSat(std::vector<Node>& assumptions, unsigned long budget);
  prop::SatValue checkSat(unsigned long budget);
  
  // returns false if the assertion lead to a conflict
  bool addAssertion(TNode assumptions);

  void push();
  void pop();
  void reset(); 
  void popToZero();
  uint64_t computeAtomWeight(TNode node, NodeSet& seen);
};


class QuickXPlain {
  struct Statistics {
    TimerStat d_xplainTime;
    IntStat d_numSolved;
    IntStat d_numUnknown;
    AverageStat d_avgMinimizationRatio;
    Statistics(const std::string&);
    ~Statistics();
  };
  BVQuickCheck* d_solver;
  unsigned long d_budget;
  unsigned d_numCalled;
  double d_minRatioSum;
  
  Statistics d_statistics;
  unsigned selectUnsatCore(unsigned low, unsigned high,
                                        std::vector<TNode>& conflict);
  void minimizeConflictInternal(unsigned low, unsigned high,
                                std::vector<TNode>& conflict,
                                std::vector<TNode>& new_conflict);


public:
  QuickXPlain(const std::string& name, BVQuickCheck* solver, unsigned long budged = 1500);
  ~QuickXPlain();
  Node minimizeConflict(TNode conflict); 
  void setBudget(); 
};

} /* bv namespace */
} /* theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__BV_QUICK_CHECK_H */
