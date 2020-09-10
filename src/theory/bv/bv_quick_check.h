/*********************                                                        */
/*! \file bv_quick_check.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sandboxed sat solver for bv quickchecks.
 **
 ** Sandboxed sat solver for bv quickchecks.
 **/

#include "cvc4_private.h"

#ifndef CVC4__BV_QUICK_CHECK_H
#define CVC4__BV_QUICK_CHECK_H

#include <unordered_set>
#include <vector>

#include "context/cdo.h"
#include "expr/node.h"
#include "prop/sat_solver_types.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {

class TheoryModel;

namespace bv {

class TLazyBitblaster;
class BVSolverLazy;

class BVQuickCheck
{
  context::Context d_ctx;
  std::unique_ptr<TLazyBitblaster> d_bitblaster;
  Node d_conflict;
  context::CDO<bool> d_inConflict;
  void setConflict();

 public:
  BVQuickCheck(const std::string& name, theory::bv::BVSolverLazy* bv);
  ~BVQuickCheck();
  bool inConflict();
  Node getConflict() { return d_conflict; }
  /**
   * Checks the satisfiability for a given set of assumptions.
   *
   * @param assumptions literals assumed true
   * @param budget max number of conflicts
   *
   * @return
   */
  prop::SatValue checkSat(std::vector<Node>& assumptions, unsigned long budget);
  /**
   * Checks the satisfiability of given assertions.
   *
   * @param budget max number of conflicts
   *
   * @return
   */
  prop::SatValue checkSat(unsigned long budget);

  /**
   * Convert to CNF and assert the given literal.
   *
   * @param assumption bv literal
   *
   * @return false if a conflict has been found via bcp.
   */
  bool addAssertion(TNode assumption);

  void push();
  void pop();
  void popToZero();
  /**
   * Deletes the SAT solver and CNF stream, but maintains the
   * bit-blasting term cache.
   *
   */
  void clearSolver();

  /**
   * Computes the size of the circuit required to bit-blast
   * atom, by not recounting the nodes in seen.
   *
   * @param node
   * @param seen
   *
   * @return
   */
  uint64_t computeAtomWeight(TNode atom, NodeSet& seen);
  bool collectModelValues(theory::TheoryModel* model,
                          const std::set<Node>& termSet);

  typedef std::unordered_set<TNode, TNodeHashFunction>::const_iterator
      vars_iterator;
  vars_iterator beginVars();
  vars_iterator endVars();

  Node getVarValue(TNode var, bool fullModel);
};

class QuickXPlain
{
  struct Statistics
  {
    TimerStat d_xplainTime;
    IntStat d_numSolved;
    IntStat d_numUnknown;
    IntStat d_numUnknownWasUnsat;
    IntStat d_numConflictsMinimized;
    IntStat d_finalPeriod;
    AverageStat d_avgMinimizationRatio;
    Statistics(const std::string& name);
    ~Statistics();
  };
  BVQuickCheck* d_solver;
  unsigned long d_budget;

  // crazy heuristic variables
  unsigned d_numCalled;  // number of times called
  double d_minRatioSum;  // sum of minimization ratio for computing average min
                         // ratio
  unsigned d_numConflicts;  // number of conflicts (including when minimization
                            // not applied)
  // unsigned d_period; // after how many conflicts to try minimizing again

  // double d_thresh; // if minimization ratio is less, increase period
  // double d_hardThresh; // decrease period if minimization ratio is greater
  // than this

  Statistics d_statistics;
  /**
   * Uses solve with assumptions unsat core feature to
   * further minimize a conflict. The minimized conflict
   * will be between low and the returned value in conflict.
   *
   * @param low
   * @param high
   * @param conflict
   *
   * @return
   */
  unsigned selectUnsatCore(unsigned low,
                           unsigned high,
                           std::vector<TNode>& conflict);
  /**
   * Internal conflict  minimization, attempts to minimize
   * literals in conflict between low and high and adds the
   * result in new_conflict.
   *
   * @param low
   * @param high
   * @param conflict
   * @param new_conflict
   */
  void minimizeConflictInternal(unsigned low,
                                unsigned high,
                                std::vector<TNode>& conflict,
                                std::vector<TNode>& new_conflict);

  bool useHeuristic();

 public:
  QuickXPlain(const std::string& name,
              BVQuickCheck* solver,
              unsigned long budged = 10000);
  ~QuickXPlain();
  Node minimizeConflict(TNode conflict);
};

}  // namespace bv
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__BV_QUICK_CHECK_H */
