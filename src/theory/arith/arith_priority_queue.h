/*********************                                                        */
/*! \file arith_priority_queue.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_PRIORITY_QUEUE_H
#define __CVC4__THEORY__ARITH__ARITH_PRIORITY_QUEUE_H

#include "theory/arith/arithvar.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/matrix.h"
#include "theory/arith/partial_model.h"

#include "util/statistics_registry.h"

#include <vector>

namespace CVC4 {
namespace theory {
namespace arith {


/**
 * The priority queue has 3 different modes of operation:
 * - Collection
 *   This passively collects arithmetic variables that may be inconsistent.
 *   This does not maintain any heap structure.
 *   dequeueInconsistentBasicVariable() does not work in this mode!
 *   Entering this mode requires the queue to be empty.
 *
 * - Difference Queue
 *   This mode uses the difference between a variables and its bound
 *   to determine which to dequeue first.
 *
 * - Variable Order Queue
 *   This mode uses the variable order to determine which ArithVar is dequeued first.
 *
 * The transitions between the modes of operation are:
 *  Collection => Difference Queue
 *  Difference Queue => Variable Order Queue
 *  Difference Queue => Collection (queue must be empty!)
 *  Variable Order Queue => Collection (queue must be empty!)
 *
 * The queue begins in Collection mode.
 */
class ArithPriorityQueue {
public:
  enum PivotRule {MINIMUM, BREAK_TIES, MAXIMUM};

private:
  class VarDRatPair {
  private:
    ArithVar d_variable;
    DeltaRational d_orderBy;
  public:
    VarDRatPair(ArithVar var, const DeltaRational& dr):
      d_variable(var), d_orderBy(dr)
    { }

    ArithVar variable() const {
      return d_variable;
    }

    static bool minimumRule(const VarDRatPair& a, const VarDRatPair& b){
      return a.d_orderBy > b.d_orderBy;
    }
    static bool maximumRule(const VarDRatPair& a, const VarDRatPair& b){
      return a.d_orderBy < b.d_orderBy;
    }

    static bool breakTiesRules(const VarDRatPair& a, const VarDRatPair& b){
      const Rational& nonInfA = a.d_orderBy.getNoninfinitesimalPart();
      const Rational& nonInfB = b.d_orderBy.getNoninfinitesimalPart();
      int cmpNonInf = nonInfA.cmp(nonInfB);
      if(cmpNonInf == 0){
        const Rational& infA = a.d_orderBy.getInfinitesimalPart();
        const Rational& infB = b.d_orderBy.getInfinitesimalPart();
        int cmpInf = infA.cmp(infB);
        if(cmpInf == 0){
          return a.d_variable > b.d_variable;
        }else{
          return cmpInf > 0;
        }
      }else{
        return cmpNonInf > 0;
      }

      return a.d_orderBy > b.d_orderBy;
    }
  };

  typedef std::vector<VarDRatPair> DifferenceArray;
  typedef std::vector<ArithVar> ArithVarArray;

  PivotRule d_pivotRule;

  /**
   * An unordered array with no heap structure for use during collection mode.
   */
  ArithVarArray d_candidates;

  /**
   * Priority Queue of the basic variables that may be inconsistent.
   * Variables are ordered according to which violates its bound the most.
   * This is a heuristic and makes no guarantees to terminate!
   * This heuristic comes from Alberto Griggio's thesis.
   */
  DifferenceArray d_diffQueue;

  /**
   * Priority Queue of the basic variables that may be inconsistent.
   *
   * This is required to contain at least 1 instance of every inconsistent
   * basic variable. This is only required to be a superset though so its
   * contents must be checked to still be basic and inconsistent.
   *
   * This is also required to agree with the row on variable order for termination.
   * Effectively this means that this must be a min-heap.
   */
  ArithVarArray d_varOrderQueue;

  /**
   * A superset of the basic variables that may be inconsistent.
   * This is empty during DiffOrderMode, and otherwise it is the same set as candidates
   * or varOrderQueue.
   */
  DenseSet d_varSet;

  /**
   * Reference to the arithmetic partial model for checking if a variable
   * is consistent with its upper and lower bounds.
   */
  ArithPartialModel& d_partialModel;

  /** Reference to the Tableau for checking if a variable is basic. */
  const Tableau& d_tableau;

  enum Mode {Collection, Difference, VariableOrder};
  /**
   * Controls which priority queue is in use.
   * If true, d_griggioRuleQueue is used.
   * If false, d_possiblyInconsistent is used.
   */
  Mode d_modeInUse;

  /** Storage of Delta Rational 0 */
  DeltaRational d_ZERO_DELTA;

  VarDRatPair computeDiff(ArithVar basic);

public:

  ArithPriorityQueue(ArithPartialModel& pm, const Tableau& tableau);

  /** precondition: !inDifferenceMode() */
  void setPivotRule(PivotRule rule);

  ArithVar dequeueInconsistentBasicVariable();

  void enqueueIfInconsistent(ArithVar basic);

  inline bool basicAndInconsistent(ArithVar var) const{
    return d_tableau.isBasic(var)
      && !d_partialModel.assignmentIsConsistent(var) ;
  }

  void transitionToDifferenceMode();
  void transitionToVariableOrderMode();
  void transitionToCollectionMode();

  inline bool inDifferenceMode() const{
    return d_modeInUse == Difference;
  }
  inline bool inCollectionMode() const{
    return d_modeInUse == Collection;
  }
  inline bool inVariableOrderMode() const{
    return d_modeInUse == VariableOrder;
  }

  inline bool empty() const{
    switch(d_modeInUse){
    case Collection:    return d_candidates.empty();
    case VariableOrder: return d_varOrderQueue.empty();
    case Difference:    return d_diffQueue.empty();
    default: Unreachable();
    }
  }

  inline size_t size() const {
    switch(d_modeInUse){
    case Collection:    return d_candidates.size();
    case VariableOrder: return d_varOrderQueue.size();
    case Difference:    return d_diffQueue.size();
    default: Unreachable();
    }
  }

  /** Clears the queue. */
  void clear();


  /**
   * Reduces the queue to only contain the subset that is still basic
   * and inconsistent.
   *Currently, O(n log n) for an easy obviously correct implementation in all modes..
   */
  void reduce();

  bool collectionModeContains(ArithVar v) const {
    Assert(inCollectionMode());
    return d_varSet.isMember(v);
  }

  class const_iterator {
  private:
    Mode d_mode;
    ArithVarArray::const_iterator d_avIter;
    DifferenceArray::const_iterator d_diffIter;
  public:
    const_iterator(Mode m,
                   ArithVarArray::const_iterator av,
                   DifferenceArray::const_iterator diff):
      d_mode(m), d_avIter(av), d_diffIter(diff)
    {}
    const_iterator(const const_iterator& other):
      d_mode(other.d_mode), d_avIter(other.d_avIter), d_diffIter(other.d_diffIter)
    {}
    bool operator==(const const_iterator& other) const{
      AlwaysAssert(d_mode == other.d_mode);
      switch(d_mode){
      case Collection:
      case VariableOrder:
        return d_avIter == other.d_avIter;
      case Difference:
        return d_diffIter == other.d_diffIter;
      default:
        Unreachable();
      }
    }
    bool operator!=(const const_iterator& other) const{
      return !(*this == other);
    }
    const_iterator& operator++(){
      switch(d_mode){
      case Collection:
      case VariableOrder:
        ++d_avIter;
        break;
      case Difference:
        ++d_diffIter;
        break;
      default:
        Unreachable();
      }
      return *this;
    }

    ArithVar operator*() const{
      switch(d_mode){
      case Collection:
      case VariableOrder:
        return *d_avIter;
      case Difference:
        return (*d_diffIter).variable();
      default:
        Unreachable();
      }
    }
  };

  const_iterator begin() const{
    switch(d_modeInUse){
      case Collection:
        return const_iterator(Collection, d_candidates.begin(), d_diffQueue.end());
      case VariableOrder:
        return const_iterator(VariableOrder, d_varOrderQueue.begin(), d_diffQueue.end());
      case Difference:
        return const_iterator(Difference, d_varOrderQueue.end(), d_diffQueue.begin());
      default:
        Unreachable();
    }
  }

  const_iterator end() const{
    switch(d_modeInUse){
      case Collection:
        return const_iterator(Collection, d_candidates.end(), d_diffQueue.end());
      case VariableOrder:
        return const_iterator(VariableOrder, d_varOrderQueue.end(), d_diffQueue.end());
      case Difference:
        return const_iterator(Difference, d_varOrderQueue.end(), d_diffQueue.end());
      default:
        Unreachable();
    }
  }

private:
  class Statistics {
  public:
    IntStat d_enqueues;
    IntStat d_enqueuesCollection;
    IntStat d_enqueuesDiffMode;
    IntStat d_enqueuesVarOrderMode;

    IntStat d_enqueuesCollectionDuplicates;
    IntStat d_enqueuesVarOrderModeDuplicates;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;
};

std::ostream& operator<<(std::ostream& out, ArithPriorityQueue::PivotRule rule);

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH_PRIORITY_QUEUE_H */
