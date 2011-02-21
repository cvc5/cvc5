
#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_PRIORITY_QUEUE_H
#define __CVC4__THEORY__ARITH__ARITH_PRIORITY_QUEUE_H

#include "theory/arith/arith_utilities.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/tableau.h"
#include "theory/arith/partial_model.h"

#include <queue>

namespace CVC4 {
namespace theory {
namespace arith {

typedef std::pair<ArithVar, DeltaRational> VarDRatPair;

struct VarDRatPairCompare{
  inline bool operator()(const VarDRatPair& a, const VarDRatPair& b){
    return a.second > b.second;
  }
};

typedef std::priority_queue<VarDRatPair, std::vector<VarDRatPair>, VarDRatPairCompare> GriggioPQueue;

typedef std::priority_queue<ArithVar, vector<ArithVar>, std::greater<ArithVar> > PQueue;


class ArithPriorityQueue {
private:
  /**
   * Priority Queue of the basic variables that may be inconsistent.
   * Variables are ordered according to which violates its bound the most.
   * This is a hueristic and makes no guarentees to terminate!
   * This heuristic comes from Alberto Griggio's thesis.
   */
  GriggioPQueue d_griggioRuleQueue;

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
  PQueue d_possiblyInconsistent;

  /**
   * Reference to the arithmetic partial model for checking if a variable
   * is consistent with its upper and lower bounds.
   */
  ArithPartialModel& d_partialModel;

  /** Reference to the Tableau for checking if a variable is basic. */
  const Tableau& d_tableau;

  /**
   * Controls which priority queue is in use.
   * If true, d_griggioRuleQueue is used.
   * If false, d_possiblyInconsistent is used.
   */
  bool d_usingGriggioRule;

public:
  ArithPriorityQueue(ArithPartialModel& pm, const Tableau& tableau);

  ArithVar popInconsistentBasicVariable();

  void enqueueIfInconsistent(ArithVar basic);

  void enqueueTrustedVector(const vector<VarDRatPair>& trusted);

  void dumpQueueIntoVector(vector<VarDRatPair>& target);

  inline bool basicAndInconsistent(ArithVar var) const{
    return d_tableau.isBasic(var)
      && !d_partialModel.assignmentIsConsistent(var) ;
  }

  void useGriggioQueue();

  void useBlandQueue();

  inline bool usingGriggioRule() const{
    return d_usingGriggioRule;
  }

  inline bool empty() const{
    if(usingGriggioRule()){
      return d_griggioRuleQueue.empty();
    }else{
      return d_possiblyInconsistent.empty();
    }
  }

  inline size_t size() const {
    if(usingGriggioRule()){
      return d_griggioRuleQueue.size();
    }else{
      return d_possiblyInconsistent.size();
    }
  }

  void clear();
};


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH_PRIORITY_QUEUE_H */
