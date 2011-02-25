
#include "theory/arith/arith_priority_queue.h"

#include <algorithm>

using namespace std;

using namespace CVC4;
using namespace CVC4::kind;

using namespace CVC4::theory;
using namespace CVC4::theory::arith;

ArithPriorityQueue::ArithPriorityQueue(ArithPartialModel& pm, const Tableau& tableau):
  d_partialModel(pm), d_tableau(tableau), d_modeInUse(Collection), d_ZERO_DELTA(0,0)
{}

ArithVar ArithPriorityQueue::dequeueInconsistentBasicVariable(){
  AlwaysAssert(!inCollectionMode());

  Debug("arith_update") << "dequeueInconsistentBasicVariable()" << endl;

  if(inDifferenceMode()){
    while(!d_diffQueue.empty()){
      ArithVar var = d_diffQueue.front().variable();
      pop_heap(d_diffQueue.begin(), d_diffQueue.end());
      d_diffQueue.pop_back();
      Debug("arith_update") << "possiblyInconsistentGriggio var" << var << endl;
      if(basicAndInconsistent(var)){
        return var;
      }
    }
  }else{
    Debug("arith_update") << "possiblyInconsistent.size()"
                          << d_varOrderQueue.size() << endl;

    while(!d_varOrderQueue.empty()){
      ArithVar var = d_varOrderQueue.front();
      pop_heap(d_varOrderQueue.begin(), d_varOrderQueue.end(), std::greater<ArithVar>());
      d_varOrderQueue.pop_back();

      Debug("arith_update") << "possiblyInconsistent var" << var << endl;
      if(basicAndInconsistent(var)){
        return var;
      }
    }
  }
  return ARITHVAR_SENTINEL;
}

ArithPriorityQueue::VarDRatPair ArithPriorityQueue::computeDiff(ArithVar basic){
  Assert(basicAndInconsistent(basic));
  const DeltaRational& beta = d_partialModel.getAssignment(basic);
  DeltaRational diff = d_partialModel.belowLowerBound(basic,beta,true) ?
    d_partialModel.getLowerBound(basic) - beta:
    beta - d_partialModel.getUpperBound(basic);

  Assert(d_ZERO_DELTA < diff);
  return VarDRatPair(basic,diff);
}

void ArithPriorityQueue::enqueueIfInconsistent(ArithVar basic){
  Assert(d_tableau.isBasic(basic));

  if(basicAndInconsistent(basic)){
    switch(d_modeInUse){
    case Collection:
      d_candidates.push_back(basic);
      break;
    case VariableOrder:
      d_varOrderQueue.push_back(basic);
      push_heap(d_varOrderQueue.begin(), d_varOrderQueue.end(), std::greater<ArithVar>());
      break;
    case Difference:
      d_diffQueue.push_back(computeDiff(basic));
      push_heap(d_diffQueue.begin(), d_diffQueue.end());
      break;
    default:
      Unreachable();
    }
  }
}

void ArithPriorityQueue::transitionToDifferenceMode() {
  Assert(inCollectionMode());
  Assert(d_varOrderQueue.empty());
  Assert(d_diffQueue.empty());

  Debug("arith::priorityqueue") << "transitionToDifferenceMode()" << endl;

  ArithVarArray::const_iterator i = d_candidates.begin(), end = d_candidates.end();
  for(; i != end; ++i){
    ArithVar var = *i;
    if(basicAndInconsistent(var)){
      d_diffQueue.push_back(computeDiff(var));
    }
  }
  make_heap(d_diffQueue.begin(), d_diffQueue.end());
  d_candidates.clear();
  d_modeInUse = Difference;

  Assert(inDifferenceMode());
  Assert(d_varOrderQueue.empty());
  Assert(d_candidates.empty());
}

void ArithPriorityQueue::transitionToVariableOrderMode() {
  Assert(inDifferenceMode());
  Assert(d_varOrderQueue.empty());
  Assert(d_candidates.empty());

  Debug("arith::priorityqueue") << "transitionToVariableOrderMode()" << endl;

  DifferenceArray::const_iterator i = d_diffQueue.begin(), end = d_diffQueue.end();
  for(; i != end; ++i){
    ArithVar var = (*i).variable();
    if(basicAndInconsistent(var)){
      d_varOrderQueue.push_back(var);
    }
  }
  make_heap(d_varOrderQueue.begin(), d_varOrderQueue.end(), std::greater<ArithVar>());
  d_diffQueue.clear();
  d_modeInUse = VariableOrder;

  Assert(inVariableOrderMode());
  Assert(d_diffQueue.empty());
  Assert(d_candidates.empty());
}

void ArithPriorityQueue::transitionToCollectionMode() {
  Assert(inDifferenceMode() || inVariableOrderMode());
  Assert(d_diffQueue.empty());
  Assert(d_candidates.empty());
  Assert(d_varOrderQueue.empty());

  Debug("arith::priorityqueue") << "transitionToCollectionMode()" << endl;

  d_modeInUse = Collection;
}

void ArithPriorityQueue::clear(){
  switch(d_modeInUse){
  case Collection:
    d_candidates.clear();
    break;
  case VariableOrder:
    if(!d_varOrderQueue.empty()) {
      d_varOrderQueue.clear();
    }
    break;
  case Difference:
    if(!d_diffQueue.empty()){
      d_diffQueue.clear();
    }
    break;
  default:
    Unreachable();
  }
  Assert(d_candidates.empty());
  Assert(d_varOrderQueue.empty());
  Assert(d_diffQueue.empty());
}
