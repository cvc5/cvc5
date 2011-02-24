
#include "theory/arith/arith_priority_queue.h"

using namespace std;

using namespace CVC4;
using namespace CVC4::kind;

using namespace CVC4::theory;
using namespace CVC4::theory::arith;

ArithPriorityQueue::ArithPriorityQueue(ArithPartialModel& pm, const Tableau& tableau):
  d_partialModel(pm), d_tableau(tableau), d_usingGriggioRule(true), d_ZERO_DELTA(0,0)
{}

ArithVar ArithPriorityQueue::popInconsistentBasicVariable(){
  Debug("arith_update") << "popInconsistentBasicVariable()" << endl;

  if(usingGriggioRule()){
    while(!d_griggioRuleQueue.empty()){
      ArithVar var = d_griggioRuleQueue.front().variable();
      pop_heap(d_griggioRuleQueue.begin(), d_griggioRuleQueue.end());
      d_griggioRuleQueue.pop_back();
      Debug("arith_update") << "possiblyInconsistentGriggio var" << var << endl;
      if(basicAndInconsistent(var)){
        return var;
      }
    }
  }else{
    Debug("arith_update") << "possiblyInconsistent.size()"
                          << d_possiblyInconsistent.size() << endl;

    while(!d_possiblyInconsistent.empty()){
      ArithVar var = d_possiblyInconsistent.front();
      pop_heap(d_possiblyInconsistent.begin(), d_possiblyInconsistent.end(), std::greater<ArithVar>());
      d_possiblyInconsistent.pop_back();

      Debug("arith_update") << "possiblyInconsistent var" << var << endl;
      if(basicAndInconsistent(var)){
        return var;
      }
    }
  }
  return ARITHVAR_SENTINEL;
}

void ArithPriorityQueue::enqueueIfInconsistent(ArithVar basic){
  Assert(d_tableau.isBasic(basic));
  if(basicAndInconsistent(basic)){
    if( usingGriggioRule() ){
      const DeltaRational& beta = d_partialModel.getAssignment(basic);
      DeltaRational diff = d_partialModel.belowLowerBound(basic,beta,true) ?
        d_partialModel.getLowerBound(basic) - beta:
        beta - d_partialModel.getUpperBound(basic);

      Assert(d_ZERO_DELTA < diff);
      d_griggioRuleQueue.push_back(VarDRatPair(basic,diff));
      push_heap(d_griggioRuleQueue.begin(), d_griggioRuleQueue.end());

    }else{
      d_possiblyInconsistent.push_back(basic);
      push_heap(d_possiblyInconsistent.begin(), d_possiblyInconsistent.end(), std::greater<ArithVar>());
    }
  }
}

ArithPriorityQueue::GriggioPQueue::const_iterator ArithPriorityQueue::queueAsListBegin() const{
  Assert(usingGriggioRule());
  return d_griggioRuleQueue.begin();
}
ArithPriorityQueue::GriggioPQueue::const_iterator ArithPriorityQueue::queueAsListEnd() const{
  Assert(usingGriggioRule());
  return d_griggioRuleQueue.end();
}


void ArithPriorityQueue::useGriggioQueue(){
  Assert(!usingGriggioRule());
  Assert(d_possiblyInconsistent.empty());
  Assert(d_griggioRuleQueue.empty());
  d_usingGriggioRule = true;
}

void ArithPriorityQueue::useBlandQueue(){
  Assert(usingGriggioRule());
  Assert(d_possiblyInconsistent.empty());
  for(GriggioPQueue::const_iterator i = d_griggioRuleQueue.begin(), end = d_griggioRuleQueue.end(); i != end; ++i){
    ArithVar var = (*i).variable();
    if(basicAndInconsistent(var)){
      d_possiblyInconsistent.push_back(var);
    }
  }
  d_griggioRuleQueue.clear();
  make_heap(d_possiblyInconsistent.begin(), d_possiblyInconsistent.end(), std::greater<ArithVar>());
  d_usingGriggioRule = false;

  Assert(d_griggioRuleQueue.empty());
  Assert(!usingGriggioRule());
}


void ArithPriorityQueue::clear(){
  if(usingGriggioRule()  && !d_griggioRuleQueue.empty()){
    d_griggioRuleQueue.clear();
  }else if(!d_possiblyInconsistent.empty()) {
    d_possiblyInconsistent.clear();
  }
  Assert(d_possiblyInconsistent.empty());
  Assert(d_griggioRuleQueue.empty());
}
