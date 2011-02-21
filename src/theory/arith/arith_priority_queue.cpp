
#include "theory/arith/arith_priority_queue.h"

using namespace std;

using namespace CVC4;
using namespace CVC4::kind;

using namespace CVC4::theory;
using namespace CVC4::theory::arith;

ArithPriorityQueue::ArithPriorityQueue(ArithPartialModel& pm, const Tableau& tableau):
  d_partialModel(pm), d_tableau(tableau), d_usingGriggioRule(true)
{}

ArithVar ArithPriorityQueue::popInconsistentBasicVariable(){
  Debug("arith_update") << "popInconsistentBasicVariable()" << endl;

  if(usingGriggioRule()){
    while(!d_griggioRuleQueue.empty()){
      ArithVar var = d_griggioRuleQueue.top().first;
      d_griggioRuleQueue.pop();
      Debug("arith_update") << "possiblyInconsistentGriggio var" << var << endl;
      if(basicAndInconsistent(var)){
        return var;
      }
    }
  }else{
    Debug("arith_update") << "possiblyInconsistent.size()"
                          << d_possiblyInconsistent.size() << endl;

    while(!d_possiblyInconsistent.empty()){
      ArithVar var = d_possiblyInconsistent.top();
      d_possiblyInconsistent.pop();
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
      d_griggioRuleQueue.push(make_pair(basic,diff));
    }else{
      d_possiblyInconsistent.push(basic);
    }
  }
}


void ArithPriorityQueue::enqueueTrustedVector(const vector<VarDRatPair>& trusted){
  Assert(usingGriggioRule());
  Assert(empty());

  d_griggioRuleQueue = GriggioPQueue(trusted.begin(), trusted.end());
  Assert(size() == trusted.size());
}


void ArithPriorityQueue::dumpQueueIntoVector(vector<VarDRatPair>& target){
  Assert(usingGriggioRule());
  while( !d_griggioRuleQueue.empty()){
    ArithVar var = d_griggioRuleQueue.top().first;
    if(basicAndInconsistent(var)){
      target.push_back( d_griggioRuleQueue.top());
    }
    d_griggioRuleQueue.pop();
  }
}


void ArithPriorityQueue::useGriggioQueue(){
  Assert(!usingGriggioRule());
  Assert(d_possiblyInconsistent.empty());
  Assert(d_griggioRuleQueue.empty());
  d_usingGriggioRule = true;
}

void ArithPriorityQueue::useBlandQueue(){
  Assert(usingGriggioRule());
  while(!d_griggioRuleQueue.empty()){
    ArithVar var = d_griggioRuleQueue.top().first;
    if(basicAndInconsistent(var)){
      d_possiblyInconsistent.push(var);
    }
    d_griggioRuleQueue.pop();
  }
  d_usingGriggioRule = false;

  Assert(d_griggioRuleQueue.empty());
  Assert(!usingGriggioRule());
}


void ArithPriorityQueue::clear(){
  if(usingGriggioRule()  && !d_griggioRuleQueue.empty()){
    d_griggioRuleQueue = GriggioPQueue();
  }else if(!d_possiblyInconsistent.empty()) {
    d_possiblyInconsistent = PQueue();
  }
  Assert(d_possiblyInconsistent.empty());
  Assert(d_griggioRuleQueue.empty());
}
