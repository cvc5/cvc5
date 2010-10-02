/*********************                                                        */
/*! \file arith_activity.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_ACTIVITY_H
#define __CVC4__THEORY__ARITH__ARITH_ACTIVITY_H

#include "expr/node.h"
#include "expr/attribute.h"

namespace CVC4 {
namespace theory {
namespace arith {


class ActivityMonitor {
private:
  std::vector<uint64_t> d_activities;

public:
  const static uint64_t ACTIVITY_THRESHOLD = 100;

  ActivityMonitor() : d_activities() {}

  void resetActivity(ArithVar var){
    d_activities[var] = 0;
  }

  void initActivity(ArithVar var){
    Assert(var == d_activities.size());
    d_activities.push_back(0);
  }

  uint64_t getActivity(ArithVar var) const{
    return d_activities[var];
  }

  inline void increaseActivity(ArithVar var, uint64_t x){
    d_activities[var] += x;
  }

};


}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */


#endif
