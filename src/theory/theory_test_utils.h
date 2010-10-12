/*********************                                                        */
/*! \file theory_test_utils.h
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



#include "cvc4_public.h"


#ifndef __CVC4__THEORY__THEORY_TEST_UTILS_H
#define __CVC4__THEORY__ITHEORY_TEST_UTILS_H

#include "util/Assert.h"
#include "expr/node.h"
#include "theory/output_channel.h"
#include "theory/interrupted.h"

#include <vector>
#include <utility>
#include <iostream>

namespace CVC4 {

namespace theory {

/**
 * Very basic OutputChannel for testing simple Theory Behaviour.
 * Stores a call sequence for the output channel
 */
enum OutputChannelCallType {
  CONFLICT,
  PROPAGATE,
  AUG_LEMMA,
  LEMMA,
  EXPLANATION
};

}/* CVC4::theory namespace */

inline std::ostream& operator<<(std::ostream& out, theory::OutputChannelCallType type) {
  switch(type) {
  case theory::CONFLICT: return out << "CONFLICT";
  case theory::PROPAGATE: return out << "PROPAGATE";
  case theory::AUG_LEMMA: return out << "AUG_LEMMA";
  case theory::LEMMA: return out << "LEMMA";
  case theory::EXPLANATION: return out << "EXPLANATION";
  default: return out << "UNDEFINED-OutputChannelCallType!" << int(type);
  }
}

namespace theory {

class TestOutputChannel : public theory::OutputChannel {
public:
  std::vector< std::pair<enum OutputChannelCallType, Node> > d_callHistory;

  TestOutputChannel() {}

  ~TestOutputChannel() {}

  void safePoint()  throw(Interrupted, AssertionException) {}

  void conflict(TNode n, bool safe = false)
    throw(Interrupted, AssertionException) {
    push(CONFLICT, n);
  }

  void propagate(TNode n, bool safe = false)
    throw(Interrupted, AssertionException) {
    push(PROPAGATE, n);
  }

  void lemma(TNode n, bool safe = false) throw(Interrupted, AssertionException) {
    push(LEMMA, n);
  }
  void augmentingLemma(TNode n, bool safe = false) throw(Interrupted, AssertionException){
    push(AUG_LEMMA, n);
  }
  void explanation(TNode n, bool safe = false)  throw(Interrupted, AssertionException) {
    push(EXPLANATION, n);
  }

  void setIncomplete() throw(Interrupted, AssertionException) {}

  void clear() {
    d_callHistory.clear();
  }

  Node getIthNode(int i) {
    Node tmp = (d_callHistory[i]).second;
    return tmp;
  }

  OutputChannelCallType getIthCallType(int i) {
    return (d_callHistory[i]).first;
  }

  unsigned getNumCalls() {
    return d_callHistory.size();
  }

private:
  void push(OutputChannelCallType call, TNode n) {
    d_callHistory.push_back(std::make_pair(call,n));
  }
};/* class TestOutputChannel */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__THEORY_TEST_UTILS_H */
