

#include "cvc4_public.h"


#ifndef __CVC4__THEORY__THEORY_TEST_UTILS_H
#define __CVC4__THEORY__ITHEORY_TEST_UTILS_H

#include "util/Assert.h"
#include "expr/node.h"
#include "theory/output_channel.h"
#include "theory/interrupted.h"

#include <vector>

namespace CVC4{

namespace theory {

/**
 * Very basic OutputChannel for testing simple Theory Behaviour.
 * Stores a call sequence for the output channel
 */
enum OutputChannelCallType { CONFLICT, PROPOGATE, AUG_LEMMA, LEMMA, EXPLANATION };


class TestOutputChannel : public theory::OutputChannel {
public:
  std::vector< pair<enum OutputChannelCallType, Node> > d_callHistory;

  TestOutputChannel() {}

  ~TestOutputChannel() {}

  void safePoint()  throw(Interrupted, AssertionException) {}

  void conflict(TNode n, bool safe = false)  throw(Interrupted, AssertionException) {
    push(CONFLICT, n);
  }

  void propagate(TNode n, bool safe = false)  throw(Interrupted, AssertionException) {
    push(PROPOGATE, n);
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
    d_callHistory.push_back(make_pair(call,n));
  }
};/* class TestOutputChannel */

}/* namespace theory */
}/* namespace CVC4 */

#endif /* __CVC4__THEORY__THEORY_TEST_UTILS_H */
