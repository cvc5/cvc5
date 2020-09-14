/*********************                                                        */
/*! \file theory_test_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common utilities for testing theories
 **
 ** Common utilities for testing theories.
 **/

#include "cvc4_public.h"

#ifndef CVC4__THEORY__THEORY_TEST_UTILS_H
#define CVC4__THEORY__THEORY_TEST_UTILS_H

#include <iostream>
#include <memory>
#include <utility>
#include <vector>

#include "expr/node.h"
#include "theory/interrupted.h"
#include "theory/output_channel.h"
#include "util/resource_manager.h"
#include "util/unsafe_interrupt_exception.h"

namespace CVC4 {
namespace theory {

/**
 * Very basic OutputChannel for testing simple Theory Behaviour.
 * Stores a call sequence for the output channel
 */
enum OutputChannelCallType {
  CONFLICT,
  PROPAGATE,
  PROPAGATE_AS_DECISION,
  AUG_LEMMA,
  LEMMA,
  EXPLANATION
};/* enum OutputChannelCallType */

}/* CVC4::theory namespace */

inline std::ostream& operator<<(std::ostream& out, theory::OutputChannelCallType type) {
  switch(type) {
  case theory::CONFLICT: return out << "CONFLICT";
  case theory::PROPAGATE: return out << "PROPAGATE";
  case theory::PROPAGATE_AS_DECISION: return out << "PROPAGATE_AS_DECISION";
  case theory::AUG_LEMMA: return out << "AUG_LEMMA";
  case theory::LEMMA: return out << "LEMMA";
  case theory::EXPLANATION: return out << "EXPLANATION";
  default: return out << "UNDEFINED-OutputChannelCallType!" << int(type);
  }
}

namespace theory {

class TestOutputChannel : public theory::OutputChannel {
public:
  TestOutputChannel() {}
  ~TestOutputChannel() override {}

  void safePoint(ResourceManager::Resource r) override {}
  void conflict(TNode n) override { push(CONFLICT, n); }

  bool propagate(TNode n) override {
    push(PROPAGATE, n);
    return true;
  }

  LemmaStatus lemma(TNode n, LemmaProperty p) override
  {
    push(LEMMA, n);
    return LemmaStatus(Node::null(), 0);
  }

  void requirePhase(TNode, bool) override {}
  void setIncomplete() override {}
  void handleUserAttribute(const char* attr, theory::Theory* t) override {}

  LemmaStatus splitLemma(TNode n, bool removable = false) override {
    push(LEMMA, n);
    return LemmaStatus(Node::null(), 0);
  }

  void clear() { d_callHistory.clear(); }

  Node getIthNode(int i) const {
    Node tmp = (d_callHistory[i]).second;
    return tmp;
  }

  OutputChannelCallType getIthCallType(int i) const {
    return (d_callHistory[i]).first;
  }

  unsigned getNumCalls() const { return d_callHistory.size(); }

  void printIth(std::ostream& os, int i) const {
    os << "[TestOutputChannel " << i;
    os << " " << getIthCallType(i);
    os << " " << getIthNode(i) << "]";
  }

 private:
  void push(OutputChannelCallType call, TNode n) {
    d_callHistory.push_back(std::make_pair(call, n));
  }

  std::vector< std::pair<enum OutputChannelCallType, Node> > d_callHistory;
};/* class TestOutputChannel */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__THEORY_TEST_UTILS_H */
