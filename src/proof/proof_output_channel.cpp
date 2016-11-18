/*********************                                                        */
/*! \file proof_output_channel.cpp
** \verbatim
** \brief [[ Add one-line brief description here ]]
**
** [[ Add lengthier description here ]]
** \todo document this file
**/

#include "base/cvc4_assert.h"
#include "proof_output_channel.h"
#include "theory/term_registration_visitor.h"
#include "theory/valuation.h"

namespace CVC4 {

ProofOutputChannel::ProofOutputChannel() : d_conflict(), d_proof(NULL) {}

void ProofOutputChannel::conflict(TNode n, Proof* pf) throw() {
  Trace("pf::tp") << "ProofOutputChannel: CONFLICT: " << n << std::endl;
  Assert(d_conflict.isNull());
  Assert(!n.isNull());
  d_conflict = n;
  Assert(pf != NULL);
  d_proof = pf;
}

bool ProofOutputChannel::propagate(TNode x) throw() {
  Trace("pf::tp") << "ProofOutputChannel: got a propagation: " << x
                  << std::endl;
  d_propagations.insert(x);
  return true;
}

theory::LemmaStatus ProofOutputChannel::lemma(TNode n, ProofRule rule, bool,
                                              bool, bool) {
  Trace("pf::tp") << "ProofOutputChannel: new lemma: " << n << std::endl;
  d_lemma = n;
  return theory::LemmaStatus(TNode::null(), 0);
}

theory::LemmaStatus ProofOutputChannel::splitLemma(TNode, bool) {
  AlwaysAssert(false);
  return theory::LemmaStatus(TNode::null(), 0);
}

void ProofOutputChannel::requirePhase(TNode n, bool b) throw() {
  Debug("pf::tp") << "ProofOutputChannel::requirePhase called" << std::endl;
  Trace("pf::tp") << "requirePhase " << n << " " << b << std::endl;
}

bool ProofOutputChannel::flipDecision() throw() {
  Debug("pf::tp") << "ProofOutputChannel::flipDecision called" << std::endl;
  AlwaysAssert(false);
  return false;
}

void ProofOutputChannel::setIncomplete() throw() {
  Debug("pf::tp") << "ProofOutputChannel::setIncomplete called" << std::endl;
  AlwaysAssert(false);
}


MyPreRegisterVisitor::MyPreRegisterVisitor(theory::Theory* theory)
  : d_theory(theory)
  , d_visited() {
}

bool MyPreRegisterVisitor::alreadyVisited(TNode current, TNode parent) {
  return d_visited.find(current) != d_visited.end();
}

void MyPreRegisterVisitor::visit(TNode current, TNode parent) {
  d_theory->preRegisterTerm(current);
  d_visited.insert(current);
}

void MyPreRegisterVisitor::start(TNode node) {
}

void MyPreRegisterVisitor::done(TNode node) {
}

} /* namespace CVC4 */
