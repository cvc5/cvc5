/*********************                                                        */
/*! \file proof_output_channel.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Guy Katz, Tim King, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/

#include "proof/proof_output_channel.h"

#include "base/check.h"
#include "theory/term_registration_visitor.h"
#include "theory/valuation.h"

namespace CVC4 {

ProofOutputChannel::ProofOutputChannel() : d_conflict(), d_proof(nullptr) {}
const Proof& ProofOutputChannel::getConflictProof() const
{
  Assert(hasConflict());
  return *d_proof;
}

void ProofOutputChannel::conflict(TNode n, std::unique_ptr<Proof> pf)
{
  Trace("pf::tp") << "ProofOutputChannel: CONFLICT: " << n << std::endl;
  Assert(!hasConflict());
  Assert(!d_proof);
  d_conflict = n;
  d_proof = std::move(pf);
  Assert(hasConflict());
  Assert(d_proof);
}

bool ProofOutputChannel::propagate(TNode x) {
  Trace("pf::tp") << "ProofOutputChannel: got a propagation: " << x
                  << std::endl;
  d_propagations.insert(x);
  return true;
}

theory::LemmaStatus ProofOutputChannel::lemma(TNode n, ProofRule rule, bool,
                                              bool, bool) {
  Trace("pf::tp") << "ProofOutputChannel: new lemma: " << n << std::endl;
  // TODO(#1231): We should transition to supporting multiple lemmas. The
  // following assertion cannot be enabled due to
  // "test/regress/regress0/arrays/swap_t1_np_nf_ai_00005_007.cvc.smt".
  // Assert(
  //     d_lemma.isNull()) <<
  //     "Multiple calls to ProofOutputChannel::lemma() are not supported.";
  d_lemma = n;
  return theory::LemmaStatus(TNode::null(), 0);
}

theory::LemmaStatus ProofOutputChannel::splitLemma(TNode, bool) {
  AlwaysAssert(false);
  return theory::LemmaStatus(TNode::null(), 0);
}

void ProofOutputChannel::requirePhase(TNode n, bool b) {
  Debug("pf::tp") << "ProofOutputChannel::requirePhase called" << std::endl;
  Trace("pf::tp") << "requirePhase " << n << " " << b << std::endl;
}

void ProofOutputChannel::setIncomplete() {
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
