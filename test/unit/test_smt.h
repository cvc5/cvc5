/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common header for unit tests that need an SolverEngine.
 */

#ifndef CVC5__TEST__UNIT__TEST_SMT_H
#define CVC5__TEST__UNIT__TEST_SMT_H

#include "expr/dtype_cons.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/skolem_manager.h"
#include "proof/proof_checker.h"
#include "smt/solver_engine.h"
#include "test.h"
#include "theory/output_channel.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "theory/theory_state.h"
#include "theory/valuation.h"
#include "util/resource_manager.h"

namespace cvc5::internal {
namespace test {

/* -------------------------------------------------------------------------- */
/* Test fixtures.                                                             */
/* -------------------------------------------------------------------------- */

class TestSmt : public TestInternal
{
 protected:
  void SetUp() override
  {
    d_nodeManager = NodeManager::currentNM();
    d_skolemManager = d_nodeManager->getSkolemManager();
    d_slvEngine.reset(new SolverEngine);
    d_slvEngine->finishInit();
  }

  NodeManager* d_nodeManager;
  SkolemManager* d_skolemManager;
  std::unique_ptr<SolverEngine> d_slvEngine;
};

class TestSmtNoFinishInit : public TestInternal
{
 protected:
  void SetUp() override
  {
    d_nodeManager = NodeManager::currentNM();
    d_skolemManager = d_nodeManager->getSkolemManager();
    d_slvEngine.reset(new SolverEngine);
  }

  NodeManager* d_nodeManager;
  SkolemManager* d_skolemManager;
  std::unique_ptr<SolverEngine> d_slvEngine;
};

/* -------------------------------------------------------------------------- */
/* Helpers.                                                                   */
/* -------------------------------------------------------------------------- */

/**
 * Very basic OutputChannel for testing simple Theory Behaviour.
 * Stores a call sequence for the output channel
 */
enum OutputChannelCallType
{
  CONFLICT,
  PROPAGATE,
  PROPAGATE_AS_DECISION,
  AUG_LEMMA,
  LEMMA,
  EXPLANATION
};

inline std::ostream& operator<<(std::ostream& out, OutputChannelCallType type)
{
  switch (type)
  {
    case CONFLICT: return out << "CONFLICT";
    case PROPAGATE: return out << "PROPAGATE";
    case PROPAGATE_AS_DECISION: return out << "PROPAGATE_AS_DECISION";
    case AUG_LEMMA: return out << "AUG_LEMMA";
    case LEMMA: return out << "LEMMA";
    case EXPLANATION: return out << "EXPLANATION";
    default: return out << "UNDEFINED-OutputChannelCallType!" << int(type);
  }
}

class DummyOutputChannel : public theory::OutputChannel
{
 public:
  DummyOutputChannel() {}
  ~DummyOutputChannel() override {}

  void safePoint(Resource r) override {}
  void conflict(TNode n) override { push(CONFLICT, n); }

  void trustedConflict(TrustNode n) override { push(CONFLICT, n.getNode()); }

  bool propagate(TNode n) override
  {
    push(PROPAGATE, n);
    return true;
  }

  void lemma(TNode n,
             theory::LemmaProperty p = theory::LemmaProperty::NONE) override
  {
    push(LEMMA, n);
  }

  void trustedLemma(TrustNode n, theory::LemmaProperty p) override
  {
    push(LEMMA, n.getNode());
  }

  void requirePhase(TNode, bool) override {}
  void setModelUnsound(theory::IncompleteId id) override {}
  void setRefutationUnsound(theory::IncompleteId id) override {}

  void clear() { d_callHistory.clear(); }

  Node getIthNode(int i) const
  {
    Node tmp = (d_callHistory[i]).second;
    return tmp;
  }

  OutputChannelCallType getIthCallType(int i) const
  {
    return (d_callHistory[i]).first;
  }

  unsigned getNumCalls() const { return d_callHistory.size(); }

  void printIth(std::ostream& os, int i) const
  {
    os << "[DummyOutputChannel " << i;
    os << " " << getIthCallType(i);
    os << " " << getIthNode(i) << "]";
  }

 private:
  void push(OutputChannelCallType call, TNode n)
  {
    d_callHistory.push_back(std::make_pair(call, n));
  }

  std::vector<std::pair<enum OutputChannelCallType, Node> > d_callHistory;
};

/* -------------------------------------------------------------------------- */

class DummyTheoryRewriter : public theory::TheoryRewriter
{
 public:
  theory::RewriteResponse preRewrite(TNode n) override
  {
    return theory::RewriteResponse(theory::REWRITE_DONE, n);
  }

  theory::RewriteResponse postRewrite(TNode n) override
  {
    return theory::RewriteResponse(theory::REWRITE_DONE, n);
  }
};

class DummyProofRuleChecker : public ProofRuleChecker
{
 public:
  DummyProofRuleChecker() {}
  ~DummyProofRuleChecker() {}
  void registerTo(ProofChecker* pc) override {}

 protected:
  Node checkInternal(PfRule id,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args) override
  {
    return Node::null();
  }
};

/** Dummy Theory interface.  */
template <theory::TheoryId theoryId>
class DummyTheory : public theory::Theory
{
 public:
  DummyTheory(Env& env, theory::OutputChannel& out, theory::Valuation valuation)
      : Theory(theoryId, env, out, valuation),
        d_state(env, valuation)
  {
    // use a default theory state object
    d_theoryState = &d_state;
  }

  theory::TheoryRewriter* getTheoryRewriter() override { return &d_rewriter; }
  ProofRuleChecker* getProofChecker() override { return &d_checker; }

  void registerTerm(TNode n)
  {
    // check that we registerTerm() a term only once
    ASSERT_TRUE(d_registered.find(n) == d_registered.end());

    for (TNode::iterator i = n.begin(); i != n.end(); ++i)
    {
      // check that registerTerm() is called in reverse topological order
      ASSERT_TRUE(d_registered.find(*i) != d_registered.end());
    }

    d_registered.insert(n);
  }

  void presolve() override { Unimplemented(); }
  void preRegisterTerm(TNode n) override { Unimplemented(); }
  void propagate(Effort level) override { Unimplemented(); }
  bool preNotifyFact(
      TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal) override
  {
    // do not assert to equality engine, since this theory does not use one
    return true;
  }
  TrustNode explain(TNode n) override { return TrustNode::null(); }
  Node getValue(TNode n) { return Node::null(); }
  std::string identify() const override { return "DummyTheory" + d_id; }

  std::set<Node> d_registered;

 private:
  /** Default theory state object */
  theory::TheoryState d_state;
  /**
   * This fake theory class is equally useful for bool, uf, arith, etc.  It
   * keeps an identifier to identify itself.
   */
  std::string d_id;
  /** The theory rewriter for this theory. */
  DummyTheoryRewriter d_rewriter;
  /** The proof checker for this theory. */
  DummyProofRuleChecker d_checker;
};

/* -------------------------------------------------------------------------- */
}  // namespace test
}  // namespace cvc5::internal
#endif
