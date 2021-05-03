/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::theory::Theory.
 */

#include <memory>
#include <vector>

#include "context/context.h"
#include "expr/node.h"
#include "test_smt.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "util/resource_manager.h"

namespace cvc5 {

using namespace theory;
using namespace expr;
using namespace context;

namespace test {

class TestTheoryWhite : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_context = d_smtEngine->getContext();
    d_user_context = d_smtEngine->getUserContext();
    d_logicInfo.reset(new LogicInfo());
    d_logicInfo->lock();
    d_smtEngine->finishInit();
    delete d_smtEngine->getTheoryEngine()->d_theoryTable[THEORY_BUILTIN];
    delete d_smtEngine->getTheoryEngine()->d_theoryOut[THEORY_BUILTIN];
    d_smtEngine->getTheoryEngine()->d_theoryTable[THEORY_BUILTIN] = nullptr;
    d_smtEngine->getTheoryEngine()->d_theoryOut[THEORY_BUILTIN] = nullptr;

    d_dummy_theory.reset(new DummyTheory<THEORY_BUILTIN>(d_context,
                                                         d_user_context,
                                                         d_outputChannel,
                                                         Valuation(nullptr),
                                                         *d_logicInfo,
                                                         nullptr));
    d_outputChannel.clear();
    d_atom0 = d_nodeManager->mkConst(true);
    d_atom1 = d_nodeManager->mkConst(false);
  }

  Context* d_context;
  UserContext* d_user_context;
  std::unique_ptr<LogicInfo> d_logicInfo;
  DummyOutputChannel d_outputChannel;
  std::unique_ptr<DummyTheory<THEORY_BUILTIN>> d_dummy_theory;
  Node d_atom0;
  Node d_atom1;
};

TEST_F(TestTheoryWhite, effort)
{
  Theory::Effort s = Theory::EFFORT_STANDARD;
  Theory::Effort f = Theory::EFFORT_FULL;

  ASSERT_TRUE(Theory::standardEffortOnly(s));
  ASSERT_FALSE(Theory::standardEffortOnly(f));

  ASSERT_FALSE(Theory::fullEffort(s));
  ASSERT_TRUE(Theory::fullEffort(f));

  ASSERT_TRUE(Theory::standardEffortOrMore(s));
  ASSERT_TRUE(Theory::standardEffortOrMore(f));
}

TEST_F(TestTheoryWhite, done)
{
  ASSERT_TRUE(d_dummy_theory->done());

  d_dummy_theory->assertFact(d_atom0, true);
  d_dummy_theory->assertFact(d_atom1, true);

  ASSERT_FALSE(d_dummy_theory->done());

  d_dummy_theory->check(Theory::EFFORT_FULL);

  ASSERT_TRUE(d_dummy_theory->done());
}

TEST_F(TestTheoryWhite, outputChannel)
{
  Node n = d_atom0.orNode(d_atom1);
  d_outputChannel.lemma(n);
  d_outputChannel.split(d_atom0);
  Node s = d_atom0.orNode(d_atom0.notNode());
  ASSERT_EQ(d_outputChannel.d_callHistory.size(), 2u);
  ASSERT_EQ(d_outputChannel.d_callHistory[0], std::make_pair(LEMMA, n));
  ASSERT_EQ(d_outputChannel.d_callHistory[1], std::make_pair(LEMMA, s));
  d_outputChannel.d_callHistory.clear();
}
}  // namespace test
}  // namespace cvc5
