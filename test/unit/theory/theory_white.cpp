/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "smt/smt_solver.h"
#include "test_smt.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "util/resource_manager.h"

namespace cvc5::internal {

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
    d_slvEngine->finishInit();
    TheoryEngine* te = d_slvEngine->d_smtSolver->getTheoryEngine();
    delete te->d_theoryTable[THEORY_BUILTIN];
    delete te->d_theoryOut[THEORY_BUILTIN];
    te->d_theoryTable[THEORY_BUILTIN] = nullptr;
    te->d_theoryOut[THEORY_BUILTIN] = nullptr;

    d_dummy_theory.reset(new DummyTheory<THEORY_BUILTIN>(
        d_slvEngine->getEnv(), d_outputChannel, Valuation(nullptr)));
    d_outputChannel.clear();
    d_atom0 = d_nodeManager->mkConst(true);
    d_atom1 = d_nodeManager->mkConst(false);
  }

  DummyOutputChannel d_outputChannel;
  std::unique_ptr<DummyTheory<THEORY_BUILTIN>> d_dummy_theory;
  Node d_atom0;
  Node d_atom1;
};

TEST_F(TestTheoryWhite, effort)
{
  Theory::Effort s = Theory::EFFORT_STANDARD;
  Theory::Effort f = Theory::EFFORT_FULL;

  ASSERT_FALSE(Theory::fullEffort(s));
  ASSERT_TRUE(Theory::fullEffort(f));
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
  d_outputChannel.lemma(d_atom0.orNode(d_atom0.notNode()));
  Node s = d_atom0.orNode(d_atom0.notNode());
  ASSERT_EQ(d_outputChannel.d_callHistory.size(), 2u);
  ASSERT_EQ(d_outputChannel.d_callHistory[0], std::make_pair(LEMMA, n));
  ASSERT_EQ(d_outputChannel.d_callHistory[1], std::make_pair(LEMMA, s));
  d_outputChannel.d_callHistory.clear();
}
}  // namespace test
}  // namespace cvc5::internal
