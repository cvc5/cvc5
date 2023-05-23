/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Christopher L. Conway, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of cvc5::prop::CnfStream.
 */

#include "base/check.h"
#include "context/context.h"
#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "prop/registrar.h"
#include "prop/sat_solver.h"
#include "prop/theory_proxy.h"
#include "test_smt.h"
#include "theory/arith/theory_arith.h"
#include "theory/booleans/theory_bool.h"
#include "theory/builtin/theory_builtin.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"

namespace cvc5::internal {

using namespace cvc5::context;
using namespace prop;
using namespace smt;
using namespace theory;

namespace test {

/* This fake class relies on the fact that a MiniSat variable is just an int. */
class FakeSatSolver : public SatSolver
{
 public:
  FakeSatSolver() : d_nextVar(0), d_addClauseCalled(false) {}

  SatVariable newVar(bool theoryAtom, bool canErase) override
  {
    return d_nextVar++;
  }

  SatVariable trueVar() override { return d_nextVar++; }

  SatVariable falseVar() override { return d_nextVar++; }

  ClauseId addClause(SatClause& c, bool lemma) override
  {
    d_addClauseCalled = true;
    return ClauseIdUndef;
  }

  ClauseId addXorClause(SatClause& clause, bool rhs, bool removable) override
  {
    d_addClauseCalled = true;
    return ClauseIdUndef;
  }

  bool nativeXor() override { return false; }

  void reset() { d_addClauseCalled = false; }

  unsigned int addClauseCalled() { return d_addClauseCalled; }

  unsigned getAssertionLevel() const override { return 0; }

  bool isDecision(Node) const { return false; }

  void unregisterVar(SatLiteral lit) {}

  void renewVar(SatLiteral lit, int level = -1) {}

  bool spendResource() { return false; }

  void interrupt() override {}

  SatValue solve() override { return SAT_VALUE_UNKNOWN; }

  SatValue solve(long unsigned int& resource) override
  {
    return SAT_VALUE_UNKNOWN;
  }

  SatValue value(SatLiteral l) override { return SAT_VALUE_UNKNOWN; }

  SatValue modelValue(SatLiteral l) override { return SAT_VALUE_UNKNOWN; }

  bool properExplanation(SatLiteral lit, SatLiteral expl) const { return true; }

  bool ok() const override { return true; }

 private:
  SatVariable d_nextVar;
  bool d_addClauseCalled;
};

class TestPropWhiteCnfStream : public TestSmt
{
 protected:
  void SetUp() override
  {
    TestSmt::SetUp();
    d_satSolver.reset(new FakeSatSolver());
    d_cnfContext.reset(new Context());
    d_cnfRegistrar.reset(new prop::NullRegistrar);
    d_cnfStream.reset(new prop::CnfStream(d_slvEngine->getEnv(),
                                          d_satSolver.get(),
                                          d_cnfRegistrar.get(),
                                          d_cnfContext.get()));
  }

  void TearDown() override
  {
    d_cnfStream.reset(nullptr);
    d_cnfRegistrar.reset(nullptr);
    d_cnfContext.reset(nullptr);
    d_satSolver.reset(nullptr);
    TestSmt::TearDown();
  }

  /** The SAT solver proxy */
  std::unique_ptr<FakeSatSolver> d_satSolver;
  /** The CNF converter in use */
  std::unique_ptr<CnfStream> d_cnfStream;
  /** The context of the CnfStream. */
  std::unique_ptr<Context> d_cnfContext;
  /** The registrar used by the CnfStream. */
  std::unique_ptr<prop::NullRegistrar> d_cnfRegistrar;
};

/**
 * [chris 5/26/2010] In the tests below, we don't attempt to delve into the
 * deep structure of the CNF conversion. Firstly, we just want to make sure
 * that the conversion doesn't choke on any boolean Exprs. We'll also check
 * that addClause got called. We won't check that it gets called a particular
 * number of times, or with what.
 */

TEST_F(TestPropWhiteCnfStream, and)
{
  Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
  Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
  Node c = d_nodeManager->mkVar(d_nodeManager->booleanType());
  d_cnfStream->convertAndAssert(
      d_nodeManager->mkNode(kind::AND, a, b, c), false, false);
  ASSERT_TRUE(d_satSolver->addClauseCalled());
}

TEST_F(TestPropWhiteCnfStream, complex_expr)
{
  Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
  Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
  Node c = d_nodeManager->mkVar(d_nodeManager->booleanType());
  Node d = d_nodeManager->mkVar(d_nodeManager->booleanType());
  Node e = d_nodeManager->mkVar(d_nodeManager->booleanType());
  Node f = d_nodeManager->mkVar(d_nodeManager->booleanType());
  d_cnfStream->convertAndAssert(
      d_nodeManager->mkNode(
          kind::IMPLIES,
          d_nodeManager->mkNode(kind::AND, a, b),
          d_nodeManager->mkNode(
              kind::EQUAL,
              d_nodeManager->mkNode(kind::OR, c, d),
              d_nodeManager->mkNode(kind::NOT,
                                    d_nodeManager->mkNode(kind::XOR, e, f)))),
      false,
      false);
  ASSERT_TRUE(d_satSolver->addClauseCalled());
}

TEST_F(TestPropWhiteCnfStream, true)
{
  d_cnfStream->convertAndAssert(d_nodeManager->mkConst(true), false, false);
  ASSERT_TRUE(d_satSolver->addClauseCalled());
}

TEST_F(TestPropWhiteCnfStream, false)
{
  d_cnfStream->convertAndAssert(d_nodeManager->mkConst(false), false, false);
  ASSERT_TRUE(d_satSolver->addClauseCalled());
}

TEST_F(TestPropWhiteCnfStream, iff)
{
  Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
  Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
  d_cnfStream->convertAndAssert(
      d_nodeManager->mkNode(kind::EQUAL, a, b), false, false);
  ASSERT_TRUE(d_satSolver->addClauseCalled());
}

TEST_F(TestPropWhiteCnfStream, implies)
{
  Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
  Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
  d_cnfStream->convertAndAssert(
      d_nodeManager->mkNode(kind::IMPLIES, a, b), false, false);
  ASSERT_TRUE(d_satSolver->addClauseCalled());
}

TEST_F(TestPropWhiteCnfStream, not )
{
  Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
  d_cnfStream->convertAndAssert(
      d_nodeManager->mkNode(kind::NOT, a), false, false);
  ASSERT_TRUE(d_satSolver->addClauseCalled());
}

TEST_F(TestPropWhiteCnfStream, or)
{
  Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
  Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
  Node c = d_nodeManager->mkVar(d_nodeManager->booleanType());
  d_cnfStream->convertAndAssert(
      d_nodeManager->mkNode(kind::OR, a, b, c), false, false);
  ASSERT_TRUE(d_satSolver->addClauseCalled());
}

TEST_F(TestPropWhiteCnfStream, var)
{
  Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
  Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
  d_cnfStream->convertAndAssert(a, false, false);
  ASSERT_TRUE(d_satSolver->addClauseCalled());
  d_satSolver->reset();
  d_cnfStream->convertAndAssert(b, false, false);
  ASSERT_TRUE(d_satSolver->addClauseCalled());
}

TEST_F(TestPropWhiteCnfStream, xor)
{
  Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
  Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
  d_cnfStream->convertAndAssert(
      d_nodeManager->mkNode(kind::XOR, a, b), false, false);
  ASSERT_TRUE(d_satSolver->addClauseCalled());
}

TEST_F(TestPropWhiteCnfStream, ensure_literal)
{
  Node a = d_nodeManager->mkVar(d_nodeManager->booleanType());
  Node b = d_nodeManager->mkVar(d_nodeManager->booleanType());
  Node a_and_b = d_nodeManager->mkNode(kind::AND, a, b);
  d_cnfStream->ensureLiteral(a_and_b);
  // Clauses are necessary to "literal-ize" a_and_b
  ASSERT_TRUE(d_satSolver->addClauseCalled());
  ASSERT_TRUE(d_cnfStream->hasLiteral(a_and_b));
}
}  // namespace test
}  // namespace cvc5::internal
