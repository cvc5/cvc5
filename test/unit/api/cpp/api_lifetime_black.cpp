/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the lifetime guarantees of the C++ API.
 *
 * API wrapper objects (Sort, Op, Term, Datatype, Grammar, Proof, ...) keep
 * the internal node manager alive while they are in use. They must therefore
 * remain usable after the TermManager and/or Solver that created them have
 * been destroyed.
 */

#include <gtest/gtest.h>

#include <memory>

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackLifetime : public TestApi
{
};

TEST_F(TestApiBlackLifetime, sortOutlivesTermManager)
{
  Sort s;
  Sort arr;
  {
    TermManager tm;
    s = tm.getIntegerSort();
    arr = tm.mkArraySort(s, tm.getBooleanSort());
  }
  // tm is destroyed here; s and arr must still be usable.
  ASSERT_TRUE(s.isInteger());
  ASSERT_TRUE(arr.isArray());
  ASSERT_EQ(arr.getArrayIndexSort(), s);
  ASSERT_NO_THROW(s.toString());
  ASSERT_EQ(s, arr.getArrayIndexSort());
}

TEST_F(TestApiBlackLifetime, termOutlivesTermManager)
{
  Term t;
  Sort s;
  {
    TermManager tm;
    s = tm.getIntegerSort();
    Term x = tm.mkConst(s, "x");
    t = tm.mkTerm(Kind::ADD, {x, tm.mkInteger(1)});
  }
  // tm is destroyed here; t must still be usable.
  ASSERT_EQ(t.getKind(), Kind::ADD);
  ASSERT_EQ(t.getSort(), s);
  ASSERT_EQ(t.getNumChildren(), 2);
  ASSERT_NO_THROW(t.toString());
  ASSERT_EQ(t, t);
}

TEST_F(TestApiBlackLifetime, opOutlivesTermManager)
{
  Op op;
  {
    TermManager tm;
    op = tm.mkOp(Kind::BITVECTOR_EXTRACT, {4, 0});
  }
  // tm is destroyed here; op must still be usable.
  ASSERT_TRUE(op.isIndexed());
  ASSERT_EQ(op.getKind(), Kind::BITVECTOR_EXTRACT);
  ASSERT_EQ(op.getNumIndices(), 2);
  ASSERT_NO_THROW(op[0]);
  ASSERT_NO_THROW(op.toString());
}

TEST_F(TestApiBlackLifetime, termIteratorOutlivesTermManager)
{
  Term t;
  {
    TermManager tm;
    Sort b = tm.getBooleanSort();
    t = tm.mkTerm(Kind::AND, {tm.mkConst(b, "x"), tm.mkConst(b, "y")});
  }
  // tm is destroyed here; iterating over t (which constructs
  // Term::const_iterator objects) must still be safe.
  size_t count = 0;
  for (auto it = t.begin(), end = t.end(); it != end; ++it)
  {
    Term child = *it;
    ASSERT_FALSE(child.isNull());
    ++count;
  }
  ASSERT_EQ(count, 2);
}

TEST_F(TestApiBlackLifetime, datatypeOutlivesTermManager)
{
  Sort listSort;
  {
    TermManager tm;
    DatatypeDecl decl = tm.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = tm.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", tm.getIntegerSort());
    cons.addSelectorSelf("tail");
    decl.addConstructor(cons);
    DatatypeConstructorDecl nil = tm.mkDatatypeConstructorDecl("nil");
    decl.addConstructor(nil);
    listSort = tm.mkDatatypeSort(decl);
  }
  // tm is destroyed here; the datatype, its constructors and selectors
  // (and their iterators) must still be usable.
  Datatype dt = listSort.getDatatype();
  ASSERT_EQ(dt.getName(), "list");
  ASSERT_EQ(dt.getNumConstructors(), 2);

  size_t numCtors = 0;
  for (const auto& ctor : dt)
  {
    ASSERT_FALSE(ctor.getName().empty());
    for (const auto& sel : ctor)
    {
      ASSERT_FALSE(sel.getName().empty());
    }
    ++numCtors;
  }
  ASSERT_EQ(numCtors, 2);

  DatatypeConstructor consCtor = dt.getConstructor("cons");
  ASSERT_EQ(consCtor.getName(), "cons");
  DatatypeSelector head = consCtor.getSelector("head");
  ASSERT_EQ(head.getName(), "head");
  ASSERT_TRUE(head.getCodomainSort().isInteger());
}

TEST_F(TestApiBlackLifetime, solverOutlivesTermManager)
{
  // The Solver stores its own copy of the TermManager (sharing the
  // underlying node manager), so it stays usable after the TermManager
  // that constructed it has been destroyed.
  std::unique_ptr<Solver> slv;
  {
    TermManager tm;
    slv = std::make_unique<Solver>(tm);
  }
  // tm is destroyed here; the solver and the term manager returned by
  // getTermManager() must still be usable.
  TermManager& tm2 = slv->getTermManager();
  Sort b = tm2.getBooleanSort();
  Term x = tm2.mkConst(b, "x");
  ASSERT_NO_THROW(slv->assertFormula(x));
  ASSERT_TRUE(slv->checkSat().isSat());
}

TEST_F(TestApiBlackLifetime, valueOutlivesSolverAndTermManager)
{
  Term value;
  {
    TermManager tm;
    Solver slv(tm);
    slv.setOption("produce-models", "true");
    Sort intSort = tm.getIntegerSort();
    Term x = tm.mkConst(intSort, "x");
    slv.assertFormula(tm.mkTerm(Kind::GT, {x, tm.mkInteger(0)}));
    ASSERT_TRUE(slv.checkSat().isSat());
    value = slv.getValue(x);
  }
  // Both the solver and the term manager are destroyed here; the value
  // term obtained from the solver must still be usable.
  ASSERT_FALSE(value.isNull());
  ASSERT_TRUE(value.getSort().isInteger());
  ASSERT_NO_THROW(value.toString());
}

TEST_F(TestApiBlackLifetime, grammarOutlivesSolverAndTermManager)
{
  Grammar g;
  {
    TermManager tm;
    Solver slv(tm);
    slv.setOption("sygus", "true");
    Sort b = tm.getBooleanSort();
    Term start = tm.mkVar(b);
    g = slv.mkGrammar({}, {start});
    g.addRule(start, tm.mkBoolean(false));
  }
  // Both the solver and the term manager are destroyed here; the grammar
  // must still be usable.
  ASSERT_NE(g.toString(), "");
}

TEST_F(TestApiBlackLifetime, proofOutlivesSolverAndTermManager)
{
  Proof proof;
  {
    TermManager tm;
    Solver slv(tm);
    slv.setOption("produce-proofs", "true");
    Sort b = tm.getBooleanSort();
    Term x = tm.mkConst(b, "x");
    slv.assertFormula(x);
    slv.assertFormula(x.notTerm());
    ASSERT_FALSE(slv.checkSat().isSat());
    proof = slv.getProof().front();
  }
  // Both the solver and the term manager are destroyed here; the proof
  // must still be usable.
  ASSERT_NO_THROW(proof.getRule());
  ASSERT_NO_THROW(proof.getResult());
  ASSERT_NO_THROW(proof.getChildren());
}

}  // namespace test
}  // namespace cvc5::internal
