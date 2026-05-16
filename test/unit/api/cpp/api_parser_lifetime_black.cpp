/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the lifetime guarantees of the parser API.
 *
 * A SymbolManager keeps the internal node manager alive (it holds its own
 * copy of the term manager). Terms and sorts obtained through the parser
 * must therefore remain usable after the parser, symbol manager, solver and
 * term manager that produced them have been destroyed.
 */

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include <sstream>

#include "test_parser.h"

using namespace cvc5::parser;

namespace cvc5::internal {
namespace test {

class TestApiBlackParserLifetime : public TestParser
{
};

TEST_F(TestApiBlackParserLifetime, symbolManagerOutlivesTermManager)
{
  std::unique_ptr<SymbolManager> sm;
  {
    TermManager tm;
    sm = std::make_unique<SymbolManager>(tm);
  }
  // tm is destroyed here; the symbol manager keeps the node manager alive
  // through its own copy of the term manager and must still be usable.
  ASSERT_FALSE(sm->isLogicSet());
  ASSERT_EQ(sm->getDeclaredTerms().size(), 0);
  ASSERT_EQ(sm->getDeclaredSorts().size(), 0);
}

TEST_F(TestApiBlackParserLifetime, declaredSymbolsOutliveParserAndManagers)
{
  std::vector<Term> terms;
  std::vector<Sort> sorts;
  {
    TermManager tm;
    Solver slv(tm);
    SymbolManager sm(tm);
    InputParser p(&slv, &sm);
    p.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                                "parser_lifetime");
    p.appendIncrementalStringInput("(set-logic ALL)\n");
    p.appendIncrementalStringInput("(declare-sort U 0)\n");
    p.appendIncrementalStringInput("(declare-fun a () Int)\n");
    p.appendIncrementalStringInput("(declare-fun b () U)\n");
    std::stringstream out;
    for (Command cmd = p.nextCommand(); !cmd.isNull(); cmd = p.nextCommand())
    {
      cmd.invoke(&slv, &sm, out);
    }
    terms = sm.getDeclaredTerms();
    sorts = sm.getDeclaredSorts();
    ASSERT_EQ(terms.size(), 2);
    ASSERT_EQ(sorts.size(), 1);
  }
  // The parser, symbol manager, solver and term manager are all destroyed
  // here; the declared terms and sorts must still be usable.
  for (const Term& t : terms)
  {
    ASSERT_FALSE(t.isNull());
    ASSERT_NO_THROW(t.getSort());
    ASSERT_NO_THROW(t.toString());
  }
  for (const Sort& s : sorts)
  {
    ASSERT_FALSE(s.isNull());
    ASSERT_NO_THROW(s.toString());
  }
}

TEST_F(TestApiBlackParserLifetime, parsedTermOutlivesParserAndManagers)
{
  Term t;
  {
    TermManager tm;
    Solver slv(tm);
    SymbolManager sm(tm);
    InputParser p(&slv, &sm);
    p.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                                "parser_lifetime");
    std::stringstream out;
    p.appendIncrementalStringInput("(set-logic ALL)\n");
    p.appendIncrementalStringInput("(declare-fun x () Int)\n");
    Command cmd = p.nextCommand();
    cmd.invoke(&slv, &sm, out);
    cmd = p.nextCommand();
    cmd.invoke(&slv, &sm, out);
    p.appendIncrementalStringInput("(+ x 1)\n");
    t = p.nextTerm();
  }
  // The parser, symbol manager, solver and term manager are all destroyed
  // here; the parsed term must still be usable.
  ASSERT_FALSE(t.isNull());
  ASSERT_EQ(t.getKind(), Kind::ADD);
  ASSERT_TRUE(t.getSort().isInteger());
  ASSERT_NO_THROW(t.toString());
}

TEST_F(TestApiBlackParserLifetime,
       parsedTermOutlivesParserWithInternalSymbolManager)
{
  Term t;
  {
    TermManager tm;
    Solver slv(tm);
    // This parser allocates and owns its own symbol manager.
    InputParser p(&slv);
    p.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                                "parser_lifetime");
    std::stringstream out;
    p.appendIncrementalStringInput("(set-logic ALL)\n");
    p.appendIncrementalStringInput("(declare-fun x () Int)\n");
    Command cmd = p.nextCommand();
    cmd.invoke(&slv, p.getSymbolManager(), out);
    cmd = p.nextCommand();
    cmd.invoke(&slv, p.getSymbolManager(), out);
    p.appendIncrementalStringInput("(* x 2)\n");
    t = p.nextTerm();
  }
  // The parser (and its internally allocated symbol manager), solver and
  // term manager are all destroyed here; the parsed term must still be
  // usable.
  ASSERT_FALSE(t.isNull());
  ASSERT_EQ(t.getKind(), Kind::MULT);
  ASSERT_TRUE(t.getSort().isInteger());
  ASSERT_NO_THROW(t.toString());
}

}  // namespace test
}  // namespace cvc5::internal
