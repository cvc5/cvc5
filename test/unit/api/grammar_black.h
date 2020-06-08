/*********************                                                        */
/*! \file grammar_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Abdalrhman Mohamed, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the guards of the C++ API functions.
 **
 ** Black box testing of the guards of the C++ API functions.
 **/

#include <cxxtest/TestSuite.h>

#include "api/cvc4cpp.h"

using namespace CVC4::api;

class GrammarBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override;
  void tearDown() override;

  void testAddRule();
  void testAddRules();
  void testAddAnyConstant();
  void testAddAnyVariable();

 private:
  std::unique_ptr<Solver> d_solver;
};

void GrammarBlack::setUp() { d_solver.reset(new Solver()); }

void GrammarBlack::tearDown() {}

void GrammarBlack::testAddRule()
{
  Sort boolean = d_solver->getBooleanSort();
  Sort integer = d_solver->getIntegerSort();

  Term nullTerm;
  Term start = d_solver->mkVar(boolean);
  Term nts = d_solver->mkVar(boolean);

  Grammar g = d_solver->mkSygusGrammar({}, {start});

  TS_ASSERT_THROWS_NOTHING(g.addRule(start, d_solver->mkBoolean(false)));

  TS_ASSERT_THROWS(g.addRule(nullTerm, d_solver->mkBoolean(false)),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(g.addRule(start, nullTerm), CVC4ApiException&);
  TS_ASSERT_THROWS(g.addRule(nts, d_solver->mkBoolean(false)),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(g.addRule(start, d_solver->mkReal(0)), CVC4ApiException&);

  d_solver->synthFun("f", {}, boolean, g);

  TS_ASSERT_THROWS(g.addRule(start, d_solver->mkBoolean(false)),
                   CVC4ApiException&);
}

void GrammarBlack::testAddRules()
{
  Sort boolean = d_solver->getBooleanSort();
  Sort integer = d_solver->getIntegerSort();

  Term nullTerm;
  Term start = d_solver->mkVar(boolean);
  Term nts = d_solver->mkVar(boolean);

  Grammar g = d_solver->mkSygusGrammar({}, {start});

  TS_ASSERT_THROWS_NOTHING(g.addRules(start, {d_solver->mkBoolean(false)}));

  TS_ASSERT_THROWS(g.addRules(nullTerm, {d_solver->mkBoolean(false)}),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(g.addRules(start, {nullTerm}), CVC4ApiException&);
  TS_ASSERT_THROWS(g.addRules(nts, {d_solver->mkBoolean(false)}),
                   CVC4ApiException&);
  TS_ASSERT_THROWS(g.addRules(start, {d_solver->mkReal(0)}), CVC4ApiException&);

  d_solver->synthFun("f", {}, boolean, g);

  TS_ASSERT_THROWS(g.addRules(start, {d_solver->mkBoolean(false)}),
                   CVC4ApiException&);
}

void GrammarBlack::testAddAnyConstant()
{
  Sort boolean = d_solver->getBooleanSort();

  Term nullTerm;
  Term start = d_solver->mkVar(boolean);
  Term nts = d_solver->mkVar(boolean);

  Grammar g = d_solver->mkSygusGrammar({}, {start});

  TS_ASSERT_THROWS_NOTHING(g.addAnyConstant(start));
  TS_ASSERT_THROWS_NOTHING(g.addAnyConstant(start));

  TS_ASSERT_THROWS(g.addAnyConstant(nullTerm), CVC4ApiException&);
  TS_ASSERT_THROWS(g.addAnyConstant(nts), CVC4ApiException&);

  d_solver->synthFun("f", {}, boolean, g);

  TS_ASSERT_THROWS(g.addAnyConstant(start), CVC4ApiException&);
}

void GrammarBlack::testAddAnyVariable()
{
  Sort boolean = d_solver->getBooleanSort();

  Term nullTerm;
  Term x = d_solver->mkVar(boolean);
  Term start = d_solver->mkVar(boolean);
  Term nts = d_solver->mkVar(boolean);

  Grammar g1 = d_solver->mkSygusGrammar({x}, {start});
  Grammar g2 = d_solver->mkSygusGrammar({}, {start});

  TS_ASSERT_THROWS_NOTHING(g1.addAnyVariable(start));
  TS_ASSERT_THROWS_NOTHING(g1.addAnyVariable(start));
  TS_ASSERT_THROWS_NOTHING(g2.addAnyVariable(start));

  TS_ASSERT_THROWS(g1.addAnyVariable(nullTerm), CVC4ApiException&);
  TS_ASSERT_THROWS(g1.addAnyVariable(nts), CVC4ApiException&);

  d_solver->synthFun("f", {}, boolean, g1);

  TS_ASSERT_THROWS(g1.addAnyVariable(start), CVC4ApiException&);
}
