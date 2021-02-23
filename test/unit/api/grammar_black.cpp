/*********************                                                        */
/*! \file grammar_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the guards of the C++ API functions.
 **
 ** Black box testing of the guards of the C++ API functions.
 **/

#include "test_api.h"

namespace CVC4 {

using namespace api;

namespace test {

class TestApiBlackGrammar : public TestApi
{
};

TEST_F(TestApiBlackGrammar, addRule)
{
  Sort boolean = d_solver.getBooleanSort();
  Sort integer = d_solver.getIntegerSort();

  Term nullTerm;
  Term start = d_solver.mkVar(boolean);
  Term nts = d_solver.mkVar(boolean);

  Grammar g = d_solver.mkSygusGrammar({}, {start});

  ASSERT_NO_THROW(g.addRule(start, d_solver.mkBoolean(false)));

  ASSERT_THROW(g.addRule(nullTerm, d_solver.mkBoolean(false)),
               CVC4ApiException);
  ASSERT_THROW(g.addRule(start, nullTerm), CVC4ApiException);
  ASSERT_THROW(g.addRule(nts, d_solver.mkBoolean(false)), CVC4ApiException);
  ASSERT_THROW(g.addRule(start, d_solver.mkInteger(0)), CVC4ApiException);

  d_solver.synthFun("f", {}, boolean, g);

  ASSERT_THROW(g.addRule(start, d_solver.mkBoolean(false)), CVC4ApiException);
}

TEST_F(TestApiBlackGrammar, addRules)
{
  Sort boolean = d_solver.getBooleanSort();
  Sort integer = d_solver.getIntegerSort();

  Term nullTerm;
  Term start = d_solver.mkVar(boolean);
  Term nts = d_solver.mkVar(boolean);

  Grammar g = d_solver.mkSygusGrammar({}, {start});

  ASSERT_NO_THROW(g.addRules(start, {d_solver.mkBoolean(false)}));

  ASSERT_THROW(g.addRules(nullTerm, {d_solver.mkBoolean(false)}),
               CVC4ApiException);
  ASSERT_THROW(g.addRules(start, {nullTerm}), CVC4ApiException);
  ASSERT_THROW(g.addRules(nts, {d_solver.mkBoolean(false)}), CVC4ApiException);
  ASSERT_THROW(g.addRules(start, {d_solver.mkInteger(0)}), CVC4ApiException);

  d_solver.synthFun("f", {}, boolean, g);

  ASSERT_THROW(g.addRules(start, {d_solver.mkBoolean(false)}),
               CVC4ApiException);
}

TEST_F(TestApiBlackGrammar, addAnyConstant)
{
  Sort boolean = d_solver.getBooleanSort();

  Term nullTerm;
  Term start = d_solver.mkVar(boolean);
  Term nts = d_solver.mkVar(boolean);

  Grammar g = d_solver.mkSygusGrammar({}, {start});

  ASSERT_NO_THROW(g.addAnyConstant(start));
  ASSERT_NO_THROW(g.addAnyConstant(start));

  ASSERT_THROW(g.addAnyConstant(nullTerm), CVC4ApiException);
  ASSERT_THROW(g.addAnyConstant(nts), CVC4ApiException);

  d_solver.synthFun("f", {}, boolean, g);

  ASSERT_THROW(g.addAnyConstant(start), CVC4ApiException);
}

TEST_F(TestApiBlackGrammar, addAnyVariable)
{
  Sort boolean = d_solver.getBooleanSort();

  Term nullTerm;
  Term x = d_solver.mkVar(boolean);
  Term start = d_solver.mkVar(boolean);
  Term nts = d_solver.mkVar(boolean);

  Grammar g1 = d_solver.mkSygusGrammar({x}, {start});
  Grammar g2 = d_solver.mkSygusGrammar({}, {start});

  ASSERT_NO_THROW(g1.addAnyVariable(start));
  ASSERT_NO_THROW(g1.addAnyVariable(start));
  ASSERT_NO_THROW(g2.addAnyVariable(start));

  ASSERT_THROW(g1.addAnyVariable(nullTerm), CVC4ApiException);
  ASSERT_THROW(g1.addAnyVariable(nts), CVC4ApiException);

  d_solver.synthFun("f", {}, boolean, g1);

  ASSERT_THROW(g1.addAnyVariable(start), CVC4ApiException);
}
}  // namespace test
}  // namespace CVC4
