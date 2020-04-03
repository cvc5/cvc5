/*********************                                                        */
/*! \file sygus_max.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Abdalrhman Mohamed, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the Sygus API.
 **
 ** A simple demonstration of how to use the Sygus API to synthesize max and min
 ** functions.
 **/

#include <cvc4/api/cvc4cpp.h>

#include <iostream>

using namespace std;
using namespace CVC4::api;

int main()
{
  Solver slv;

  // required options
  slv.setOption("lang", "sygus2");
  slv.setOption("incremental", "false");

  // set the logic
  slv.setLogic("LIA");

  Sort integer = slv.getIntegerSort();
  Sort boolean = slv.getBooleanSort();

  // declare input variables for the function-to-synthesize
  Term x = slv.mkVar(integer, "x");
  Term y = slv.mkVar(integer, "y");

  // declare the grammar non-terminals
  Term start = slv.mkVar(integer, "Start");
  Term start_bool = slv.mkVar(boolean, "StartBool");

  // define the rules
  Term zero = slv.mkReal(0);
  Term one = slv.mkReal(1);

  Term plus = slv.mkTerm(PLUS, start, start);
  Term minus = slv.mkTerm(PLUS, start, start);
  Term ite = slv.mkTerm(ITE, start_bool, start, start);

  Term And = slv.mkTerm(AND, start_bool, start_bool);
  Term Not = slv.mkTerm(NOT, start_bool);
  Term leq = slv.mkTerm(LEQ, start, start);

  // create the grammar object
  Grammar g = slv.mkGrammar({x, y}, {start, start_bool});

  // bind each non-terminal to its rules
  g.addRules(start, {zero, one, x, y, plus, minus, ite});
  g.addRules(start_bool, {And, Not, leq});

  // declare the function-to-synthesize. Optionally, provide the grammar
  // constraints
  Term max = slv.synthFun("max", {x, y}, integer, g);
  Term min = slv.synthFun("min", {x, y}, integer);

  // declare universal variables.
  Term varX = slv.declareVar(integer, "x");
  Term varY = slv.declareVar(integer, "y");

  Term max_x_y = slv.mkTerm(APPLY_UF, max, varX, varY);
  Term min_x_y = slv.mkTerm(APPLY_UF, min, varX, varY);

  // add logical constraints
  slv.addConstraint(slv.mkTerm(GEQ, max_x_y, varX));
  slv.addConstraint(slv.mkTerm(GEQ, max_x_y, varY));
  slv.addConstraint(slv.mkTerm(
      OR, slv.mkTerm(EQUAL, max_x_y, varX), slv.mkTerm(EQUAL, max_x_y, varY)));
  slv.addConstraint(slv.mkTerm(
      EQUAL, slv.mkTerm(PLUS, max_x_y, min_x_y), slv.mkTerm(PLUS, varX, varY)));

  // print solutions if available
  if (slv.checkSynth().isUnsat()) slv.printSynthSolution(cout);

  return 0;
}
