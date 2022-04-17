/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Mathias Preiner, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the Sygus API.
 *
 * A simple demonstration of how to use the Sygus API to synthesize max and min
 * functions.
 */

#include <cvc5/cvc5.h>

#include <iostream>

#include "utils.h"

using namespace cvc5;

int main()
{
  Solver slv;

  // required options
  slv.setOption("sygus", "true");
  slv.setOption("incremental", "false");

  // set the logic
  slv.setLogic("LIA");

  Sort integer = slv.getIntegerSort();
  Sort boolean = slv.getBooleanSort();

  // declare input variables for the functions-to-synthesize
  Term x = slv.mkVar(integer, "x");
  Term y = slv.mkVar(integer, "y");

  // declare the grammar non-terminals
  Term start = slv.mkVar(integer, "Start");
  Term start_bool = slv.mkVar(boolean, "StartBool");

  // define the rules
  Term zero = slv.mkInteger(0);
  Term one = slv.mkInteger(1);

  Term plus = slv.mkTerm(ADD, {start, start});
  Term minus = slv.mkTerm(SUB, {start, start});
  Term ite = slv.mkTerm(ITE, {start_bool, start, start});

  Term And = slv.mkTerm(AND, {start_bool, start_bool});
  Term Not = slv.mkTerm(NOT, {start_bool});
  Term leq = slv.mkTerm(LEQ, {start, start});

  // create the grammar object
  Grammar g = slv.mkGrammar({x, y}, {start, start_bool});

  // bind each non-terminal to its rules
  g.addRules(start, {zero, one, x, y, plus, minus, ite});
  g.addRules(start_bool, {And, Not, leq});

  // declare the functions-to-synthesize. Optionally, provide the grammar
  // constraints
  Term max = slv.synthFun("max", {x, y}, integer, g);
  Term min = slv.synthFun("min", {x, y}, integer);

  // declare universal variables.
  Term varX = slv.declareSygusVar("x", integer);
  Term varY = slv.declareSygusVar("y", integer);

  Term max_x_y = slv.mkTerm(APPLY_UF, {max, varX, varY});
  Term min_x_y = slv.mkTerm(APPLY_UF, {min, varX, varY});

  // add semantic constraints
  // (constraint (>= (max x y) x))
  slv.addSygusConstraint(slv.mkTerm(GEQ, {max_x_y, varX}));

  // (constraint (>= (max x y) y))
  slv.addSygusConstraint(slv.mkTerm(GEQ, {max_x_y, varY}));

  // (constraint (or (= x (max x y))
  //                 (= y (max x y))))
  slv.addSygusConstraint(slv.mkTerm(OR,
                                    {slv.mkTerm(EQUAL, {max_x_y, varX}),
                                     slv.mkTerm(EQUAL, {max_x_y, varY})}));

  // (constraint (= (+ (max x y) (min x y))
  //                (+ x y)))
  slv.addSygusConstraint(slv.mkTerm(
      EQUAL,
      {slv.mkTerm(ADD, {max_x_y, min_x_y}), slv.mkTerm(ADD, {varX, varY})}));

  // print solutions if available
  if (slv.checkSynth().hasSolution())
  {
    // Output should be equivalent to:
    // (
    //   (define-fun max ((x Int) (y Int)) Int (ite (<= x y) y x))
    //   (define-fun min ((x Int) (y Int)) Int (ite (<= x y) x y))
    // )
    std::vector<Term> terms = {max, min};
    utils::printSynthSolutions(terms, slv.getSynthSolutions(terms));
  }

  return 0;
}
