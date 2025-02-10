/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
  TermManager tm;
  Solver slv(tm);

  // required options
  slv.setOption("sygus", "true");
  slv.setOption("incremental", "false");

  // set the logic
  slv.setLogic("LIA");

  Sort integer = tm.getIntegerSort();
  Sort boolean = tm.getBooleanSort();

  // declare input variables for the functions-to-synthesize
  Term x = tm.mkVar(integer, "x");
  Term y = tm.mkVar(integer, "y");

  // declare the grammar non-terminals
  Term start = tm.mkVar(integer, "Start");
  Term start_bool = tm.mkVar(boolean, "StartBool");

  // define the rules
  Term zero = tm.mkInteger(0);
  Term one = tm.mkInteger(1);

  Term plus = tm.mkTerm(Kind::ADD, {start, start});
  Term minus = tm.mkTerm(Kind::SUB, {start, start});
  Term ite = tm.mkTerm(Kind::ITE, {start_bool, start, start});

  Term And = tm.mkTerm(Kind::AND, {start_bool, start_bool});
  Term Not = tm.mkTerm(Kind::NOT, {start_bool});
  Term leq = tm.mkTerm(Kind::LEQ, {start, start});

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

  Term max_x_y = tm.mkTerm(Kind::APPLY_UF, {max, varX, varY});
  Term min_x_y = tm.mkTerm(Kind::APPLY_UF, {min, varX, varY});

  // add semantic constraints
  // (constraint (>= (max x y) x))
  slv.addSygusConstraint(tm.mkTerm(Kind::GEQ, {max_x_y, varX}));

  // (constraint (>= (max x y) y))
  slv.addSygusConstraint(tm.mkTerm(Kind::GEQ, {max_x_y, varY}));

  // (constraint (or (= x (max x y))
  //                 (= y (max x y))))
  slv.addSygusConstraint(tm.mkTerm(Kind::OR,
                                   {tm.mkTerm(Kind::EQUAL, {max_x_y, varX}),
                                    tm.mkTerm(Kind::EQUAL, {max_x_y, varY})}));

  // (constraint (= (+ (max x y) (min x y))
  //                (+ x y)))
  slv.addSygusConstraint(tm.mkTerm(Kind::EQUAL,
                                   {tm.mkTerm(Kind::ADD, {max_x_y, min_x_y}),
                                    tm.mkTerm(Kind::ADD, {varX, varY})}));

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
