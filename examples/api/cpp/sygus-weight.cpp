/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A demonstration of the SyGuS weight API.
 *
 * Find a synthesis of 3*x using only `+` (weight 1) or `*` (weight 31),
 * constrained to have a total `w` weight of 2. The expected solution is
 * `(+ x (+ x x))`.
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
  slv.setLogic("NIA");

  Sort integer = tm.getIntegerSort();

  // declare input variables for the functions-to-synthesize
  Term x = tm.mkVar(integer, "x");

  // declare the grammar non-terminals
  Term start = tm.mkVar(integer, "Start");

  // define the rules
  Term zero = tm.mkInteger(0);
  Term one = tm.mkInteger(1);
  Term two = tm.mkInteger(2);
  Term three = tm.mkInteger(3);
  Term thirtyOne = tm.mkInteger(31);

  Term add = tm.mkTerm(Kind::ADD, {start, start});
  Term mult = tm.mkTerm(Kind::MULT, {start, start});

  // declare a weight attribute with a default of 0
  Weight w = slv.declareWeight("w");

  // create the grammar object
  Grammar g = slv.mkGrammar({x}, {start});

  // bind each non-terminal to its rules
  g.addRules(start, {zero, one, three, x});
  g.addRule(start, add, {{w, one}});
  g.addRule(start, mult, {{w, thirtyOne}});

  // declare the function-to-synthesize
  Term f = slv.synthFun("f", {x}, integer, g);

  // declare universal variables
  Term varX = slv.declareSygusVar("x", integer);

  Term fX = tm.mkTerm(Kind::APPLY_UF, {f, varX});
  Term threeX = tm.mkTerm(Kind::MULT, {three, varX});

  // add the semantic constraint: (= (f x) (* 3 x))
  slv.addSygusConstraint(tm.mkTerm(Kind::EQUAL, {fX, threeX}));

  // declare a weight symbol: (_ w f)
  Term wF = slv.mkWeightSymbol(w, f);

  // add the weight constraint: (= (_ w f) 2)
  slv.addSygusConstraint(tm.mkTerm(Kind::EQUAL, {wF, two}));

  // print solutions if available
  if (slv.checkSynth().hasSolution())
  {
    // Output should be equivalent to:
    // (
    //   (define-fun f ((x Int)) Int (+ x (+ x x)))
    // )
    std::vector<Term> terms = {f};
    utils::printSynthSolutions(terms, slv.getSynthSolutions(terms));
  }

  return 0;
}
