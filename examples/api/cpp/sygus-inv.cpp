/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the Sygus API.
 *
 * A simple demonstration of how to use the Sygus API to synthesize a simple
 * invariant.
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

  Term zero = tm.mkInteger(0);
  Term one = tm.mkInteger(1);
  Term ten = tm.mkInteger(10);

  // declare input variables for functions
  Term x = tm.mkVar(integer, "x");
  Term xp = tm.mkVar(integer, "xp");

  // (ite (< x 10) (= xp (+ x 1)) (= xp x))
  Term ite =
      tm.mkTerm(Kind::ITE,
                {tm.mkTerm(Kind::LT, {x, ten}),
                 tm.mkTerm(Kind::EQUAL, {xp, tm.mkTerm(Kind::ADD, {x, one})}),
                 tm.mkTerm(Kind::EQUAL, {xp, x})});

  // define the pre-conditions, transition relations, and post-conditions
  Term pre_f =
      slv.defineFun("pre-f", {x}, boolean, tm.mkTerm(Kind::EQUAL, {x, zero}));
  Term trans_f = slv.defineFun("trans-f", {x, xp}, boolean, ite);
  Term post_f =
      slv.defineFun("post-f", {x}, boolean, tm.mkTerm(Kind::LEQ, {x, ten}));

  // declare the invariant-to-synthesize
  Term inv_f = slv.synthFun("inv-f", {x}, boolean);

  slv.addSygusInvConstraint(inv_f, pre_f, trans_f, post_f);

  // print solutions if available
  if (slv.checkSynth().hasSolution())
  {
    // Output should be equivalent to:
    // (
    //   (define-fun inv-f ((x Int)) Bool (not (>= x 11)))
    // )
    std::vector<Term> terms = {inv_f};
    utils::printSynthSolutions(terms, slv.getSynthSolutions(terms));
  }

  return 0;
}
