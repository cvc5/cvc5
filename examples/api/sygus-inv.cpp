/*********************                                                        */
/*! \file sygus-inv.cpp
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
 ** A simple demonstration of how to use the Sygus API to synthesize a simple
 ** invariant. Here is the same problem written in Sygus V2 format:
 **
 ** (set-logic LIA)
 **
 ** (synth-inv inv-f ((x Int)))
 **
 ** (define-fun pre-f ((x Int)) Bool
 **   (= x 0))
 ** (define-fun trans-f ((x Int) (xp Int)) Bool
 **   (ite (< x 10) (= xp (+ x 1)) (= xp x)))
 ** (define-fun post-f ((x Int)) Bool
 **   (<= x 10))
 **
 ** (inv-constraint inv-f pre-f trans-f post-f)
 **
 ** (check-synth)
 **
 ** The printed output to this example should be equivalent to:
 ** (define-fun inv-f ((x Int)) Bool (not (>= x 11)))
 **/

#include <cvc4/api/cvc4cpp.h>

#include <iostream>

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

  Term zero = slv.mkReal(0);
  Term one = slv.mkReal(1);
  Term ten = slv.mkReal(10);

  // declare input variables for functions
  Term x = slv.mkVar(integer, "x");
  Term xp = slv.mkVar(integer, "xp");

  // (ite (< x 10) (= xp (+ x 1)) (= xp x))
  Term ite = slv.mkTerm(ITE,
                        slv.mkTerm(LT, x, ten),
                        slv.mkTerm(EQUAL, xp, slv.mkTerm(PLUS, x, one)),
                        slv.mkTerm(EQUAL, xp, x));

  // define the pre-conditions, transition relations, and post-conditions
  Term pre_f = slv.defineFun("pre-f", {x}, boolean, slv.mkTerm(EQUAL, x, zero));
  Term trans_f = slv.defineFun("trans-f", {x, xp}, boolean, ite);
  Term post_f = slv.defineFun("post-f", {x}, boolean, slv.mkTerm(LEQ, x, ten));

  // declare the invariant-to-synthesize
  Term inv_f = slv.synthInv("inv-f", {x});

  slv.addSygusInvConstraint(inv_f, pre_f, trans_f, post_f);

  // print solutions if available
  if (slv.checkSynth().isUnsat())
  {
    // Output should be equivalent to:
    // (define-fun inv-f ((x Int)) Bool (not (>= x 11)))
    slv.printSynthSolution(std::cout);
  }

  return 0;
}
