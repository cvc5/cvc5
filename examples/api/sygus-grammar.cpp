/*********************                                                        */
/*! \file sygus-grammar.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the Sygus API.
 **
 ** A simple demonstration of how to use Grammar to add syntax constraints to
 ** the Sygus solution for the identity function. Here is the same problem
 ** written in Sygus V2 format:
 **
 ** (set-logic LIA)
 **
 ** (synth-fun id1 ((x Int)) Int
 **   ((Start Int)) ((Start Int ((- x) (+ x Start)))))
 **
 ** (synth-fun id2 ((x Int)) Int
 **   ((Start Int)) ((Start Int ((Variable Int) (- x) (+ x Start)))))
 **
 ** (synth-fun id3 ((x Int)) Int
 **   ((Start Int)) ((Start Int (0 (- x) (+ x Start)))))
 **
 ** (synth-fun id4 ((x Int)) Int
 **   ((Start Int)) ((Start Int ((- x) (+ x Start)))))
 **
 ** (declare-var x Int)
 **
 ** (constraint (= (id1 x) (id2 x) (id3 x) (id4 x) x))
 **
 ** (check-synth)
 **
 ** The printed output to this example should look like:
 ** (define-fun id1 ((x Int)) Int (+ x (+ x (- x))))
 ** (define-fun id2 ((x Int)) Int x)
 ** (define-fun id3 ((x Int)) Int (+ x 0))
 ** (define-fun id4 ((x Int)) Int (+ x (+ x (- x))))
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

  // declare input variable for the function-to-synthesize
  Term x = slv.mkVar(integer, "x");

  // declare the grammar non-terminal
  Term start = slv.mkVar(integer, "Start");

  // define the rules
  Term zero = slv.mkReal(0);
  Term neg_x = slv.mkTerm(UMINUS, x);
  Term plus = slv.mkTerm(PLUS, x, start);

  // create the grammar object
  Grammar g1 = slv.mkSygusGrammar({x}, {start});

  // bind each non-terminal to its rules
  g1.addRules(start, {neg_x, plus});

  // copy the first grammar with all of its non-termainals and their rules
  Grammar g2 = g1;
  Grammar g3 = g1;

  // add parameters as rules for the start symbol. Similar to "(Variable Int)"
  g2.addAnyVariable(start);

  // declare the functions-to-synthesize
  Term id1 = slv.synthFun("id1", {x}, integer, g1);
  Term id2 = slv.synthFun("id2", {x}, integer, g2);

  g3.addRule(start, zero);

  Term id3 = slv.synthFun("id3", {x}, integer, g3);

  // g1 is reusable as long as it remains unmodified after first use
  Term id4 = slv.synthFun("id4", {x}, integer, g1);

  // declare universal variables.
  Term varX = slv.mkSygusVar(integer, "x");

  Term id1_x = slv.mkTerm(APPLY_UF, id1, varX);
  Term id2_x = slv.mkTerm(APPLY_UF, id2, varX);
  Term id3_x = slv.mkTerm(APPLY_UF, id3, varX);
  Term id4_x = slv.mkTerm(APPLY_UF, id4, varX);

  // add semantic constraints
  // (constraint (= (id1 x) (id2 x) (id3 x) (id4 x) x))
  slv.addSygusConstraint(slv.mkTerm(EQUAL, {id1_x, id2_x, id3_x, id4_x, varX}));

  // print solutions if available
  if (slv.checkSynth().isUnsat())
  {
    // Output should be equivalent to:
    // (define-fun id1 ((x Int)) Int (+ x (+ x (- x))))
    // (define-fun id2 ((x Int)) Int x)
    // (define-fun id3 ((x Int)) Int (+ x 0))
    // (define-fun id4 ((x Int)) Int (+ x (+ x (- x))))
    slv.printSynthSolution(std::cout);
  }

  return 0;
}
