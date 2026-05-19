/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A demonstration of the SyGuS 2.1 weight API.
 *
 * Synthesize 3*x using only `+` (weight 1) and `*` (weight 31), constrained
 * to have a total `w` weight of 2. The expected solution is (+ x (+ x x)).
 */

import static io.github.cvc5.Kind.*;

import io.github.cvc5.*;
import java.util.HashMap;
import java.util.Map;

public class SygusWeight
{
  public static void main(String args[]) throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver slv = new Solver(tm);

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

    Term add = tm.mkTerm(ADD, start, start);
    Term mult = tm.mkTerm(MULT, start, start);

    // declare a weight attribute with the default value of 0
    Weight w = slv.declareWeight("w");

    // create the grammar object
    Grammar g = slv.mkGrammar(new Term[] {x}, new Term[] {start});

    // bind each non-terminal to its rules
    g.addRules(start, new Term[] {zero, one, three, x});

    Map<Weight, Term> addWeights = new HashMap<>();
    addWeights.put(w, one);
    g.addRule(start, add, addWeights);

    Map<Weight, Term> multWeights = new HashMap<>();
    multWeights.put(w, thirtyOne);
    g.addRule(start, mult, multWeights);

    // declare the function-to-synthesize
    Term f = slv.synthFun("f", new Term[] {x}, integer, g);

    // declare universal variables
    Term varX = slv.declareSygusVar("x", integer);

    Term fX = tm.mkTerm(APPLY_UF, f, varX);
    Term threeX = tm.mkTerm(MULT, three, varX);

    // add the semantic constraint: (= (f x) (* 3 x))
    slv.addSygusConstraint(tm.mkTerm(EQUAL, fX, threeX));

    // declare the weight symbol (_ w f)
    Term wF = slv.mkWeightSymbol(w, f);

    // add the weight constraint: (= (_ w f) 2)
    slv.addSygusConstraint(tm.mkTerm(EQUAL, wF, two));

    // print the solution if available
    if (slv.checkSynth().hasSolution())
    {
      // Output should be equivalent to:
      // (define-fun f ((x Int)) Int (+ x (+ x x)))
      Term[] terms = new Term[] {f};
      Utils.printSynthSolutions(terms, slv.getSynthSolutions(terms));
    }
  }
}
