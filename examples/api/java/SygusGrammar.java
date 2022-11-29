/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Andres Noetzli
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
 * A simple demonstration of how to use Grammar to add syntax constraints to
 * the Sygus solution for the identity function. This is a direct translation
 * of sygus-grammar.cpp.
 */

import static io.github.cvc5.Kind.*;

import io.github.cvc5.*;

public class SygusGrammar
{
  public static void main(String args[]) throws CVC5ApiException
  {
    Solver slv = new Solver();
    {
      // required options
      slv.setOption("sygus", "true");
      slv.setOption("incremental", "false");

      // set the logic
      slv.setLogic("LIA");

      Sort integer = slv.getIntegerSort();

      // declare input variable for the function-to-synthesize
      Term x = slv.mkVar(integer, "x");

      // declare the grammar non-terminal
      Term start = slv.mkVar(integer, "Start");

      // define the rules
      Term zero = slv.mkInteger(0);
      Term neg_x = slv.mkTerm(NEG, x);
      Term plus = slv.mkTerm(ADD, x, start);

      // create the grammar object
      Grammar g1 = slv.mkGrammar(new Term[] {x}, new Term[] {start});

      // bind each non-terminal to its rules
      g1.addRules(start, new Term[] {neg_x, plus});

      // copy the first grammar with all of its non-terminals and their rules
      Grammar g2 = new Grammar(g1);
      Grammar g3 = new Grammar(g1);

      // add parameters as rules for the start symbol. Similar to "(Variable Int)"
      g2.addAnyVariable(start);

      // declare the functions-to-synthesize
      Term id1 = slv.synthFun("id1", new Term[] {x}, integer, g1);
      Term id2 = slv.synthFun("id2", new Term[] {x}, integer, g2);

      g3.addRule(start, zero);

      Term id3 = slv.synthFun("id3", new Term[] {x}, integer, g3);

      // g1 is reusable as long as it remains unmodified after first use
      Term id4 = slv.synthFun("id4", new Term[] {x}, integer, g1);

      // declare universal variables.
      Term varX = slv.declareSygusVar("x", integer);

      Term id1_x = slv.mkTerm(APPLY_UF, id1, varX);
      Term id2_x = slv.mkTerm(APPLY_UF, id2, varX);
      Term id3_x = slv.mkTerm(APPLY_UF, id3, varX);
      Term id4_x = slv.mkTerm(APPLY_UF, id4, varX);

      // add semantic constraints
      // (constraint (= (id1 x) (id2 x) (id3 x) (id4 x) x))
      slv.addSygusConstraint(slv.mkTerm(EQUAL, new Term[] {id1_x, id2_x, id3_x, id4_x, varX}));

      // print solutions if available
      if (slv.checkSynth().hasSolution())
      {
        // Output should be equivalent to:
        // (
        //   (define-fun id1 ((x Int)) Int (+ x (+ x (- x))))
        //   (define-fun id2 ((x Int)) Int x)
        //   (define-fun id3 ((x Int)) Int (+ x 0))
        //   (define-fun id4 ((x Int)) Int (+ x (+ x (- x))))
        // )
        Term[] terms = new Term[] {id1, id2, id3, id4};
        Utils.printSynthSolutions(terms, slv.getSynthSolutions(terms));
      }
    }
  }
}
