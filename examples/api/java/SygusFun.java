/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Aina Niemetz
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
 * functions. This is a direct translation of sygus-fun.cpp.
 */

import static io.github.cvc5.Kind.*;

import io.github.cvc5.*;

public class SygusFun
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
      Sort bool = slv.getBooleanSort();

      // declare input variables for the functions-to-synthesize
      Term x = slv.mkVar(integer, "x");
      Term y = slv.mkVar(integer, "y");

      // declare the grammar non-terminals
      Term start = slv.mkVar(integer, "Start");
      Term start_bool = slv.mkVar(bool, "StartBool");

      // define the rules
      Term zero = slv.mkInteger(0);
      Term one = slv.mkInteger(1);

      Term plus = slv.mkTerm(ADD, start, start);
      Term minus = slv.mkTerm(SUB, start, start);
      Term ite = slv.mkTerm(ITE, start_bool, start, start);

      Term And = slv.mkTerm(AND, start_bool, start_bool);
      Term Not = slv.mkTerm(NOT, start_bool);
      Term leq = slv.mkTerm(LEQ, start, start);

      // create the grammar object
      Grammar g = slv.mkGrammar(new Term[] {x, y}, new Term[] {start, start_bool});

      // bind each non-terminal to its rules
      g.addRules(start, new Term[] {zero, one, x, y, plus, minus, ite});
      g.addRules(start_bool, new Term[] {And, Not, leq});

      // declare the functions-to-synthesize. Optionally, provide the grammar
      // constraints
      Term max = slv.synthFun("max", new Term[] {x, y}, integer, g);
      Term min = slv.synthFun("min", new Term[] {x, y}, integer);

      // declare universal variables.
      Term varX = slv.declareSygusVar("x", integer);
      Term varY = slv.declareSygusVar("y", integer);

      Term max_x_y = slv.mkTerm(APPLY_UF, max, varX, varY);
      Term min_x_y = slv.mkTerm(APPLY_UF, min, varX, varY);

      // add semantic constraints
      // (constraint (>= (max x y) x))
      slv.addSygusConstraint(slv.mkTerm(GEQ, max_x_y, varX));

      // (constraint (>= (max x y) y))
      slv.addSygusConstraint(slv.mkTerm(GEQ, max_x_y, varY));

      // (constraint (or (= x (max x y))
      //                 (= y (max x y))))
      slv.addSygusConstraint(
          slv.mkTerm(OR, slv.mkTerm(EQUAL, max_x_y, varX), slv.mkTerm(EQUAL, max_x_y, varY)));

      // (constraint (= (+ (max x y) (min x y))
      //                (+ x y)))
      slv.addSygusConstraint(
          slv.mkTerm(EQUAL, slv.mkTerm(ADD, max_x_y, min_x_y), slv.mkTerm(ADD, varX, varY)));

      // print solutions if available
      if (slv.checkSynth().hasSolution())
      {
        // Output should be equivalent to:
        // (
        //   (define-fun max ((x Int) (y Int)) Int (ite (<= x y) y x))
        //   (define-fun min ((x Int) (y Int)) Int (ite (<= x y) x y))
        // )
        Term[] terms = new Term[] {max, min};
        Utils.printSynthSolutions(terms, slv.getSynthSolutions(terms));
      }
    }
  }
}
