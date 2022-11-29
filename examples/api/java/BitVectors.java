/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Liana Hadarean, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the solving capabilities of the cvc5
 * bit-vector solver.
 *
 */

import io.github.cvc5.*;
import java.util.*;

public class BitVectors
{
  public static void main(String args[]) throws CVC5ApiException
  {
    Solver slv = new Solver();
    {
      slv.setLogic("QF_BV"); // Set the logic

      // The following example has been adapted from the book A Hacker's Delight by
      // Henry S. Warren.
      //
      // Given a variable x that can only have two values, a or b. We want to
      // assign to x a value other than the current one. The straightforward code
      // to do that is:
      //
      //(0) if (x == a ) x = b;
      //    else x = a;
      //
      // Two more efficient yet equivalent methods are:
      //
      //(1) x = a ⊕ b ⊕ x;
      //
      //(2) x = a + b - x;
      //
      // We will use cvc5 to prove that the three pieces of code above are all
      // equivalent by encoding the problem in the bit-vector theory.

      // Creating a bit-vector type of width 32
      Sort bitvector32 = slv.mkBitVectorSort(32);

      // Variables
      Term x = slv.mkConst(bitvector32, "x");
      Term a = slv.mkConst(bitvector32, "a");
      Term b = slv.mkConst(bitvector32, "b");

      // First encode the assumption that x must be Kind.EQUAL to a or b
      Term x_eq_a = slv.mkTerm(Kind.EQUAL, x, a);
      Term x_eq_b = slv.mkTerm(Kind.EQUAL, x, b);
      Term assumption = slv.mkTerm(Kind.OR, x_eq_a, x_eq_b);

      // Assert the assumption
      slv.assertFormula(assumption);

      // Introduce a new variable for the new value of x after assignment.
      Term new_x = slv.mkConst(bitvector32, "new_x"); // x after executing code (0)
      Term new_x_ = slv.mkConst(bitvector32, "new_x_"); // x after executing code (1) or (2)

      // Encoding code (0)
      // new_x = x == a ? b : a;
      Term ite = slv.mkTerm(Kind.ITE, x_eq_a, b, a);
      Term assignment0 = slv.mkTerm(Kind.EQUAL, new_x, ite);

      // Assert the encoding of code (0)
      System.out.println("Asserting " + assignment0 + " to cvc5 ");
      slv.assertFormula(assignment0);
      System.out.println("Pushing a new context.");
      slv.push();

      // Encoding code (1)
      // new_x_ = a xor b xor x
      Term a_xor_b_xor_x = slv.mkTerm(Kind.BITVECTOR_XOR, a, b, x);
      Term assignment1 = slv.mkTerm(Kind.EQUAL, new_x_, a_xor_b_xor_x);

      // Assert encoding to cvc5 in current context;
      System.out.println("Asserting " + assignment1 + " to cvc5 ");
      slv.assertFormula(assignment1);
      Term new_x_eq_new_x_ = slv.mkTerm(Kind.EQUAL, new_x, new_x_);

      System.out.println(" Check sat assuming: " + new_x_eq_new_x_.notTerm());
      System.out.println(" Expect UNSAT. ");
      System.out.println(" cvc5: " + slv.checkSatAssuming(new_x_eq_new_x_.notTerm()));
      System.out.println(" Popping context. ");
      slv.pop();

      // Encoding code (2)
      // new_x_ = a + b - x
      Term a_plus_b = slv.mkTerm(Kind.BITVECTOR_ADD, a, b);
      Term a_plus_b_minus_x = slv.mkTerm(Kind.BITVECTOR_SUB, a_plus_b, x);
      Term assignment2 = slv.mkTerm(Kind.EQUAL, new_x_, a_plus_b_minus_x);

      // Assert encoding to cvc5 in current context;
      System.out.println("Asserting " + assignment2 + " to cvc5 ");
      slv.assertFormula(assignment2);

      System.out.println(" Check sat assuming: " + new_x_eq_new_x_.notTerm());
      System.out.println(" Expect UNSAT. ");
      System.out.println(" cvc5: " + slv.checkSatAssuming(new_x_eq_new_x_.notTerm()));

      Term x_neq_x = slv.mkTerm(Kind.EQUAL, x, x).notTerm();
      Term[] v = new Term[] {new_x_eq_new_x_, x_neq_x};
      Term query = slv.mkTerm(Kind.AND, v);
      System.out.println(" Check sat assuming: " + query.notTerm());
      System.out.println(" Expect SAT. ");
      System.out.println(" cvc5: " + slv.checkSatAssuming(query.notTerm()));

      // Assert that a is odd
      Op extract_op = slv.mkOp(Kind.BITVECTOR_EXTRACT, 0, 0);
      Term lsb_of_a = slv.mkTerm(extract_op, a);
      System.out.println("Sort of " + lsb_of_a + " is " + lsb_of_a.getSort());
      Term a_odd = slv.mkTerm(Kind.EQUAL, lsb_of_a, slv.mkBitVector(1, 1));
      System.out.println("Assert " + a_odd);
      System.out.println("Check satisfiability.");
      slv.assertFormula(a_odd);
      System.out.println(" Expect sat. ");
      System.out.println(" cvc5: " + slv.checkSat());
    }
  }
}
