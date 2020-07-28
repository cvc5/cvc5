/*********************                                                        */
/*! \file BitVectors.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Liana Hadarean, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the solving capabilities of the CVC4
 ** bit-vector solver.
 **
 **/

import edu.stanford.CVC4.*;

public class BitVectors {
  public static void main(String[] args) {
    System.loadLibrary("cvc4jni");

    ExprManager em = new ExprManager();
    SmtEngine smt = new SmtEngine(em);

    smt.setLogic("QF_BV"); // Set the logic

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
    // We will use CVC4 to prove that the three pieces of code above are all
    // equivalent by encoding the problem in the bit-vector theory.

    // Creating a bit-vector type of width 32
    Type bitvector32 = em.mkBitVectorType(32);

    // Variables
    Expr x = em.mkVar("x", bitvector32);
    Expr a = em.mkVar("a", bitvector32);
    Expr b = em.mkVar("b", bitvector32);

    // First encode the assumption that x must be equal to a or b
    Expr x_eq_a = em.mkExpr(Kind.EQUAL, x, a);
    Expr x_eq_b = em.mkExpr(Kind.EQUAL, x, b);
    Expr assumption = em.mkExpr(Kind.OR, x_eq_a, x_eq_b);

    // Assert the assumption
    smt.assertFormula(assumption);

    // Introduce a new variable for the new value of x after assignment.
    Expr new_x = em.mkVar("new_x", bitvector32); // x after executing code (0)
    Expr new_x_ = em.mkVar("new_x_", bitvector32); // x after executing code (1) or (2)

    // Encoding code (0)
    // new_x = x == a ? b : a;
    Expr ite = em.mkExpr(Kind.ITE, x_eq_a, b, a);
    Expr assignment0 = em.mkExpr(Kind.EQUAL, new_x, ite);

    // Assert the encoding of code (0)
    System.out.println("Asserting " + assignment0 + " to CVC4 ");
    smt.assertFormula(assignment0);
    System.out.println("Pushing a new context.");
    smt.push();

    // Encoding code (1)
    // new_x_ = a xor b xor x
    Expr a_xor_b_xor_x = em.mkExpr(Kind.BITVECTOR_XOR, a, b, x);
    Expr assignment1 = em.mkExpr(Kind.EQUAL, new_x_, a_xor_b_xor_x);

    // Assert encoding to CVC4 in current context;
    System.out.println("Asserting " + assignment1 + " to CVC4 ");
    smt.assertFormula(assignment1);
    Expr new_x_eq_new_x_ = em.mkExpr(Kind.EQUAL, new_x, new_x_);

    System.out.println(" Querying: " + new_x_eq_new_x_);
    System.out.println(" Expect entailed. ");
    System.out.println(" CVC4: " + smt.checkEntailed(new_x_eq_new_x_));
    System.out.println(" Popping context. ");
    smt.pop();

    // Encoding code (2)
    // new_x_ = a + b - x
    Expr a_plus_b = em.mkExpr(Kind.BITVECTOR_PLUS, a, b);
    Expr a_plus_b_minus_x = em.mkExpr(Kind.BITVECTOR_SUB, a_plus_b, x);
    Expr assignment2 = em.mkExpr(Kind.EQUAL, new_x_, a_plus_b_minus_x);

    // Assert encoding to CVC4 in current context;
    System.out.println("Asserting " + assignment2 + " to CVC4 ");
    smt.assertFormula(assignment2);

    System.out.println(" Querying: " + new_x_eq_new_x_);
    System.out.println(" Expect entailed. ");
    System.out.println(" CVC4: " + smt.checkEntailed(new_x_eq_new_x_));
  }
}
