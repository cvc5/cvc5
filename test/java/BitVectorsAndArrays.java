/*********************                                                        */
/*! \file BitVectorsAndArrays.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Pat Hawks, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

import static org.junit.Assert.assertEquals;

import edu.stanford.CVC4.*;
import org.junit.Before;
import org.junit.Test;

public class BitVectorsAndArrays {
  static {
    System.loadLibrary("cvc4jni");
  }
  ExprManager em;
  SmtEngine smt;

  @Before
  public void initialize() {
    em = new ExprManager();
    smt = new SmtEngine(em);
  }

  @Test
  public void evaluatesExpression() {
    smt.setOption("produce-models", new SExpr(true));      // Produce Models
    smt.setOption("output-language", new SExpr("smtlib")); // output-language
    smt.setLogic("QF_AUFBV");                              // Set the logic

    // Consider the following code (where size is some previously defined constant):
    //
    //   Assert (current_array[0] > 0);
    //   for (unsigned i = 1; i < k; ++i) {
    //     current_array[i] = 2 * current_array[i - 1];
    //     Assert (current_array[i-1] < current_array[i]);
    //   }
    //
    // We want to check whether the assertion in the body of the for loop holds
    // throughout the loop.

    // Setting up the problem parameters
    int k = 4;                // number of unrollings (should be a power of 2)
    int index_size = log2(k); // size of the index

    // Types
    Type elementType = em.mkBitVectorType(32);
    Type indexType = em.mkBitVectorType(index_size);
    Type arrayType = em.mkArrayType(indexType, elementType);

    // Variables
    Expr current_array = em.mkVar("current_array", arrayType);

    // Making a bit-vector constant
    Expr zero = em.mkConst(new BitVector(index_size, 0));

    // Asserting that current_array[0] > 0
    Expr current_array0 = em.mkExpr(Kind.SELECT, current_array, zero);
    Expr current_array0_gt_0 = em.mkExpr(Kind.BITVECTOR_SGT, current_array0, em.mkConst(new BitVector(32, 0)));
    smt.assertFormula(current_array0_gt_0);

    // Building the assertions in the loop unrolling
    Expr index = em.mkConst(new BitVector(index_size, 0));
    Expr old_current = em.mkExpr(Kind.SELECT, current_array, index);
    Expr two = em.mkConst(new BitVector(32, 2));

    vectorExpr assertions = new vectorExpr();
    for (int i = 1; i < k; ++i) {
      index = em.mkConst(
          new BitVector(index_size, new edu.stanford.CVC4.Integer(i)));
      Expr new_current = em.mkExpr(Kind.BITVECTOR_MULT, two, old_current);
      // current[i] = 2 * current[i-1]
      current_array = em.mkExpr(Kind.STORE, current_array, index, new_current);
      // current[i-1] < current [i]
      Expr current_slt_new_current = em.mkExpr(Kind.BITVECTOR_SLT, old_current, new_current);
      assertions.add(current_slt_new_current);

      old_current = em.mkExpr(Kind.SELECT, current_array, index);
    }

    Expr query = em.mkExpr(Kind.NOT, em.mkExpr(Kind.AND, assertions));
    smt.assertFormula(query);

    Result.Sat expect = Result.Sat.SAT;
    Result.Sat actual = smt.checkSat(em.mkConst(true)).isSat();
    assertEquals(expect, actual);
  }

  private static int log2(int n) {
    return (int) Math.round(Math.log(n) / Math.log(2));
  }
}
