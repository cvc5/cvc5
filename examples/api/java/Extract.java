/******************************************************************************
 * Top contributors (to current version):
 *   Daniel Larraz, Mudathir Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

public class Extract
{
  public static void main(String args[]) throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver slv = new Solver(tm);
    {
      slv.setLogic("QF_BV"); // Set the logic

      Sort bitvector32 = tm.mkBitVectorSort(32);

      Term x = tm.mkConst(bitvector32, "a");

      Op ext_31_1 = tm.mkOp(Kind.BITVECTOR_EXTRACT, 31, 1);
      Term x_31_1 = tm.mkTerm(ext_31_1, x);

      Op ext_30_0 = tm.mkOp(Kind.BITVECTOR_EXTRACT, 30, 0);
      Term x_30_0 = tm.mkTerm(ext_30_0, x);

      Op ext_31_31 = tm.mkOp(Kind.BITVECTOR_EXTRACT, 31, 31);
      Term x_31_31 = tm.mkTerm(ext_31_31, x);

      Op ext_0_0 = tm.mkOp(Kind.BITVECTOR_EXTRACT, 0, 0);
      Term x_0_0 = tm.mkTerm(ext_0_0, x);

      Term eq = tm.mkTerm(Kind.EQUAL, x_31_1, x_30_0);
      System.out.println(" Asserting: " + eq);
      slv.assertFormula(eq);

      Term eq2 = tm.mkTerm(Kind.EQUAL, x_31_31, x_0_0);
      System.out.println(" Check entailment assuming: " + eq2);
      System.out.println(" Expect UNSAT. ");
      System.out.println(" cvc5: " + slv.checkSatAssuming(eq2.notTerm()));
    }
    Context.deletePointers();
  }
}
