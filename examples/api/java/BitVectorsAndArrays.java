/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Daniel Larraz, Morgan Deters
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
import java.util.*;

public class BitVectorsAndArrays
{
  private static int log2(int n)
  {
    return (int) Math.round(Math.log(n) / Math.log(2));
  }

  public static void main(String[] args) throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver slv = new Solver(tm);
    {
      slv.setOption("produce-models", "true"); // Produce Models
      slv.setOption("output-language", "smtlib"); // output-language
      slv.setLogic("QF_ABV"); // Set the logic

      // Consider the following code (where size is some previously defined constant):
      //
      //
      //   Assert (current_array[0] > 0);
      //   for (unsigned i = 1; i < k; ++i) {
      //     current_array[i] = 2 * current_array[i - 1];
      //     Assert (current_array[i-1] < current_array[i]);
      //     }
      //
      // We want to check whether the assertion in the body of the for loop holds
      // throughout the loop.

      // Setting up the problem parameters
      int k = 4; // number of unrollings (should be a power of 2)
      int index_size = log2(k); // size of the index

      // Sorts
      Sort elementSort = tm.mkBitVectorSort(32);
      Sort indexSort = tm.mkBitVectorSort(index_size);
      Sort arraySort = tm.mkArraySort(indexSort, elementSort);

      // Variables
      Term current_array = tm.mkConst(arraySort, "current_array");

      // Making a bit-vector constant
      Term zero = tm.mkBitVector(index_size, 0);

      // Asserting that current_array[0] > 0
      Term current_array0 = tm.mkTerm(Kind.SELECT, current_array, zero);
      Term current_array0_gt_0 =
          tm.mkTerm(Kind.BITVECTOR_SGT, current_array0, tm.mkBitVector(32, 0));
      slv.assertFormula(current_array0_gt_0);

      // Building the assertions in the loop unrolling
      Term index = tm.mkBitVector(index_size, 0);
      Term old_current = tm.mkTerm(Kind.SELECT, current_array, index);
      Term two = tm.mkBitVector(32, 2);

      List<Term> assertions = new ArrayList<Term>();
      for (int i = 1; i < k; ++i)
      {
        index = tm.mkBitVector(index_size, i);
        Term new_current = tm.mkTerm(Kind.BITVECTOR_MULT, two, old_current);
        // current[i] = 2 * current[i-1]
        current_array = tm.mkTerm(Kind.STORE, current_array, index, new_current);
        // current[i-1] < current [i]
        Term current_slt_new_current = tm.mkTerm(Kind.BITVECTOR_SLT, old_current, new_current);
        assertions.add(current_slt_new_current);

        old_current = tm.mkTerm(Kind.SELECT, current_array, index);
      }

      Term query = tm.mkTerm(Kind.NOT, tm.mkTerm(Kind.AND, assertions.toArray(new Term[0])));

      System.out.println("Asserting " + query + " to cvc5 ");
      slv.assertFormula(query);
      System.out.println("Expect sat. ");
      System.out.println("cvc5: " + slv.checkSatAssuming(tm.mkTrue()));

      // Getting the model
      System.out.println("The satisfying model is: ");
      System.out.println("  current_array = " + slv.getValue(current_array));
      System.out.println("  current_array[0] = " + slv.getValue(current_array0));
    }
    Context.deletePointers();
  }
}
