/******************************************************************************
 * Top contributors (to current version):
 *   Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple test for cvc5.Solver.resetAssertions()
 *
 * This indirectly also tests some corner cases w.r.t. context-dependent
 * datastructures: resetAssertions() pops the contexts to zero but some
 * context-dependent datastructures are created at level 1, which the
 * datastructure needs to handle properly problematic.
 */

import io.github.cvc5.*;

public class ResetAssertions
{
  public static void main(String[] args)
  {
    TermManager tm = new TermManager();
    Solver slv = new Solver(tm);
    slv.setOption("incremental", "true");

    Sort real = tm.getRealSort();
    Term x = tm.mkConst(real, "x");
    Term four = tm.mkReal(4);
    Term xEqFour = tm.mkTerm(Kind.EQUAL, x, four);
    slv.assertFormula(xEqFour);
    System.out.println(slv.checkSat());

    slv.resetAssertions();

    Sort elementType = tm.getIntegerSort();
    Sort indexType = tm.getIntegerSort();
    Sort arrayType = tm.mkArraySort(indexType, elementType);
    Term array = tm.mkConst(arrayType, "array");
    Term fourInt = tm.mkInteger(4);
    Term arrayAtFour = tm.mkTerm(Kind.SELECT, array, fourInt);
    Term ten = tm.mkInteger(10);
    Term arrayAtFourEqTen = tm.mkTerm(Kind.EQUAL, arrayAtFour, ten);
    slv.assertFormula(arrayAtFourEqTen);
    System.out.println(slv.checkSat());
  }
}
