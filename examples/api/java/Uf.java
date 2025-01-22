/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the capabilities of the cvc5 uf solver.
 */

import io.github.cvc5.*;
import java.util.Iterator;

public class Uf 
{
  public static void main(String[] args) throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver slv = new Solver(tm);
    {
      slv.setLogic("QF_UF");

      // Sorts
      Sort u = tm.mkUninterpretedSort("U");
      Sort bool = tm.getBooleanSort();
      Sort uTou = tm.mkFunctionSort(u, u);
      Sort uPred = tm.mkFunctionSort(u, bool);

      // Variables
      Term x = tm.mkConst(u, "x");
      Term y = tm.mkConst(u, "y");

      // Functions
      Term f = tm.mkConst(uTou, "f");
      Term p = tm.mkConst(uPred, "p");

      // Terms
      Term f_x = tm.mkTerm(Kind.APPLY_UF, f, x);
      Term f_y = tm.mkTerm(Kind.APPLY_UF, f, y);
      Term p_f_x = tm.mkTerm(Kind.APPLY_UF, p, f_x);
      Term p_f_y = tm.mkTerm(Kind.APPLY_UF, p, f_y);

      // Construct the assertions
      Term assertions = tm.mkTerm(Kind.AND,
          new Term[] {tm.mkTerm(Kind.EQUAL, x, f_x),
              tm.mkTerm(Kind.EQUAL, y, f_y),
              p_f_x.notTerm(),
              p_f_y});
      slv.assertFormula(assertions);

      System.out.println("Call checkSat to show that the assertions are satisfiable. \n"
          + "cvc5: " + slv.checkSat() + ".\n");
    
      Context.deletePointers();
    }
  }
}
