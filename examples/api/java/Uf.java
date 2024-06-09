/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
    Solver slv = new Solver();
    {
      slv.setLogic("QF_UF");

      // Sorts
      Sort u = slv.mkUninterpretedSort("U");
      Sort bool = slv.getBooleanSort();
      Sort uTou = slv.mkFunctionSort(u, u);
      Sort uPred = slv.mkFunctionSort(u, bool);

      // Variables
      Term x = slv.mkConst(u, "x");
      Term y = slv.mkConst(u, "y");

      // Functions
      Term f = slv.mkConst(uTou, "f");
      Term p = slv.mkConst(uPred, "p");

      // Terms
      Term f_x = slv.mkTerm(Kind.APPLY_UF, f, x);
      Term f_y = slv.mkTerm(Kind.APPLY_UF, f, y);
      Term p_f_x = slv.mkTerm(Kind.APPLY_UF, p, f_x);
      Term p_f_y = slv.mkTerm(Kind.APPLY_UF, p, f_y);

      // Construct the assertions
      Term assertions = slv.mkTerm(Kind.AND,
          new Term[] {
              slv.mkTerm(Kind.EQUAL, x, f_x),
              slv.mkTerm(Kind.EQUAL, y, f_y),
              p_f_x.notTerm(), 
              p_f_y 
          });
      slv.assertFormula(assertions);

      System.out.println("Call checkSat to show that the assertions are satisfiable. \n"
          + "cvc5: " + slv.checkSat() + ".\n");
    
      Context.deletePointers();
    }
  }
}
