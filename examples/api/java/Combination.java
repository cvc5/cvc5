/*********************                                                        */
/*! \file Combination.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the capabilities of CVC4
 **
 ** A simple demonstration of how to use uninterpreted functions, combining this
 ** with arithmetic, and extracting a model at the end of a satisfiable query.
 ** The model is displayed using getValue().
 **/

import edu.stanford.CVC4.*;

public class Combination {
  private static void prefixPrintGetValue(SmtEngine smt, Expr e, int level) {
    for(int i = 0; i < level; ++i) { System.out.print('-'); }
    System.out.println("smt.getValue(" + e + ") -> " + smt.getValue(e));

    if(e.hasOperator()) {
      prefixPrintGetValue(smt, e.getOperator(), level + 1);
    }

    for(int i = 0; i < e.getNumChildren(); ++i) {
      Expr curr = e.getChild(i);
      prefixPrintGetValue(smt, curr, level + 1);
    }
  }

  public static void main(String[] args) {
    System.loadLibrary("cvc4jni");

    ExprManager em = new ExprManager();
    SmtEngine smt = new SmtEngine(em);

    smt.setOption("tlimit", new SExpr(100));
    smt.setOption("produce-models", new SExpr(true)); // Produce Models
    smt.setOption("output-language", new SExpr("cvc4")); // output-language
    smt.setOption("dag-thresh", new SExpr(0)); //Disable dagifying the output
    smt.setLogic("QF_UFLIRA");

    // Sorts
    SortType u = em.mkSort("u");
    Type integer = em.integerType();
    Type booleanType = em.booleanType();
    Type uToInt = em.mkFunctionType(u, integer);
    Type intPred = em.mkFunctionType(integer, booleanType);

    // Variables
    Expr x = em.mkVar("x", u);
    Expr y = em.mkVar("y", u);

    // Functions
    Expr f = em.mkVar("f", uToInt);
    Expr p = em.mkVar("p", intPred);

    // Constants
    Expr zero = em.mkConst(new Rational(0));
    Expr one = em.mkConst(new Rational(1));

    // Terms
    Expr f_x = em.mkExpr(Kind.APPLY_UF, f, x);
    Expr f_y = em.mkExpr(Kind.APPLY_UF, f, y);
    Expr sum = em.mkExpr(Kind.PLUS, f_x, f_y);
    Expr p_0 = em.mkExpr(Kind.APPLY_UF, p, zero);
    Expr p_f_y = em.mkExpr(Kind.APPLY_UF, p, f_y);

    // Construct the assumptions
    Expr assumptions =
      em.mkExpr(Kind.AND,
                em.mkExpr(Kind.LEQ, zero, f_x), // 0 <= f(x)
                em.mkExpr(Kind.LEQ, zero, f_y), // 0 <= f(y)
                em.mkExpr(Kind.LEQ, sum, one),  // f(x) + f(y) <= 1
                p_0.notExpr(),                  // not p(0)
                p_f_y);                         // p(f(y))
    smt.assertFormula(assumptions);

    System.out.println("Given the following assumptions:");
    System.out.println(assumptions);
    System.out.println("Prove x /= y is entailed. "
        + "CVC4 says: " + smt.checkEntailed(em.mkExpr(Kind.DISTINCT, x, y))
        + ".");

    System.out.println("Now we call checksat on a trivial query to show that");
    System.out.println("the assumptions are satisfiable: " +
                       smt.checkSat(em.mkConst(true)) + ".");

    System.out.println("Finally, after a SAT call, we recursively call smt.getValue(...) on " +
                       "all of the assumptions to see what the satisfying model looks like.");
    prefixPrintGetValue(smt, assumptions, 0);
  }
}
