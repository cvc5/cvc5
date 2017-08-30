import static org.junit.Assert.assertEquals;
import org.junit.Before;
import org.junit.Test;

import edu.nyu.acsys.CVC4.*;

public class Combination {
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
    smt.setOption("tlimit", new SExpr(100));
    smt.setOption("produce-models", new SExpr(true)); // Produce Models
    smt.setOption("output-language", new SExpr("cvc4")); // output-language
    smt.setOption("default-dag-thresh", new SExpr(0)); //Disable dagifying the output
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

    assertEquals(
        Result.Validity.VALID,
        smt.query(em.mkExpr(Kind.DISTINCT, x, y)).isValid()
    );

    assertEquals(
        Result.Sat.SAT,
        smt.checkSat(em.mkConst(true)).isSat()
    );
  }
}
