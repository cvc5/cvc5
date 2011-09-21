import edu.nyu.acsys.CVC4.CVC4;

import edu.nyu.acsys.CVC4.SmtEngine;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Type;
import edu.nyu.acsys.CVC4.BoolExpr;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Configuration;

//import edu.nyu.acsys.CVC4.Exception;

import edu.nyu.acsys.CVC4.Parser;
import edu.nyu.acsys.CVC4.ParserBuilder;

public class CVC4JavaTest {
  public static void main(String[] args) {
    try {
      System.loadLibrary("cvc4bindings_java");

      CVC4.getDebugChannel().on("current");

System.out.println(Configuration.about());
System.out.println("constructing");

      ExprManager em = new ExprManager();
      SmtEngine smt = new SmtEngine(em);

System.out.println("getting type");
      Type t = em.booleanType();
System.out.println("making vars");
      Expr a = em.mkVar("a", em.booleanType());
      Expr b = em.mkVar("b", em.booleanType());
System.out.println("making sausage");
      BoolExpr e = new BoolExpr(em.mkExpr(Kind.AND, a, b));

System.out.println("about to check");

      System.out.println(smt.checkSat(e));

      System.out.println(smt.getStatisticsRegistry());

      System.exit(1);
    } catch(Exception e) {
      System.err.println(e);
      System.exit(1);
    }
  }
}

