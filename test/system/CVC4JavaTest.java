import edu.nyu.acsys.CVC4.CVC4;

import edu.nyu.acsys.CVC4.SmtEngine;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Type;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Result;
import edu.nyu.acsys.CVC4.Configuration;

//import edu.nyu.acsys.CVC4.Exception;

import edu.nyu.acsys.CVC4.Parser;
import edu.nyu.acsys.CVC4.ParserBuilder;

public class CVC4JavaTest {
  public static void main(String[] args) {
    try {
      System.loadLibrary("cvc4jni");

      //CVC4.getDebugChannel().on("current");

      System.out.println(Configuration.about());

      String[] tags = Configuration.getDebugTags();
      System.out.print("available debug tags:");
      for(int i = 0; i < tags.length; ++i) {
        System.out.print(" " + tags[i]);
      }
      System.out.println();

      ExprManager em = new ExprManager();
      SmtEngine smt = new SmtEngine(em);

      Type t = em.booleanType();
      Expr a = em.mkVar("a", em.booleanType());
      Expr b = em.mkVar("b", em.booleanType());
      Expr e = new Expr(em.mkExpr(Kind.AND, a, b, new Expr(a).notExpr()));
      System.out.println("==> " + e);

      Result r = smt.checkSat(e);
      boolean correct = r.isSat() == Result.Sat.UNSAT;

      System.out.println(smt.getStatistics());

      System.exit(correct ? 0 : 1);
    } catch(Exception e) {
      System.err.println(e);
      System.exit(1);
    }
  }
}

