import static org.junit.Assert.assertEquals;
import org.junit.Before;
import org.junit.Test;

import edu.nyu.acsys.CVC4.*;

public class HelloWorld {
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
    Expr helloworld = em.mkVar("Hello World!", em.booleanType());
    Result.Validity expect = Result.Validity.INVALID;
    Result.Validity actual = smt.query(helloworld).isValid();
    assertEquals(actual, expect);
  }
}
