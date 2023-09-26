import static io.github.cvc5.Kind.*;
import io.github.cvc5.*;

public class Leak {
  public static void main(String[] args) {
    while (true) {
      Solver solver = new Solver();
      Term x = solver.mkConst(solver.getIntegerSort());
      Term y = solver.mkConst(solver.getIntegerSort());
      Term two = solver.mkInteger(2);
      // x = 2 AND y = 2*x
      Term assertion = x.eqTerm(two).andTerm(y.eqTerm(solver.mkTerm(Kind.MULT, x, two)));
      solver.assertFormula(assertion);
      Result result = solver.checkSat();
      if (!result.isSat()) {
        System.exit(1);
      }
      Context.deletePointers();      
    }
  }
}
