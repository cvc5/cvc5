package cvc;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class SolverTest
{
  private Solver d_solver;

  @BeforeEach void setUp()
  {
    d_solver = new Solver();
  }

  @AfterEach void tearDown()
  {
    d_solver.deletePointer();
  }

  @Test void setLogic()
  {
    assertDoesNotThrow(() -> d_solver.setLogic("AUFLIRA"));
    assertThrows(CVCApiException.class, () -> d_solver.setLogic("AF_BV"));
    // TODO: enable this when mkTrue is added to Solver
    // d_solver.assertFormula(d_solver.mkTrue());
    // assertThrows(CVCApiException.class, () -> d_solver.setLogic("AUFLIRA"));
  }
}