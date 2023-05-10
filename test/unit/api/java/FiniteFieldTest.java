/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the finite-field related API methods.
 *
 * In its own file because it requires cvc5 to be built with --cocoa.
 */

package tests;

import static io.github.cvc5.Kind.*;
import static io.github.cvc5.RoundingMode.*;
import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import io.github.cvc5.modes.BlockModelsMode;
import io.github.cvc5.modes.LearnedLitType;
import io.github.cvc5.modes.ProofComponent;
import java.math.BigInteger;
import java.util.*;
import java.util.concurrent.atomic.AtomicReference;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.function.Executable;

class FiniteFieldTest
{
  private Solver d_solver;

  @BeforeEach
  void setUp()
  {
    d_solver = new Solver();
  }

  @AfterEach
  void tearDown()
  {
    Context.deletePointers();
  }

  @Test
  void finiteFieldTest() throws CVC5ApiException
  {
    d_solver.setLogic("QF_FF"); // Set the logic

    Sort f5 = d_solver.mkFiniteFieldSort("5");
    Term a = d_solver.mkConst(f5, "a");
    Term b = d_solver.mkConst(f5, "b");
    Term z = d_solver.mkFiniteFieldElem("0", f5);

    assertEquals(f5.isFiniteField(), true);
    assertEquals(f5.getFiniteFieldSize(), "5");
    assertEquals(z.isFiniteFieldValue(), true);
    assertEquals(z.getFiniteFieldValue(), "0");

    Term inv =
      d_solver.mkTerm(Kind.EQUAL,
          d_solver.mkTerm(Kind.FINITE_FIELD_ADD,
            d_solver.mkTerm(Kind.FINITE_FIELD_MULT, a, b),
            d_solver.mkFiniteFieldElem("-1", f5)),
          z);

    Term aIsTwo =
      d_solver.mkTerm(Kind.EQUAL,
          d_solver.mkTerm(Kind.FINITE_FIELD_ADD,
            a,
            d_solver.mkFiniteFieldElem("-2", f5)),
          z);

    d_solver.assertFormula(inv);
    d_solver.assertFormula(aIsTwo);

    Result r = d_solver.checkSat();
    assertEquals(r.isSat(), true);

    Term bIsTwo =
      d_solver.mkTerm(Kind.EQUAL,
          d_solver.mkTerm(Kind.FINITE_FIELD_ADD,
            b,
            d_solver.mkFiniteFieldElem("-2", f5)),
          z);

    d_solver.assertFormula(bIsTwo);
    r = d_solver.checkSat();
    assertEquals(r.isSat(), false);
  }
}
