/******************************************************************************
 * Top contributors (to current version):
 *   Hans-Jörg Schurr, Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the guards of the Java API functions.
 */

package tests;
import static io.github.cvc5.Kind.*;
import static io.github.cvc5.SortKind.*;
import static io.github.cvc5.ProofRule.*;
import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class ProofTest
{
  private TermManager d_tm;
  private Solver d_solver;

  @BeforeEach
  void setUp()
  {
    d_tm = new TermManager();
    d_solver = new Solver(d_tm);
  }

  @AfterEach
  void tearDown()
  {
    Context.deletePointers();
  }

  Proof create_proof() throws CVC5ApiException
  {
    d_solver.setOption("produce-proofs", "true");

    Sort uSort = d_tm.mkUninterpretedSort("u");
    Sort intSort = d_tm.getIntegerSort();
    Sort boolSort = d_tm.getBooleanSort();
    Sort uToIntSort = d_tm.mkFunctionSort(uSort, intSort);
    Sort intPredSort = d_tm.mkFunctionSort(intSort, boolSort);

    Term x = d_tm.mkConst(uSort, "x");
    Term y = d_tm.mkConst(uSort, "y");
    Term f = d_tm.mkConst(uToIntSort, "f");
    Term p = d_tm.mkConst(intPredSort, "p");
    Term zero = d_tm.mkInteger(0);
    Term one = d_tm.mkInteger(1);
    Term f_x = d_tm.mkTerm(Kind.APPLY_UF, f, x);
    Term f_y = d_tm.mkTerm(Kind.APPLY_UF, f, y);
    Term sum = d_tm.mkTerm(Kind.ADD, f_x, f_y);
    Term p_0 = d_tm.mkTerm(Kind.APPLY_UF, p, zero);
    Term p_f_y = d_tm.mkTerm(APPLY_UF, p, f_y);
    d_solver.assertFormula(d_tm.mkTerm(Kind.GT, zero, f_x));
    d_solver.assertFormula(d_tm.mkTerm(Kind.GT, zero, f_y));
    d_solver.assertFormula(d_tm.mkTerm(Kind.GT, sum, one));
    d_solver.assertFormula(p_0);
    d_solver.assertFormula(p_f_y.notTerm());
    assertTrue(d_solver.checkSat().isUnsat());

    return d_solver.getProof()[0];
  }

  @Test
  void getRule() throws CVC5ApiException
  {
    Proof proof = create_proof();
    assertEquals(ProofRule.SCOPE, proof.getRule());
  }

  @Test
  void getResult() throws CVC5ApiException
  {
    Proof proof = create_proof();
    assertDoesNotThrow(() -> proof.getResult());
  }

  @Test
  void getChildren() throws CVC5ApiException
  {
    Proof proof = create_proof();
    Proof[] children = proof.getChildren();
    assertNotEquals(0, children.length);
  }

  @Test
  void getArguments() throws CVC5ApiException
  {
    Proof proof = create_proof();
    assertDoesNotThrow(() -> proof.getArguments());
  }

}
