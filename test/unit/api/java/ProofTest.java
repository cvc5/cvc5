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

  Proof createProof() throws CVC5ApiException
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

  Proof createRewriteProof() throws CVC5ApiException
  {
    d_solver.setOption("produce-proofs", "true");
    d_solver.setOption("proof-granularity", "dsl-rewrite");
    Sort intSort = d_tm.getIntegerSort();
    Term x = d_tm.mkConst(intSort, "x");
    Term twoX = d_tm.mkTerm(Kind.MULT, new Term[]{d_tm.mkInteger(2), x});
    Term xPlusX = d_tm.mkTerm(Kind.ADD, new Term[]{x, x});
    d_solver.assertFormula(
        d_tm.mkTerm(Kind.DISTINCT, new Term[]{twoX, xPlusX}));
    d_solver.checkSat();
    return d_solver.getProof()[0];
  }

  @Test
  void nullProof() throws CVC5ApiException
  {
    Proof proof = new Proof();
    assertEquals(proof.getRule(), ProofRule.UNKNOWN);
    assertEquals(ProofRule.UNKNOWN.hashCode(), ProofRule.UNKNOWN.hashCode());
    assertTrue(proof.getResult().isNull());
    assertTrue(proof.getChildren().length == 0);
    assertTrue(proof.getArguments().length == 0);
  }

  @Test
  void equalHash() throws CVC5ApiException
  {
    Proof x = createProof();
    Proof y = x.getChildren()[0];
    Proof n = new Proof();
    assertTrue(x.equals(x));
    assertFalse(x.equals(y));
    assertFalse(x.equals(n));

    assertTrue(x.hashCode() == x.hashCode());
  }

  @Test
  void getRule() throws CVC5ApiException
  {
    Proof proof = createProof();
    assertEquals(ProofRule.SCOPE, proof.getRule());
  }

  @Test
  void getRewriteRule() throws CVC5ApiException
  {
    Proof proof = createRewriteProof();
    assertThrows(CVC5ApiException.class, () -> proof.getRewriteRule());
    ProofRule rule;
    List<Proof> stack = new ArrayList<Proof>();
    stack.add(proof);
    Proof curr;
    do
    {
      curr = stack.get(stack.size() - 1);
      stack.remove(stack.size() - 1);
      rule = curr.getRule();
      Proof[] children = curr.getChildren();
      stack.addAll(Arrays.asList(children));
    } while (rule != ProofRule.DSL_REWRITE);
    Proof rewriteProof = curr;
    assertDoesNotThrow(() -> rewriteProof.getRewriteRule());
  }

  @Test
  void getResult() throws CVC5ApiException
  {
    Proof proof = createProof();
    assertDoesNotThrow(() -> proof.getResult());
  }

  @Test
  void getChildren() throws CVC5ApiException
  {
    Proof proof = createProof();
    Proof[] children = proof.getChildren();
    assertNotEquals(0, children.length);
  }

  @Test
  void getArguments() throws CVC5ApiException
  {
    Proof proof = createProof();
    assertDoesNotThrow(() -> proof.getArguments());
  }
}
