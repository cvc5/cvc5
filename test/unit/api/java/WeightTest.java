/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the SyGuS weight Java API.
 */

package tests;
import static io.github.cvc5.Kind.*;
import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import java.util.HashMap;
import java.util.Map;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class WeightTest
{
  private TermManager d_tm;
  private Solver d_solver;

  @BeforeEach
  void setUp()
  {
    d_tm = new TermManager();
    d_solver = new Solver(d_tm);
    d_solver.setOption("sygus", "true");
    d_solver.setLogic("NIA");
  }

  @AfterEach
  void tearDown()
  {
    Context.deletePointers();
  }

  @Test
  void declareWeight()
  {
    Weight w = d_solver.declareWeight("w");
    assertEquals("w", w.getName());
  }

  @Test
  void declareWeightWithDefault()
  {
    Weight w = d_solver.declareWeight("w", d_tm.mkInteger(5));
    assertEquals("w", w.getName());
    // Default weight must be an integer value.
    assertThrows(CVC5ApiException.class, () -> d_solver.declareWeight("bad", d_tm.mkBoolean(true)));
  }

  @Test
  void getDefaultValue()
  {
    Term five = d_tm.mkInteger(5);
    Weight wDefault = d_solver.declareWeight("a", five);
    assertEquals(five, wDefault.getDefaultValue());
    // Weights declared without :default get 0.
    Weight wZero = d_solver.declareWeight("b");
    assertEquals(d_tm.mkInteger(0), wZero.getDefaultValue());
  }

  @Test
  void declareWeightRequiresSygus()
  {
    TermManager tm = new TermManager();
    Solver s = new Solver(tm);
    assertThrows(CVC5ApiException.class, () -> s.declareWeight("w"));
  }

  @Test
  void weightEquality()
  {
    Weight w1 = d_solver.declareWeight("a");
    Weight w2 = d_solver.declareWeight("b");
    assertEquals(w1, w1);
    assertNotEquals(w1, w2);
    assertEquals(w1.hashCode(), w1.hashCode());
  }

  @Test
  void mkWeightSymbol()
  {
    Sort integer = d_tm.getIntegerSort();
    Term x = d_tm.mkVar(integer, "x");
    Term start = d_tm.mkVar(integer, "Start");
    Weight w = d_solver.declareWeight("w");
    Grammar g = d_solver.mkGrammar(new Term[] {x}, new Term[] {start});
    g.addRule(start, x);
    Term f = d_solver.synthFun("f", new Term[] {x}, integer, g);
    Term ws = d_solver.mkWeightSymbol(w, f);
    assertEquals(integer, ws.getSort());

    // mkWeightSymbol requires sygus mode.
    TermManager tm = new TermManager();
    Solver s = new Solver(tm);
    assertThrows(CVC5ApiException.class, () -> s.mkWeightSymbol(w, f));
  }

  @Test
  void grammarAddRuleWithWeights()
  {
    Sort integer = d_tm.getIntegerSort();
    Term x = d_tm.mkVar(integer, "x");
    Term start = d_tm.mkVar(integer, "Start");
    Weight w = d_solver.declareWeight("w");

    Grammar g = d_solver.mkGrammar(new Term[] {x}, new Term[] {start});
    Term add = d_tm.mkTerm(ADD, start, start);

    Map<Weight, Term> weights = new HashMap<>();
    weights.put(w, d_tm.mkInteger(1));
    g.addRule(start, add, weights);

    // Rule must have matching sort.
    assertThrows(CVC5ApiException.class, () -> g.addRule(start, d_tm.mkBoolean(true), weights));

    // After grammar is bound to synth-fun, addition is rejected.
    d_solver.synthFun("f", new Term[] {x}, integer, g);
    assertThrows(CVC5ApiException.class, () -> g.addRule(start, x, weights));
  }
}
