/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the guards of the Java API functions.
 */

package tests;
import static io.github.cvc5.Kind.*;
import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import java.util.Arrays;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class GrammarTest
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
  void testToString()
  {
    d_solver.setOption("sygus", "true");
    Sort bool = d_solver.getBooleanSort();
    Term start = d_solver.mkVar(bool);
    Grammar g = d_solver.mkGrammar(new Term[] {}, new Term[] {start});
    g.addRule(start, d_solver.mkBoolean(false));
    g.toString();
  }

  @Test
  void addRule()
  {
    d_solver.setOption("sygus", "true");
    Sort bool = d_solver.getBooleanSort();
    Sort integer = d_solver.getIntegerSort();

    Term nullTerm = new Term();
    Term start = d_solver.mkVar(bool);
    Term nts = d_solver.mkVar(bool);

    Grammar g = d_solver.mkGrammar(new Term[] {}, new Term[] {start});

    assertDoesNotThrow(() -> g.addRule(start, d_solver.mkBoolean(false)));

    assertThrows(CVC5ApiException.class, () -> g.addRule(nullTerm, d_solver.mkBoolean(false)));
    assertThrows(CVC5ApiException.class, () -> g.addRule(start, nullTerm));
    assertThrows(CVC5ApiException.class, () -> g.addRule(nts, d_solver.mkBoolean(false)));
    assertThrows(CVC5ApiException.class, () -> g.addRule(start, d_solver.mkInteger(0)));
    assertThrows(CVC5ApiException.class, () -> g.addRule(start, nts));

    d_solver.synthFun("f", new Term[] {}, bool, g);

    assertThrows(CVC5ApiException.class, () -> g.addRule(start, d_solver.mkBoolean(false)));
  }

  @Test
  void addRules()
  {
    d_solver.setOption("sygus", "true");
    Sort bool = d_solver.getBooleanSort();
    Sort integer = d_solver.getIntegerSort();

    Term nullTerm = new Term();
    Term start = d_solver.mkVar(bool);
    Term nts = d_solver.mkVar(bool);

    Grammar g = d_solver.mkGrammar(new Term[] {}, new Term[] {start});

    assertDoesNotThrow(() -> g.addRules(start, new Term[] {d_solver.mkBoolean(false)}));

    assertThrows(
        CVC5ApiException.class, () -> g.addRules(nullTerm, new Term[] {d_solver.mkBoolean(false)}));
    assertThrows(CVC5ApiException.class, () -> g.addRules(start, new Term[] {nullTerm}));
    assertThrows(
        CVC5ApiException.class, () -> g.addRules(nts, new Term[] {d_solver.mkBoolean(false)}));
    assertThrows(
        CVC5ApiException.class, () -> g.addRules(start, new Term[] {d_solver.mkInteger(0)}));
    assertThrows(CVC5ApiException.class, () -> g.addRules(start, new Term[] {nts}));

    d_solver.synthFun("f", new Term[] {}, bool, g);

    assertThrows(
        CVC5ApiException.class, () -> g.addRules(start, new Term[] {d_solver.mkBoolean(false)}));
  }

  @Test
  void addAnyConstant()
  {
    d_solver.setOption("sygus", "true");
    Sort bool = d_solver.getBooleanSort();

    Term nullTerm = new Term();
    Term start = d_solver.mkVar(bool);
    Term nts = d_solver.mkVar(bool);

    Grammar g = d_solver.mkGrammar(new Term[] {}, new Term[] {start});

    assertDoesNotThrow(() -> g.addAnyConstant(start));
    assertDoesNotThrow(() -> g.addAnyConstant(start));

    assertThrows(CVC5ApiException.class, () -> g.addAnyConstant(nullTerm));
    assertThrows(CVC5ApiException.class, () -> g.addAnyConstant(nts));

    d_solver.synthFun("f", new Term[] {}, bool, g);

    assertThrows(CVC5ApiException.class, () -> g.addAnyConstant(start));
  }

  @Test
  void addAnyVariable()
  {
    d_solver.setOption("sygus", "true");
    Sort bool = d_solver.getBooleanSort();

    Term nullTerm = new Term();
    Term x = d_solver.mkVar(bool);
    Term start = d_solver.mkVar(bool);
    Term nts = d_solver.mkVar(bool);

    Grammar g1 = d_solver.mkGrammar(new Term[] {x}, new Term[] {start});
    Grammar g2 = d_solver.mkGrammar(new Term[] {}, new Term[] {start});

    assertDoesNotThrow(() -> g1.addAnyVariable(start));
    assertDoesNotThrow(() -> g1.addAnyVariable(start));
    assertDoesNotThrow(() -> g2.addAnyVariable(start));

    assertThrows(CVC5ApiException.class, () -> g1.addAnyVariable(nullTerm));
    assertThrows(CVC5ApiException.class, () -> g1.addAnyVariable(nts));

    d_solver.synthFun("f", new Term[] {}, bool, g1);

    assertThrows(CVC5ApiException.class, () -> g1.addAnyVariable(start));
  }
}
