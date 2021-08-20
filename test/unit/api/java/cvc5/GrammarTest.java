/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Abdalrhman Mohamed, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the guards of the Java API functions.
 */

package cvc5;

import static cvc5.Kind.*;
import static org.junit.jupiter.api.Assertions.*;

import java.util.Arrays;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class GrammarTest {
  private Solver d_solver;

  @BeforeEach
  void setUp() {
    d_solver = new Solver();
  }

  @Test
  void addRule() {
    Sort bool = d_solver.getBooleanSort();
    Sort integer = d_solver.getIntegerSort();

    Term nullTerm = d_solver.getNullTerm();
    Term start = d_solver.mkVar(bool);
    Term nts = d_solver.mkVar(bool);

    Grammar g = d_solver.mkSygusGrammar(new Term[] {}, new Term[] {start});

    assertDoesNotThrow(() -> g.addRule(start, d_solver.mkBoolean(false)));

    assertThrows(CVC5ApiException.class,
        () -> g.addRule(nullTerm, d_solver.mkBoolean(false)));
    assertThrows(CVC5ApiException.class, () -> g.addRule(start, nullTerm));
    assertThrows(CVC5ApiException.class,
        () -> g.addRule(nts, d_solver.mkBoolean(false)));
    assertThrows(
        CVC5ApiException.class, () -> g.addRule(start, d_solver.mkInteger(0)));
    assertThrows(CVC5ApiException.class, () -> g.addRule(start, nts));

    d_solver.synthFun("f", new Term[] {}, bool, g);

    assertThrows(CVC5ApiException.class,
        () -> g.addRule(start, d_solver.mkBoolean(false)));
  }

  @Test
  void addRules() {
    Sort bool = d_solver.getBooleanSort();
    Sort integer = d_solver.getIntegerSort();

    Term nullTerm = d_solver.getNullTerm();
    Term start = d_solver.mkVar(bool);
    Term nts = d_solver.mkVar(bool);

    Grammar g = d_solver.mkSygusGrammar(new Term[] {}, new Term[] {start});

    assertDoesNotThrow(
        () -> g.addRules(start, new Term[] {d_solver.mkBoolean(false)}));

    assertThrows(CVC5ApiException.class,
        () -> g.addRules(nullTerm, new Term[] {d_solver.mkBoolean(false)}));
    assertThrows(
        CVC5ApiException.class, () -> g.addRules(start, new Term[] {nullTerm}));
    assertThrows(CVC5ApiException.class,
        () -> g.addRules(nts, new Term[] {d_solver.mkBoolean(false)}));
    assertThrows(CVC5ApiException.class,
        () -> g.addRules(start, new Term[] {d_solver.mkInteger(0)}));
    assertThrows(
        CVC5ApiException.class, () -> g.addRules(start, new Term[] {nts}));

    d_solver.synthFun("f", new Term[] {}, bool, g);

    assertThrows(CVC5ApiException.class,
        () -> g.addRules(start, new Term[] {d_solver.mkBoolean(false)}));
  }

  @Test
  void addAnyConstant() {
    Sort bool = d_solver.getBooleanSort();

    Term nullTerm = d_solver.getNullTerm();
    Term start = d_solver.mkVar(bool);
    Term nts = d_solver.mkVar(bool);

    Grammar g = d_solver.mkSygusGrammar(new Term[] {}, new Term[] {start});

    assertDoesNotThrow(() -> g.addAnyConstant(start));
    assertDoesNotThrow(() -> g.addAnyConstant(start));

    assertThrows(CVC5ApiException.class, () -> g.addAnyConstant(nullTerm));
    assertThrows(CVC5ApiException.class, () -> g.addAnyConstant(nts));

    d_solver.synthFun("f", new Term[] {}, bool, g);

    assertThrows(CVC5ApiException.class, () -> g.addAnyConstant(start));
  }

  @Test
  void addAnyVariable() {
    Sort bool = d_solver.getBooleanSort();

    Term nullTerm = d_solver.getNullTerm();
    Term x = d_solver.mkVar(bool);
    Term start = d_solver.mkVar(bool);
    Term nts = d_solver.mkVar(bool);

    Grammar g1 = d_solver.mkSygusGrammar(new Term[] {x}, new Term[] {start});
    Grammar g2 = d_solver.mkSygusGrammar(new Term[] {}, new Term[] {start});

    assertDoesNotThrow(() -> g1.addAnyVariable(start));
    assertDoesNotThrow(() -> g1.addAnyVariable(start));
    assertDoesNotThrow(() -> g2.addAnyVariable(start));

    assertThrows(CVC5ApiException.class, () -> g1.addAnyVariable(nullTerm));
    assertThrows(CVC5ApiException.class, () -> g1.addAnyVariable(nts));

    d_solver.synthFun("f", new Term[] {}, bool, g1);

    assertThrows(CVC5ApiException.class, () -> g1.addAnyVariable(start));
  }
}
