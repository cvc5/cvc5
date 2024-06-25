/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Gereon Kremer
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
import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import java.util.Arrays;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class GrammarTest
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

  @Test
  void testToString()
  {
    d_solver.setOption("sygus", "true");
    Sort bool = d_tm.getBooleanSort();
    Term start = d_tm.mkVar(bool);
    Grammar g = d_solver.mkGrammar(new Term[] {}, new Term[] {start});
    assertFalse(g.isNull());
    g.addRule(start, d_tm.mkBoolean(false));
    g.toString();
  }

  @Test
  void addRule()
  {
    d_solver.setOption("sygus", "true");
    Sort bool = d_tm.getBooleanSort();
    Sort integer = d_tm.getIntegerSort();

    Term nullTerm = new Term();
    Term start = d_tm.mkVar(bool);
    Term nts = d_tm.mkVar(bool);

    Grammar g = d_solver.mkGrammar(new Term[] {}, new Term[] {start});

    assertDoesNotThrow(() -> g.addRule(start, d_tm.mkBoolean(false)));

    assertThrows(CVC5ApiException.class, () -> g.addRule(nullTerm, d_tm.mkBoolean(false)));
    assertThrows(CVC5ApiException.class, () -> g.addRule(start, nullTerm));
    assertThrows(CVC5ApiException.class, () -> g.addRule(nts, d_tm.mkBoolean(false)));
    assertThrows(CVC5ApiException.class, () -> g.addRule(start, d_tm.mkInteger(0)));

    d_solver.synthFun("f", new Term[] {}, bool, g);

    assertThrows(CVC5ApiException.class, () -> g.addRule(start, d_tm.mkBoolean(false)));
  }

  @Test
  void addRules()
  {
    d_solver.setOption("sygus", "true");
    Sort bool = d_tm.getBooleanSort();
    Sort integer = d_tm.getIntegerSort();

    Term nullTerm = new Term();
    Term start = d_tm.mkVar(bool);
    Term nts = d_tm.mkVar(bool);

    Grammar g = d_solver.mkGrammar(new Term[] {}, new Term[] {start});

    assertDoesNotThrow(() -> g.addRules(start, new Term[] {d_tm.mkBoolean(false)}));

    assertThrows(
        CVC5ApiException.class, () -> g.addRules(nullTerm, new Term[] {d_tm.mkBoolean(false)}));
    assertThrows(CVC5ApiException.class, () -> g.addRules(start, new Term[] {nullTerm}));
    assertThrows(CVC5ApiException.class, () -> g.addRules(nts, new Term[] {d_tm.mkBoolean(false)}));
    assertThrows(CVC5ApiException.class, () -> g.addRules(start, new Term[] {d_tm.mkInteger(0)}));

    d_solver.synthFun("f", new Term[] {}, bool, g);

    assertThrows(
        CVC5ApiException.class, () -> g.addRules(start, new Term[] {d_tm.mkBoolean(false)}));
  }

  @Test
  void addAnyConstant()
  {
    d_solver.setOption("sygus", "true");
    Sort bool = d_tm.getBooleanSort();

    Term nullTerm = new Term();
    Term start = d_tm.mkVar(bool);
    Term nts = d_tm.mkVar(bool);

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
    Sort bool = d_tm.getBooleanSort();

    Term nullTerm = new Term();
    Term x = d_tm.mkVar(bool);
    Term start = d_tm.mkVar(bool);
    Term nts = d_tm.mkVar(bool);

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

  @Test
  void hash()
  {
    d_solver.setOption("sygus", "true");

    Sort bool = d_tm.getBooleanSort();
    Term x = d_tm.mkVar(bool, "x");
    Term start1 = d_tm.mkVar(bool, "start");
    Term start2 = d_tm.mkVar(bool, "start");

    Grammar g1, g2;

    {
      g1 = d_solver.mkGrammar(new Term[] {}, new Term[] {start1});
      g2 = d_solver.mkGrammar(new Term[] {}, new Term[] {start1});
      assertTrue(g1.hashCode() == g1.hashCode());
      assertTrue(g1.hashCode() == g2.hashCode());
    }

    {
      g1 = d_solver.mkGrammar(new Term[] {}, new Term[] {start1});
      g2 = d_solver.mkGrammar(new Term[] {x}, new Term[] {start1});
      assertFalse(g1.hashCode() == g2.hashCode());
    }

    {
      g1 = d_solver.mkGrammar(new Term[] {x}, new Term[] {start1});
      g2 = d_solver.mkGrammar(new Term[] {x}, new Term[] {start2});
      assertFalse(g1.hashCode() == g2.hashCode());
    }

    {
      g1 = d_solver.mkGrammar(new Term[] {x}, new Term[] {start1});
      g2 = d_solver.mkGrammar(new Term[] {x}, new Term[] {start1});
      g2.addAnyVariable(start1);
      assertFalse(g1.hashCode() == g2.hashCode());
    }

    {
      g1 = d_solver.mkGrammar(new Term[] {x}, new Term[] {start1});
      g2 = d_solver.mkGrammar(new Term[] {x}, new Term[] {start1});
      g1.addRules(start1, new Term[] {d_tm.mkFalse()});
      g2.addRules(start1, new Term[] {d_tm.mkFalse()});
      assertTrue(g1.hashCode() == g2.hashCode());
    }

    {
      g1 = d_solver.mkGrammar(new Term[] {x}, new Term[] {start1});
      g2 = d_solver.mkGrammar(new Term[] {x}, new Term[] {start1});
      g2.addRules(start1, new Term[] {d_tm.mkFalse()});
      assertFalse(g1.hashCode() == g2.hashCode());
    }

    {
      g1 = d_solver.mkGrammar(new Term[] {x}, new Term[] {start1});
      g2 = d_solver.mkGrammar(new Term[] {x}, new Term[] {start1});
      g1.addRules(start1, new Term[] {d_tm.mkTrue()});
      g2.addRules(start1, new Term[] {d_tm.mkFalse()});
      assertFalse(g1.hashCode() == g2.hashCode());
    }
  }
}
