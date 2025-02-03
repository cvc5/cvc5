/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Solver class of the Java API.
 */

package tests;

import static io.github.cvc5.Kind.*;
import static io.github.cvc5.RoundingMode.*;
import static io.github.cvc5.SortKind.*;
import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import io.github.cvc5.modes.BlockModelsMode;
import io.github.cvc5.modes.FindSynthTarget;
import io.github.cvc5.modes.LearnedLitType;
import io.github.cvc5.modes.ProofComponent;
import io.github.cvc5.modes.ProofFormat;
import java.math.BigInteger;
import java.util.*;
import java.util.concurrent.atomic.AtomicReference;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.function.Executable;

class SolverTest
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
  void recoverableException() throws CVC5ApiException
  {
    d_solver.setOption("produce-models", "true");
    Term x = d_tm.mkConst(d_tm.getBooleanSort(), "x");
    d_solver.assertFormula(x.eqTerm(x).notTerm());
    assertThrows(CVC5ApiRecoverableException.class, () -> d_solver.getValue(x));
  }

  @Test
  void declareFunFresh()
  {
    Sort boolSort = d_solver.getBooleanSort();
    Sort intSort = d_solver.getIntegerSort();
    Term t1 = d_solver.declareFun("b", new Sort[] {}, boolSort, true);
    Term t2 = d_solver.declareFun("b", new Sort[] {}, boolSort, false);
    Term t3 = d_solver.declareFun("b", new Sort[] {}, boolSort, false);
    assertNotEquals(t1, t2);
    assertNotEquals(t1, t3);
    assertEquals(t2, t3);
    Term t4 = d_solver.declareFun("c", new Sort[] {}, boolSort, false);
    assertNotEquals(t2, t4);
    Term t5 = d_solver.declareFun("b", new Sort[] {}, intSort, false);
    assertNotEquals(t2, t5);
  }

  @Test
  void declareDatatype()
  {
    DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
    DatatypeConstructorDecl[] ctors1 = new DatatypeConstructorDecl[] {nil};
    assertDoesNotThrow(() -> d_solver.declareDatatype(("a"), ctors1));
    DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
    DatatypeConstructorDecl nil2 = d_solver.mkDatatypeConstructorDecl("nil");
    DatatypeConstructorDecl[] ctors2 = new DatatypeConstructorDecl[] {cons, nil2};
    assertDoesNotThrow(() -> d_solver.declareDatatype(("b"), ctors2));
    DatatypeConstructorDecl cons2 = d_solver.mkDatatypeConstructorDecl("cons");
    DatatypeConstructorDecl nil3 = d_solver.mkDatatypeConstructorDecl("nil");
    DatatypeConstructorDecl[] ctors3 = new DatatypeConstructorDecl[] {cons2, nil3};
    assertDoesNotThrow(() -> d_solver.declareDatatype((""), ctors3));
    DatatypeConstructorDecl[] ctors4 = new DatatypeConstructorDecl[0];
    assertThrows(CVC5ApiException.class, () -> d_solver.declareDatatype(("c"), ctors4));

    assertThrows(CVC5ApiException.class, () -> d_solver.declareDatatype((""), ctors4));

    Solver slv = new Solver();
    assertThrows(CVC5ApiException.class, () -> slv.declareDatatype(("a"), ctors1));
  }

  @Test
  void declareFun() throws CVC5ApiException
  {
    Sort bvSort = d_solver.mkBitVectorSort(32);
    Sort funSort =
        d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort());
    assertDoesNotThrow(() -> d_solver.declareFun("f1", new Sort[] {}, bvSort));
    assertDoesNotThrow(
        () -> d_solver.declareFun("f3", new Sort[] {bvSort, d_solver.getIntegerSort()}, bvSort));
    assertThrows(CVC5ApiException.class, () -> d_solver.declareFun("f2", new Sort[] {}, funSort));
    // functions as arguments is allowed
    assertDoesNotThrow(() -> d_solver.declareFun("f4", new Sort[] {bvSort, funSort}, bvSort));
    assertThrows(CVC5ApiException.class,
        () -> d_solver.declareFun("f5", new Sort[] {bvSort, bvSort}, funSort));

    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.declareFun("f1", new Sort[] {}, bvSort));
  }

  @Test
  void declareSort()
  {
    assertDoesNotThrow(() -> d_solver.declareSort("s", 0));
    assertDoesNotThrow(() -> d_solver.declareSort("s", 2));
    assertDoesNotThrow(() -> d_solver.declareSort("", 2));
  }

  @Test
  void declareSortFresh() throws CVC5ApiException
  {
    Sort t1 = d_solver.declareSort("b", 0, true);
    Sort t2 = d_solver.declareSort("b", 0, false);
    Sort t3 = d_solver.declareSort("b", 0, false);
    assertNotEquals(t1, t2);
    assertNotEquals(t1, t3);
    assertEquals(t2, t3);
    Sort t4 = d_solver.declareSort("c", 0, false);
    assertNotEquals(t2, t4);
    Sort t5 = d_solver.declareSort("b", 1, false);
    assertNotEquals(t2, t5);
  }

  @Test
  void defineFun() throws CVC5ApiException
  {
    Sort bvSort = d_solver.mkBitVectorSort(32);
    Sort funSort =
        d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort());
    Term b1 = d_solver.mkVar(bvSort, "b1");
    Term b2 = d_solver.mkVar(d_solver.getIntegerSort(), "b2");
    Term b3 = d_solver.mkVar(funSort, "b3");
    Term v1 = d_solver.mkConst(bvSort, "v1");
    Term v2 = d_solver.mkConst(funSort, "v2");
    assertDoesNotThrow(() -> d_solver.defineFun("f", new Term[] {}, bvSort, v1));
    assertDoesNotThrow(() -> d_solver.defineFun("ff", new Term[] {b1, b2}, bvSort, v1));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.defineFun("ff", new Term[] {v1, b2}, bvSort, v1));

    assertThrows(
        CVC5ApiException.class, () -> d_solver.defineFun("fff", new Term[] {b1}, bvSort, v2));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.defineFun("ffff", new Term[] {b1}, funSort, v2));

    // b3 has function sort, which is allowed as an argument
    assertDoesNotThrow(() -> d_solver.defineFun("fffff", new Term[] {b1, b3}, bvSort, v1));

    Solver slv = new Solver();
    Sort bvSort2 = slv.mkBitVectorSort(32);
    Term v12 = slv.mkConst(bvSort2, "v1");
    Term b12 = slv.mkVar(bvSort2, "b1");
    Term b22 = slv.mkVar(slv.getIntegerSort(), "b2");
    assertDoesNotThrow(() -> slv.defineFun("f", new Term[] {}, bvSort, v12));
    assertDoesNotThrow(() -> slv.defineFun("f", new Term[] {}, bvSort2, v1));
    assertDoesNotThrow(() -> slv.defineFun("ff", new Term[] {b1, b22}, bvSort2, v12));
    assertDoesNotThrow(() -> slv.defineFun("ff", new Term[] {b12, b2}, bvSort2, v12));
    assertDoesNotThrow(() -> slv.defineFun("ff", new Term[] {b12, b22}, bvSort, v12));
    assertDoesNotThrow(() -> slv.defineFun("ff", new Term[] {b12, b22}, bvSort2, v1));
  }

  @Test
  void defineFunGlobal()
  {
    Sort bSort = d_solver.getBooleanSort();

    Term bTrue = d_solver.mkBoolean(true);
    // (define-fun f () Bool true)
    Term f = d_solver.defineFun("f", new Term[] {}, bSort, bTrue, true);
    Term b = d_solver.mkVar(bSort, "b");
    // (define-fun g (b Bool) Bool b)
    Term g = d_solver.defineFun("g", new Term[] {b}, bSort, b, true);

    // (assert (or (not f) (not (g true))))
    d_solver.assertFormula(
        d_solver.mkTerm(OR, f.notTerm(), d_solver.mkTerm(APPLY_UF, g, bTrue).notTerm()));
    assertTrue(d_solver.checkSat().isUnsat());
    d_solver.resetAssertions();
    // (assert (or (not f) (not (g true))))
    d_solver.assertFormula(
        d_solver.mkTerm(OR, f.notTerm(), d_solver.mkTerm(APPLY_UF, g, bTrue).notTerm()));
    assertTrue(d_solver.checkSat().isUnsat());
  }

  @Test
  void defineFunRec() throws CVC5ApiException
  {
    Sort bvSort = d_solver.mkBitVectorSort(32);
    Sort funSort1 = d_solver.mkFunctionSort(new Sort[] {bvSort, bvSort}, bvSort);
    Sort funSort2 =
        d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort());
    Term b1 = d_solver.mkVar(bvSort, "b1");
    Term b11 = d_solver.mkVar(bvSort, "b1");
    Term b2 = d_solver.mkVar(d_solver.getIntegerSort(), "b2");
    Term b3 = d_solver.mkVar(funSort2, "b3");
    Term v1 = d_solver.mkConst(bvSort, "v1");
    Term v2 = d_solver.mkConst(d_solver.getIntegerSort(), "v2");
    Term v3 = d_solver.mkConst(funSort2, "v3");
    Term f1 = d_solver.mkConst(funSort1, "f1");
    Term f2 = d_solver.mkConst(funSort2, "f2");
    Term f3 = d_solver.mkConst(bvSort, "f3");
    assertDoesNotThrow(() -> d_solver.defineFunRec("f", new Term[] {}, bvSort, v1));
    assertDoesNotThrow(() -> d_solver.defineFunRec("ff", new Term[] {b1, b2}, bvSort, v1));
    assertDoesNotThrow(() -> d_solver.defineFunRec(f1, new Term[] {b1, b11}, v1));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.defineFunRec("fff", new Term[] {b1}, bvSort, v3));

    assertThrows(
        CVC5ApiException.class, () -> d_solver.defineFunRec("ff", new Term[] {b1, v2}, bvSort, v1));

    assertThrows(
        CVC5ApiException.class, () -> d_solver.defineFunRec("ffff", new Term[] {b1}, funSort2, v3));

    // b3 has function sort, which is allowed as an argument
    assertDoesNotThrow(() -> d_solver.defineFunRec("fffff", new Term[] {b1, b3}, bvSort, v1));
    assertThrows(CVC5ApiException.class, () -> d_solver.defineFunRec(f1, new Term[] {b1}, v1));
    assertThrows(CVC5ApiException.class, () -> d_solver.defineFunRec(f1, new Term[] {b1, b11}, v2));
    assertThrows(CVC5ApiException.class, () -> d_solver.defineFunRec(f1, new Term[] {b1, b11}, v3));
    assertThrows(CVC5ApiException.class, () -> d_solver.defineFunRec(f2, new Term[] {b1}, v2));
    assertThrows(CVC5ApiException.class, () -> d_solver.defineFunRec(f3, new Term[] {b1}, v1));

    Solver slv = new Solver();
    Sort bvSort2 = slv.mkBitVectorSort(32);
    Term v12 = slv.mkConst(bvSort2, "v1");
    Term b12 = slv.mkVar(bvSort2, "b1");
    Term b22 = slv.mkVar(slv.getIntegerSort(), "b2");
    assertDoesNotThrow(() -> slv.defineFunRec("f", new Term[] {}, bvSort2, v12));
    assertDoesNotThrow(() -> slv.defineFunRec("ff", new Term[] {b12, b22}, bvSort2, v12));
    assertDoesNotThrow(() -> slv.defineFunRec("f", new Term[] {}, bvSort, v12));
    assertDoesNotThrow(() -> slv.defineFunRec("f", new Term[] {}, bvSort2, v1));
    assertDoesNotThrow(() -> slv.defineFunRec("ff", new Term[] {b1, b22}, bvSort2, v12));

    assertDoesNotThrow(() -> slv.defineFunRec("ff", new Term[] {b12, b2}, bvSort2, v12));

    assertDoesNotThrow(() -> slv.defineFunRec("ff", new Term[] {b12, b22}, bvSort, v12));

    assertDoesNotThrow(() -> slv.defineFunRec("ff", new Term[] {b12, b22}, bvSort2, v1));
  }

  @Test
  void defineFunRecWrongLogic() throws CVC5ApiException
  {
    d_solver.setLogic("QF_BV");
    Sort bvSort = d_solver.mkBitVectorSort(32);
    Sort funSort = d_solver.mkFunctionSort(new Sort[] {bvSort, bvSort}, bvSort);
    Term b = d_solver.mkVar(bvSort, "b");
    Term v = d_solver.mkConst(bvSort, "v");
    Term f = d_solver.mkConst(funSort, "f");
    assertThrows(
        CVC5ApiException.class, () -> d_solver.defineFunRec("f", new Term[] {}, bvSort, v));
    assertThrows(CVC5ApiException.class, () -> d_solver.defineFunRec(f, new Term[] {b, b}, v));
  }

  @Test
  void defineFunRecGlobal() throws CVC5ApiException
  {
    Sort bSort = d_solver.getBooleanSort();
    Sort fSort = d_solver.mkFunctionSort(bSort, bSort);

    d_solver.push();
    Term bTrue = d_solver.mkBoolean(true);
    // (define-fun f () Bool true)
    Term f = d_solver.defineFunRec("f", new Term[] {}, bSort, bTrue, true);
    Term b = d_solver.mkVar(bSort, "b");
    Term gSym = d_solver.mkConst(fSort, "g");
    // (define-fun g (b Bool) Bool b)
    Term g = d_solver.defineFunRec(gSym, new Term[] {b}, b, true);

    // (assert (or (not f) (not (g true))))
    d_solver.assertFormula(
        d_solver.mkTerm(OR, f.notTerm(), d_solver.mkTerm(APPLY_UF, g, bTrue).notTerm()));
    assertTrue(d_solver.checkSat().isUnsat());
    d_solver.pop();
    // (assert (or (not f) (not (g true))))
    d_solver.assertFormula(
        d_solver.mkTerm(OR, f.notTerm(), d_solver.mkTerm(APPLY_UF, g, bTrue).notTerm()));
    assertTrue(d_solver.checkSat().isUnsat());
  }

  @Test
  void defineFunsRec() throws CVC5ApiException
  {
    Sort uSort = d_solver.mkUninterpretedSort("u");
    Sort bvSort = d_solver.mkBitVectorSort(32);
    Sort funSort1 = d_solver.mkFunctionSort(new Sort[] {bvSort, bvSort}, bvSort);
    Sort funSort2 = d_solver.mkFunctionSort(uSort, d_solver.getIntegerSort());
    Term b1 = d_solver.mkVar(bvSort, "b1");
    Term b11 = d_solver.mkVar(bvSort, "b1");
    Term b2 = d_solver.mkVar(d_solver.getIntegerSort(), "b2");
    Term b3 = d_solver.mkVar(funSort2, "b3");
    Term b4 = d_solver.mkVar(uSort, "b4");
    Term v1 = d_solver.mkConst(bvSort, "v1");
    Term v2 = d_solver.mkConst(d_solver.getIntegerSort(), "v2");
    Term v3 = d_solver.mkConst(funSort2, "v3");
    Term v4 = d_solver.mkConst(uSort, "v4");
    Term f1 = d_solver.mkConst(funSort1, "f1");
    Term f2 = d_solver.mkConst(funSort2, "f2");
    Term f3 = d_solver.mkConst(bvSort, "f3");
    assertDoesNotThrow(
        ()
            -> d_solver.defineFunsRec(
                new Term[] {f1, f2}, new Term[][] {{b1, b11}, {b4}}, new Term[] {v1, v2}));
    assertThrows(CVC5ApiException.class,
        ()
            -> d_solver.defineFunsRec(
                new Term[] {f1, f2}, new Term[][] {{v1, b11}, {b4}}, new Term[] {v1, v2}));
    assertThrows(CVC5ApiException.class,
        ()
            -> d_solver.defineFunsRec(
                new Term[] {f1, f3}, new Term[][] {{b1, b11}, {b4}}, new Term[] {v1, v2}));
    assertThrows(CVC5ApiException.class,
        ()
            -> d_solver.defineFunsRec(
                new Term[] {f1, f2}, new Term[][] {{b1}, {b4}}, new Term[] {v1, v2}));
    assertThrows(CVC5ApiException.class,
        ()
            -> d_solver.defineFunsRec(
                new Term[] {f1, f2}, new Term[][] {{b1, b2}, {b4}}, new Term[] {v1, v2}));
    assertThrows(CVC5ApiException.class,
        ()
            -> d_solver.defineFunsRec(
                new Term[] {f1, f2}, new Term[][] {{b1, b11}, {b4}}, new Term[] {v1, v4}));

    Solver slv = new Solver();
    Sort uSort2 = slv.mkUninterpretedSort("u");
    Sort bvSort2 = slv.mkBitVectorSort(32);
    Sort funSort12 = slv.mkFunctionSort(new Sort[] {bvSort2, bvSort2}, bvSort2);
    Sort funSort22 = slv.mkFunctionSort(uSort2, slv.getIntegerSort());
    Term b12 = slv.mkVar(bvSort2, "b1");
    Term b112 = slv.mkVar(bvSort2, "b1");
    Term b42 = slv.mkVar(uSort2, "b4");
    Term v12 = slv.mkConst(bvSort2, "v1");
    Term v22 = slv.mkConst(slv.getIntegerSort(), "v2");
    Term f12 = slv.mkConst(funSort12, "f1");
    Term f22 = slv.mkConst(funSort22, "f2");
    assertDoesNotThrow(
        ()
            -> slv.defineFunsRec(
                new Term[] {f12, f22}, new Term[][] {{b12, b112}, {b42}}, new Term[] {v12, v22}));
    assertDoesNotThrow(
        ()
            -> slv.defineFunsRec(
                new Term[] {f1, f22}, new Term[][] {{b12, b112}, {b42}}, new Term[] {v12, v22}));
    assertThrows(CVC5ApiException.class,
        ()
            -> slv.defineFunsRec(
                new Term[] {f12, f2}, new Term[][] {{b12, b112}, {b42}}, new Term[] {v12, v22}));
    assertDoesNotThrow(
        ()
            -> slv.defineFunsRec(
                new Term[] {f12, f22}, new Term[][] {{b1, b112}, {b42}}, new Term[] {v12, v22}));
    assertDoesNotThrow(
        ()
            -> slv.defineFunsRec(
                new Term[] {f12, f22}, new Term[][] {{b12, b11}, {b42}}, new Term[] {v12, v22}));
    assertThrows(CVC5ApiException.class,
        ()
            -> slv.defineFunsRec(
                new Term[] {f12, f22}, new Term[][] {{b12, b112}, {b4}}, new Term[] {v12, v22}));
    assertDoesNotThrow(
        ()
            -> slv.defineFunsRec(
                new Term[] {f12, f22}, new Term[][] {{b12, b112}, {b42}}, new Term[] {v1, v22}));
    assertDoesNotThrow(
        ()
            -> slv.defineFunsRec(
                new Term[] {f12, f22}, new Term[][] {{b12, b112}, {b42}}, new Term[] {v12, v2}));
  }

  @Test
  void defineFunsRecWrongLogic() throws CVC5ApiException
  {
    d_solver.setLogic("QF_BV");
    Sort uSort = d_solver.mkUninterpretedSort("u");
    Sort bvSort = d_solver.mkBitVectorSort(32);
    Sort funSort1 = d_solver.mkFunctionSort(new Sort[] {bvSort, bvSort}, bvSort);
    Sort funSort2 = d_solver.mkFunctionSort(uSort, d_solver.getIntegerSort());
    Term b = d_solver.mkVar(bvSort, "b");
    Term u = d_solver.mkVar(uSort, "u");
    Term v1 = d_solver.mkConst(bvSort, "v1");
    Term v2 = d_solver.mkConst(d_solver.getIntegerSort(), "v2");
    Term f1 = d_solver.mkConst(funSort1, "f1");
    Term f2 = d_solver.mkConst(funSort2, "f2");
    assertThrows(CVC5ApiException.class,
        ()
            -> d_solver.defineFunsRec(
                new Term[] {f1, f2}, new Term[][] {{b, b}, {u}}, new Term[] {v1, v2}));
  }

  @Test
  void defineFunsRecGlobal() throws CVC5ApiException
  {
    Sort bSort = d_solver.getBooleanSort();
    Sort fSort = d_solver.mkFunctionSort(bSort, bSort);

    d_solver.push();
    Term bTrue = d_solver.mkBoolean(true);
    Term b = d_solver.mkVar(bSort, "b");
    Term gSym = d_solver.mkConst(fSort, "g");
    // (define-funs-rec ((g ((b Bool)) Bool)) (b))
    d_solver.defineFunsRec(new Term[] {gSym}, new Term[][] {{b}}, new Term[] {b}, true);

    // (assert (not (g true)))
    d_solver.assertFormula(d_solver.mkTerm(APPLY_UF, gSym, bTrue).notTerm());
    assertTrue(d_solver.checkSat().isUnsat());
    d_solver.pop();
    // (assert (not (g true)))
    d_solver.assertFormula(d_solver.mkTerm(APPLY_UF, gSym, bTrue).notTerm());
    assertTrue(d_solver.checkSat().isUnsat());
  }

  @Test
  void getAssertions()
  {
    Term a = d_solver.mkConst(d_solver.getBooleanSort(), "a");
    Term b = d_solver.mkConst(d_solver.getBooleanSort(), "b");
    d_solver.assertFormula(a);
    d_solver.assertFormula(b);
    Term[] asserts = d_solver.getAssertions();
    assertEquals(asserts[0], a);
    assertEquals(asserts[1], b);
  }

  @Test
  void getInfo()
  {
    assertDoesNotThrow(() -> d_solver.getInfo("name"));
    assertThrows(CVC5ApiException.class, () -> d_solver.getInfo("asdf"));
  }

  @Test
  void getAbduct() throws CVC5ApiException
  {
    d_solver.setLogic("QF_LIA");
    d_solver.setOption("produce-abducts", "true");
    d_solver.setOption("incremental", "false");

    Sort intSort = d_solver.getIntegerSort();
    Term zero = d_solver.mkInteger(0);
    Term x = d_solver.mkConst(intSort, "x");
    Term y = d_solver.mkConst(intSort, "y");

    // Assumptions for abduction: x > 0
    d_solver.assertFormula(d_solver.mkTerm(GT, x, zero));
    // Conjecture for abduction: y > 0
    Term conj = d_solver.mkTerm(GT, y, zero);
    Term output = new Term();
    // Call the abduction api, while the resulting abduct is the output
    output = d_solver.getAbduct(conj);
    // We expect the resulting output to be a boolean formula
    assertTrue(!output.isNull() && output.getSort().isBoolean());

    // try with a grammar, a simple grammar admitting true
    Sort bsort = d_solver.getBooleanSort();
    Term truen = d_solver.mkBoolean(true);
    Term start = d_solver.mkVar(bsort);
    Term output2 = new Term();
    Grammar g = d_solver.mkGrammar(new Term[] {}, new Term[] {start});
    Term conj2 = d_solver.mkTerm(GT, x, zero);
    assertDoesNotThrow(() -> g.addRule(start, truen));
    // Call the abduction api, while the resulting abduct is the output
    output2 = d_solver.getAbduct(conj2, g);
    // abduct must be true
    assertEquals(output2, truen);
  }

  @Test
  void getAbduct2() throws CVC5ApiException
  {
    d_solver.setLogic("QF_LIA");
    d_solver.setOption("incremental", "false");
    Sort intSort = d_solver.getIntegerSort();
    Term zero = d_solver.mkInteger(0);
    Term x = d_solver.mkConst(intSort, "x");
    Term y = d_solver.mkConst(intSort, "y");
    // Assumptions for abduction: x > 0
    d_solver.assertFormula(d_solver.mkTerm(GT, x, zero));
    // Conjecture for abduction: y > 0
    Term conj = d_solver.mkTerm(GT, y, zero);
    Term output = new Term();
    // Fails due to option not set
    assertThrows(CVC5ApiException.class, () -> d_solver.getAbduct(conj));
  }

  @Test
  void getAbductNext() throws CVC5ApiException
  {
    d_solver.setLogic("QF_LIA");
    d_solver.setOption("produce-abducts", "true");
    d_solver.setOption("incremental", "true");

    Sort intSort = d_solver.getIntegerSort();
    Term zero = d_solver.mkInteger(0);
    Term x = d_solver.mkConst(intSort, "x");
    Term y = d_solver.mkConst(intSort, "y");

    // Assumptions for abduction: x > 0
    d_solver.assertFormula(d_solver.mkTerm(GT, x, zero));
    // Conjecture for abduction: y > 0
    Term conj = d_solver.mkTerm(GT, y, zero);
    // Call the abduction api, while the resulting abduct is the output
    Term output = d_solver.getAbduct(conj);
    Term output2 = d_solver.getAbductNext();
    // should produce a different output
    assertNotEquals(output, output2);
  }

  @Test
  void getInterpolant() throws CVC5ApiException
  {
    d_solver.setLogic("QF_LIA");
    d_solver.setOption("produce-interpolants", "true");
    d_solver.setOption("incremental", "false");

    Sort intSort = d_solver.getIntegerSort();
    Term zero = d_solver.mkInteger(0);
    Term x = d_solver.mkConst(intSort, "x");
    Term y = d_solver.mkConst(intSort, "y");
    Term z = d_solver.mkConst(intSort, "z");

    // Assumptions for interpolation: x + y > 0 /\ x < 0
    d_solver.assertFormula(d_solver.mkTerm(GT, d_solver.mkTerm(ADD, x, y), zero));
    d_solver.assertFormula(d_solver.mkTerm(LT, x, zero));
    // Conjecture for interpolation: y + z > 0 \/ z < 0
    Term conj = d_solver.mkTerm(
        OR, d_solver.mkTerm(GT, d_solver.mkTerm(ADD, y, z), zero), d_solver.mkTerm(LT, z, zero));
    // Call the interpolation api, while the resulting interpolant is the output
    Term output = d_solver.getInterpolant(conj);

    // We expect the resulting output to be a boolean formula
    assertTrue(output.getSort().isBoolean());

    // try with a grammar, a simple grammar admitting true
    Sort bsort = d_solver.getBooleanSort();
    Term truen = d_solver.mkBoolean(true);
    Term start = d_solver.mkVar(bsort);
    Grammar g = d_solver.mkGrammar(new Term[] {}, new Term[] {start});
    Term conj2 = d_solver.mkTerm(EQUAL, zero, zero);
    assertDoesNotThrow(() -> g.addRule(start, truen));
    // Call the interpolation api, while the resulting interpolant is the output
    Term output2 = d_solver.getInterpolant(conj2, g);
    // interpolant must be true
    assertEquals(output2, truen);
  }

  @Test
  void getInterpolantNext() throws CVC5ApiException
  {
    d_solver.setLogic("QF_LIA");
    d_solver.setOption("produce-interpolants", "true");
    d_solver.setOption("incremental", "true");

    Sort intSort = d_solver.getIntegerSort();
    Term zero = d_solver.mkInteger(0);
    Term x = d_solver.mkConst(intSort, "x");
    Term y = d_solver.mkConst(intSort, "y");
    Term z = d_solver.mkConst(intSort, "z");

    d_solver.assertFormula(d_solver.mkTerm(GT, d_solver.mkTerm(ADD, x, y), zero));
    d_solver.assertFormula(d_solver.mkTerm(LT, x, zero));
    Term conj = d_solver.mkTerm(
        OR, d_solver.mkTerm(GT, d_solver.mkTerm(ADD, y, z), zero), d_solver.mkTerm(LT, z, zero));
    Term output = d_solver.getInterpolant(conj);
    Term output2 = d_solver.getInterpolantNext();

    // We expect the next output to be distinct
    assertNotEquals(output, output2);
  }

  @Test
  void declarePool() throws CVC5ApiException
  {
    Sort intSort = d_solver.getIntegerSort();
    Sort setSort = d_solver.mkSetSort(intSort);
    Term zero = d_solver.mkInteger(0);
    Term x = d_solver.mkConst(intSort, "x");
    Term y = d_solver.mkConst(intSort, "y");
    // declare a pool with initial value { 0, x, y }
    Term p = d_solver.declarePool("p", intSort, new Term[] {zero, x, y});
    // pool should have the same sort
    assertEquals(p.getSort(), setSort);
  }

  @Test
  void getOp() throws CVC5ApiException
  {
    Sort bv32 = d_solver.mkBitVectorSort(32);
    Term a = d_solver.mkConst(bv32, "a");
    Op ext = d_solver.mkOp(BITVECTOR_EXTRACT, 2, 1);
    Term exta = d_solver.mkTerm(ext, a);

    assertFalse(a.hasOp());
    assertThrows(CVC5ApiException.class, () -> a.getOp());
    assertTrue(exta.hasOp());
    assertEquals(exta.getOp(), ext);

    // Test Datatypes -- more complicated
    DatatypeDecl consListSpec = d_solver.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", d_solver.getIntegerSort());
    cons.addSelectorSelf("tail");
    consListSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
    consListSpec.addConstructor(nil);
    Sort consListSort = d_solver.mkDatatypeSort(consListSpec);
    Datatype consList = consListSort.getDatatype();

    Term consTerm = consList.getConstructor("cons").getTerm();
    Term nilTerm = consList.getConstructor("nil").getTerm();
    Term headTerm = consList.getConstructor("cons").getSelector("head").getTerm();

    Term listnil = d_solver.mkTerm(APPLY_CONSTRUCTOR, nilTerm);
    Term listcons1 = d_solver.mkTerm(APPLY_CONSTRUCTOR, consTerm, d_solver.mkInteger(1), listnil);
    Term listhead = d_solver.mkTerm(APPLY_SELECTOR, headTerm, listcons1);

    assertTrue(listnil.hasOp());
    assertTrue(listcons1.hasOp());
    assertTrue(listhead.hasOp());
  }

  @Test
  void getOption()
  {
    assertDoesNotThrow(() -> d_solver.getOption("incremental"));
    assertThrows(CVC5ApiException.class, () -> d_solver.getOption("asdf"));
  }

  @Test
  void getOptionNames()
  {
    String[] names = d_solver.getOptionNames();
    assertTrue(names.length > 100);
    assertTrue(Arrays.asList(names).contains("verbose"));
    assertFalse(Arrays.asList(names).contains("foobar"));
  }

  @Test
  void getOptionInfo()
  {
    List<Executable> assertions = new ArrayList<>();
    {
      assertions.add(
          () -> assertThrows(CVC5ApiException.class, () -> d_solver.getOptionInfo("asdf-invalid")));
    }
    {
      OptionInfo info = d_solver.getOptionInfo("verbose");
      assertions.add(() -> assertEquals("verbose", info.getName()));
      assertions.add(
          () -> assertEquals(Arrays.asList(new String[] {}), Arrays.asList(info.getAliases())));
      assertions.add(() -> assertTrue(info.getBaseInfo() instanceof OptionInfo.VoidInfo));
      assertions.add(() -> assertEquals(info.toString(), "OptionInfo{ verbose | void }"));
    }
    {
      // bool type with default
      OptionInfo info = d_solver.getOptionInfo("print-success");
      assertions.add(() -> assertEquals("print-success", info.getName()));
      assertions.add(
          () -> assertEquals(Arrays.asList(new String[] {}), Arrays.asList(info.getAliases())));
      assertions.add(() -> assertTrue(info.getBaseInfo().getClass() == OptionInfo.ValueInfo.class));
      OptionInfo.ValueInfo<Boolean> valInfo = (OptionInfo.ValueInfo<Boolean>) info.getBaseInfo();
      assertions.add(() -> assertEquals(false, valInfo.getDefaultValue().booleanValue()));
      assertions.add(() -> assertEquals(false, valInfo.getCurrentValue().booleanValue()));
      assertions.add(() -> assertEquals(info.booleanValue(), false));
      assertions.add(()
                         -> assertEquals(info.toString(),
                             "OptionInfo{ print-success | bool | false | default false }"));
    }
    {
      // int64 type with default
      OptionInfo info = d_solver.getOptionInfo("verbosity");
      assertions.add(() -> assertEquals("verbosity", info.getName()));
      assertions.add(
          () -> assertEquals(Arrays.asList(new String[] {}), Arrays.asList(info.getAliases())));
      assertions.add(
          () -> assertTrue(info.getBaseInfo().getClass() == OptionInfo.NumberInfo.class));
      OptionInfo.NumberInfo<BigInteger> numInfo =
          (OptionInfo.NumberInfo<BigInteger>) info.getBaseInfo();
      assertions.add(() -> assertEquals(0, numInfo.getDefaultValue().intValue()));
      assertions.add(() -> assertEquals(0, numInfo.getCurrentValue().intValue()));
      assertions.add(
          () -> assertTrue(numInfo.getMinimum() == null && numInfo.getMaximum() == null));
      assertions.add(() -> assertEquals(info.intValue().intValue(), 0));
      assertions.add(
          () -> assertEquals(info.toString(), "OptionInfo{ verbosity | int64_t | 0 | default 0 }"));
    }
    assertAll(assertions);
    {
      OptionInfo info = d_solver.getOptionInfo("rlimit");
      assertEquals(info.getName(), "rlimit");
      assertEquals(Arrays.asList(info.getAliases()), Arrays.asList(new String[] {}));
      assertTrue(info.getBaseInfo().getClass() == OptionInfo.NumberInfo.class);
      OptionInfo.NumberInfo<BigInteger> ni = (OptionInfo.NumberInfo<BigInteger>) info.getBaseInfo();
      assertEquals(ni.getCurrentValue().intValue(), 0);
      assertEquals(ni.getDefaultValue().intValue(), 0);
      assertTrue(ni.getMinimum() == null && ni.getMaximum() == null);
      assertEquals(info.intValue().intValue(), 0);
      assertEquals(info.toString(), "OptionInfo{ rlimit | uint64_t | 0 | default 0 }");
    }
    {
      OptionInfo info = d_solver.getOptionInfo("random-freq");
      assertEquals(info.getName(), "random-freq");
      assertEquals(
          Arrays.asList(info.getAliases()), Arrays.asList(new String[] {"random-frequency"}));
      assertTrue(info.getBaseInfo().getClass() == OptionInfo.NumberInfo.class);
      OptionInfo.NumberInfo<Double> ni = (OptionInfo.NumberInfo<Double>) info.getBaseInfo();
      assertEquals(ni.getCurrentValue(), 0.0);
      assertEquals(ni.getDefaultValue(), 0.0);
      assertTrue(ni.getMinimum() != null && ni.getMaximum() != null);
      assertEquals(ni.getMinimum(), 0.0);
      assertEquals(ni.getMaximum(), 1.0);
      assertEquals(info.doubleValue(), 0.0);
      assertEquals(info.toString(),
          "OptionInfo{ random-freq, random-frequency | double | 0 | default 0 | 0 <= x <= 1 }");
    }
    {
      OptionInfo info = d_solver.getOptionInfo("force-logic");
      assertEquals(info.getName(), "force-logic");
      assertEquals(Arrays.asList(info.getAliases()), Arrays.asList(new String[] {}));
      assertTrue(info.getBaseInfo().getClass() == OptionInfo.ValueInfo.class);
      OptionInfo.ValueInfo<String> ni = (OptionInfo.ValueInfo<String>) info.getBaseInfo();
      assertEquals(ni.getCurrentValue(), "");
      assertEquals(ni.getDefaultValue(), "");
      assertEquals(info.stringValue(), "");
      assertEquals(info.toString(), "OptionInfo{ force-logic | string | \"\" | default \"\" }");
    }
    {
      // mode option
      OptionInfo info = d_solver.getOptionInfo("simplification");
      assertions.clear();
      assertions.add(() -> assertEquals("simplification", info.getName()));
      assertions.add(()
                         -> assertEquals(Arrays.asList(new String[] {"simplification-mode"}),
                             Arrays.asList(info.getAliases())));
      assertions.add(() -> assertTrue(info.getBaseInfo().getClass() == OptionInfo.ModeInfo.class));
      OptionInfo.ModeInfo modeInfo = (OptionInfo.ModeInfo) info.getBaseInfo();
      assertions.add(() -> assertEquals("batch", modeInfo.getDefaultValue()));
      assertions.add(() -> assertEquals("batch", modeInfo.getCurrentValue()));
      assertions.add(() -> assertEquals(2, modeInfo.getModes().length));
      assertions.add(() -> assertTrue(Arrays.asList(modeInfo.getModes()).contains("batch")));
      assertions.add(() -> assertTrue(Arrays.asList(modeInfo.getModes()).contains("none")));
      assertEquals(info.toString(),
          "OptionInfo{ simplification, simplification-mode | mode | batch | default batch | modes: batch, none }");
    }
    assertAll(assertions);
  }

  @Test
  void getStatistics()
  {
    // do some array reasoning to make sure we have a double statistics
    {
      Sort s1 = d_tm.getIntegerSort();
      Sort s2 = d_tm.mkArraySort(s1, s1);
      Term t1 = d_tm.mkConst(s1, "i");
      Term t2 = d_tm.mkVar(s2, "a");
      Term t3 = d_tm.mkTerm(Kind.SELECT, t2, t1);
      d_solver.checkSat();
    }
    Statistics stats = d_solver.getStatistics();
    stats.toString();
    {
      Stat s = stats.get("global::totalTime");
      assertFalse(s.isInternal());
      assertFalse(s.isDefault());
      assertTrue(s.isString());
      assertTrue(s.getString().endsWith("ms"));
      s = stats.get("resource::resourceUnitsUsed");
      s.toString();
      assertTrue(s.isInternal());
      assertFalse(s.isDefault());
      assertTrue(s.isInt());
      assertTrue(s.getInt() >= 0);
      s.toString();
    }
    for (Map.Entry<String, Stat> s : stats)
    {
      assertFalse(s.getKey().isEmpty());
    }
    for (Statistics.ConstIterator it = stats.iterator(true, true); it.hasNext();)
    {
      Map.Entry<String, Stat> elem = it.next();
      if (elem.getKey().equals("theory::arrays::avgIndexListLength"))
      {
        assertTrue(elem.getValue().isInternal());
        assertTrue(elem.getValue().isDouble());
        assertTrue(Double.isNaN(elem.getValue().getDouble()));
        elem.getValue().toString();
      }
    }
  }

  @Test
  void getUnsatAssumptions1()
  {
    d_solver.setOption("incremental", "false");
    d_solver.checkSatAssuming(d_solver.mkFalse());
    assertThrows(CVC5ApiException.class, () -> d_solver.getUnsatAssumptions());
  }

  @Test
  void getUnsatAssumptions2()
  {
    d_solver.setOption("incremental", "true");
    d_solver.setOption("produce-unsat-assumptions", "false");
    d_solver.checkSatAssuming(d_solver.mkFalse());
    assertThrows(CVC5ApiException.class, () -> d_solver.getUnsatAssumptions());
  }

  @Test
  void getUnsatAssumptions3()
  {
    d_solver.setOption("incremental", "true");
    d_solver.setOption("produce-unsat-assumptions", "true");
    d_solver.checkSatAssuming(d_solver.mkFalse());
    assertDoesNotThrow(() -> d_solver.getUnsatAssumptions());
    d_solver.checkSatAssuming(d_solver.mkTrue());
    assertThrows(CVC5ApiException.class, () -> d_solver.getUnsatAssumptions());
  }

  @Test
  void getUnsatCore1()
  {
    d_solver.setOption("incremental", "false");
    d_solver.assertFormula(d_solver.mkFalse());
    d_solver.checkSat();
    assertThrows(CVC5ApiException.class, () -> d_solver.getUnsatCore());
  }

  @Test
  void getUnsatCore2()
  {
    d_solver.setOption("incremental", "false");
    d_solver.setOption("produce-unsat-cores", "false");
    d_solver.assertFormula(d_solver.mkFalse());
    d_solver.checkSat();
    assertThrows(CVC5ApiException.class, () -> d_solver.getUnsatCore());
  }

  @Test
  void getUnsatCoreAndProof()
  {
    d_solver.setOption("incremental", "true");
    d_solver.setOption("produce-unsat-cores", "true");
    d_solver.setOption("produce-proofs", "true");

    Sort uSort = d_solver.mkUninterpretedSort("u");
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort uToIntSort = d_solver.mkFunctionSort(uSort, intSort);
    Sort intPredSort = d_solver.mkFunctionSort(intSort, boolSort);

    Term x = d_solver.mkConst(uSort, "x");
    Term y = d_solver.mkConst(uSort, "y");
    Term f = d_solver.mkConst(uToIntSort, "f");
    Term p = d_solver.mkConst(intPredSort, "p");
    Term zero = d_solver.mkInteger(0);
    Term one = d_solver.mkInteger(1);
    Term f_x = d_solver.mkTerm(Kind.APPLY_UF, f, x);
    Term f_y = d_solver.mkTerm(Kind.APPLY_UF, f, y);
    Term sum = d_solver.mkTerm(Kind.ADD, f_x, f_y);
    Term p_0 = d_solver.mkTerm(Kind.APPLY_UF, p, zero);
    Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
    d_solver.assertFormula(d_solver.mkTerm(Kind.GT, zero, f_x));
    d_solver.assertFormula(d_solver.mkTerm(Kind.GT, zero, f_y));
    d_solver.assertFormula(d_solver.mkTerm(Kind.GT, sum, one));
    d_solver.assertFormula(p_0);
    d_solver.assertFormula(p_f_y.notTerm());
    assertTrue(d_solver.checkSat().isUnsat());

    Term[] unsat_core = d_solver.getUnsatCore();

    assertDoesNotThrow(() -> d_solver.getProof());
    assertDoesNotThrow(() -> d_solver.getProof(ProofComponent.SAT));

    d_solver.resetAssertions();
    for (Term t : unsat_core)
    {
      d_solver.assertFormula(t);
    }
    Result res = d_solver.checkSat();
    assertTrue(res.isUnsat());
    assertDoesNotThrow(() -> d_solver.getProof());
  }

  @Test
  void getProofAndProofToString()
  {
    d_solver.setOption("produce-proofs", "true");

    Sort uSort = d_solver.mkUninterpretedSort("u");
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort uToIntSort = d_solver.mkFunctionSort(uSort, intSort);
    Sort intPredSort = d_solver.mkFunctionSort(intSort, boolSort);

    Term x = d_solver.mkConst(uSort, "x");
    Term y = d_solver.mkConst(uSort, "y");
    Term f = d_solver.mkConst(uToIntSort, "f");
    Term p = d_solver.mkConst(intPredSort, "p");
    Term zero = d_solver.mkInteger(0);
    Term one = d_solver.mkInteger(1);
    Term f_x = d_solver.mkTerm(Kind.APPLY_UF, f, x);
    Term f_y = d_solver.mkTerm(Kind.APPLY_UF, f, y);
    Term sum = d_solver.mkTerm(Kind.ADD, f_x, f_y);
    Term p_0 = d_solver.mkTerm(Kind.APPLY_UF, p, zero);
    Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
    d_solver.assertFormula(d_solver.mkTerm(Kind.GT, zero, f_x));
    d_solver.assertFormula(d_solver.mkTerm(Kind.GT, zero, f_y));
    d_solver.assertFormula(d_solver.mkTerm(Kind.GT, sum, one));
    d_solver.assertFormula(p_0);
    d_solver.assertFormula(p_f_y.notTerm());
    assertTrue(d_solver.checkSat().isUnsat());

    Proof[] proofs = d_solver.getProof();
    assertNotEquals(0, proofs.length);
    String printedProof = d_solver.proofToString(proofs[0]);
    assertFalse(printedProof.isEmpty());
    printedProof = d_solver.proofToString(proofs[0], ProofFormat.ALETHE);
    assertFalse(printedProof.isEmpty());

    proofs = d_solver.getProof(ProofComponent.SAT);
    assertNotEquals(0, proofs.length);
    printedProof = d_solver.proofToString(proofs[0], ProofFormat.NONE);
    assertFalse(printedProof.isEmpty());
  }

  @Test
  void proofToStringAssertionNames()
  {
    d_solver.setOption("produce-proofs", "true");

    Sort uSort = d_solver.mkUninterpretedSort("u");

    Term x = d_solver.mkConst(uSort, "x");
    Term y = d_solver.mkConst(uSort, "y");

    Term x_eq_y = d_solver.mkTerm(Kind.EQUAL, x, y);
    Term not_x_eq_y = d_solver.mkTerm(Kind.NOT, x_eq_y);

    Map<Term, String> assertionNames = new HashMap();
    assertionNames.put(x_eq_y, "as1");
    assertionNames.put(not_x_eq_y, "as2");

    d_solver.assertFormula(x_eq_y);
    d_solver.assertFormula(not_x_eq_y);
    assertTrue(d_solver.checkSat().isUnsat());

    Proof[] proofs = d_solver.getProof();
    assertNotEquals(0, proofs.length);
    String printedProof = d_solver.proofToString(proofs[0], ProofFormat.ALETHE, assertionNames);
    assertFalse(printedProof.isEmpty());
    assertTrue(printedProof.contains("as1"));
    assertTrue(printedProof.contains("as2"));
  }

  @Test
  void getUnsatCoreLemmas1()
  {
    d_solver.assertFormula(d_solver.mkFalse());
    assertTrue(d_solver.checkSat().isUnsat());
    assertThrows(CVC5ApiException.class, () -> d_solver.getUnsatCoreLemmas());
  }

  @Test
  void getUnsatCoreLemmas2()
  {
    d_solver.setOption("produce-unsat-cores", "true");
    d_solver.setOption("unsat-cores-mode", "sat-proof");

    Sort uSort = d_solver.mkUninterpretedSort("u");
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort uToIntSort = d_solver.mkFunctionSort(uSort, intSort);
    Sort intPredSort = d_solver.mkFunctionSort(intSort, boolSort);

    Term x = d_solver.mkConst(uSort, "x");
    Term y = d_solver.mkConst(uSort, "y");
    Term f = d_solver.mkConst(uToIntSort, "f");
    Term p = d_solver.mkConst(intPredSort, "p");
    Term zero = d_solver.mkInteger(0);
    Term one = d_solver.mkInteger(1);
    Term f_x = d_solver.mkTerm(Kind.APPLY_UF, f, x);
    Term f_y = d_solver.mkTerm(Kind.APPLY_UF, f, y);
    Term sum = d_solver.mkTerm(Kind.ADD, f_x, f_y);
    Term p_0 = d_solver.mkTerm(Kind.APPLY_UF, p, zero);
    Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
    d_solver.assertFormula(d_solver.mkTerm(Kind.GT, zero, f_x));
    d_solver.assertFormula(d_solver.mkTerm(Kind.GT, zero, f_y));
    d_solver.assertFormula(d_solver.mkTerm(Kind.GT, sum, one));
    d_solver.assertFormula(p_0);
    d_solver.assertFormula(p_f_y.notTerm());
    assertTrue(d_solver.checkSat().isUnsat());

    d_solver.getUnsatCoreLemmas();
  }

  @Test
  void getDifficulty()
  {
    d_solver.setOption("produce-difficulty", "true");
    // cannot ask before a check sat
    assertThrows(CVC5ApiException.class, () -> d_solver.getDifficulty());
    d_solver.checkSat();
    assertDoesNotThrow(() -> d_solver.getDifficulty());
  }

  @Test
  void getDifficulty2()
  {
    d_solver.checkSat();
    // option is not set
    assertThrows(CVC5ApiException.class, () -> d_solver.getDifficulty());
  }

  @Test
  void getDifficulty3() throws CVC5ApiException
  {
    d_solver.setOption("produce-difficulty", "true");
    Sort intSort = d_solver.getIntegerSort();
    Term x = d_solver.mkConst(intSort, "x");
    Term zero = d_solver.mkInteger(0);
    Term ten = d_solver.mkInteger(10);
    Term f0 = d_solver.mkTerm(GEQ, x, ten);
    Term f1 = d_solver.mkTerm(GEQ, zero, x);
    d_solver.assertFormula(f0);
    d_solver.assertFormula(f1);
    d_solver.checkSat();
    Map<Term, Term> dmap = d_solver.getDifficulty();
    // difficulty should map assertions to integer values
    for (Map.Entry<Term, Term> t : dmap.entrySet())
    {
      assertTrue(t.getKey().equals(f0) || t.getKey().equals(f1));
      assertTrue(t.getValue().getKind() == Kind.CONST_INTEGER);
    }
  }

  @Test
  void getLearnedLiterals()
  {
    d_solver.setOption("produce-learned-literals", "true");
    // cannot ask before a check sat
    assertThrows(CVC5ApiException.class, () -> d_solver.getLearnedLiterals());
    d_solver.checkSat();
    assertDoesNotThrow(() -> d_solver.getLearnedLiterals());
    assertDoesNotThrow(() -> d_solver.getLearnedLiterals(LearnedLitType.PREPROCESS));
  }

  @Test
  void getLearnedLiterals2()
  {
    d_solver.setOption("produce-learned-literals", "true");
    Sort intSort = d_solver.getIntegerSort();
    Term x = d_solver.mkConst(intSort, "x");
    Term y = d_solver.mkConst(intSort, "y");
    Term zero = d_solver.mkInteger(0);
    Term ten = d_solver.mkInteger(10);
    Term f0 = d_solver.mkTerm(GEQ, x, ten);
    Term f1 = d_solver.mkTerm(OR, d_solver.mkTerm(GEQ, zero, x), d_solver.mkTerm(GEQ, y, zero));
    d_solver.assertFormula(f0);
    d_solver.assertFormula(f1);
    d_solver.checkSat();
    assertDoesNotThrow(() -> d_solver.getLearnedLiterals(LearnedLitType.INPUT));
  }

  @Test
  void getTimeoutCoreUnsat() throws CVC5ApiException
  {
    d_solver.setOption("timeout-core-timeout", "100");
    d_solver.setOption("produce-unsat-cores", "true");
    Sort intSort = d_solver.getIntegerSort();
    Term x = d_solver.mkConst(intSort, "x");
    Term tt = d_solver.mkBoolean(true);
    Term hard = d_solver.mkTerm(EQUAL,
        new Term[] {d_solver.mkTerm(MULT, new Term[] {x, x}),
            d_solver.mkInteger("501240912901901249014210220059591")});
    d_solver.assertFormula(tt);
    d_solver.assertFormula(hard);
    Pair<Result, Term[]> res = d_solver.getTimeoutCore();
    assertTrue(res.first.isUnknown());
    assertTrue(res.second.length == 1);
    assertEquals(res.second[0], hard);
  }

  @Test
  void getTimeoutCore() throws CVC5ApiException
  {
    d_solver.setOption("produce-unsat-cores", "true");
    Term ff = d_solver.mkBoolean(false);
    Term tt = d_solver.mkBoolean(true);
    d_solver.assertFormula(tt);
    d_solver.assertFormula(ff);
    d_solver.assertFormula(tt);
    Pair<Result, Term[]> res = d_solver.getTimeoutCore();
    assertTrue(res.first.isUnsat());
    assertTrue(res.second.length == 1);
    assertEquals(res.second[0], ff);
  }

  @Test
  void getTimeoutCoreAssuming() throws CVC5ApiException
  {
    d_solver.setOption("produce-unsat-cores", "true");
    Term ff = d_solver.mkBoolean(false);
    Term tt = d_solver.mkBoolean(true);
    d_solver.assertFormula(tt);
    Pair<Result, Term[]> res = d_solver.getTimeoutCoreAssuming(new Term[] {ff, tt});
    assertTrue(res.first.isUnsat());
    assertTrue(res.second.length == 1);
    assertEquals(res.second[0], ff);
  }

  @Test
  void getTimeoutCoreAssumingEmpty() throws CVC5ApiException
  {
    d_solver.setOption("produce-unsat-cores", "true");
    assertThrows(CVC5ApiException.class, () -> d_solver.getTimeoutCoreAssuming(new Term[] {}));
  }

  @Test
  void getValue1()
  {
    d_solver.setOption("produce-models", "false");
    Term t = d_solver.mkTrue();
    d_solver.assertFormula(t);
    d_solver.checkSat();
    assertThrows(CVC5ApiException.class, () -> d_solver.getValue(t));
  }

  @Test
  void getValue2()
  {
    d_solver.setOption("produce-models", "true");
    Term t = d_solver.mkFalse();
    d_solver.assertFormula(t);
    d_solver.checkSat();
    assertThrows(CVC5ApiException.class, () -> d_solver.getValue(t));
  }

  @Test
  void getValue3()
  {
    d_solver.setOption("produce-models", "true");
    Sort uSort = d_solver.mkUninterpretedSort("u");
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort uToIntSort = d_solver.mkFunctionSort(uSort, intSort);
    Sort intPredSort = d_solver.mkFunctionSort(intSort, boolSort);
    Term[] unsat_core;

    Term x = d_solver.mkConst(uSort, "x");
    Term y = d_solver.mkConst(uSort, "y");
    Term z = d_solver.mkConst(uSort, "z");
    Term f = d_solver.mkConst(uToIntSort, "f");
    Term p = d_solver.mkConst(intPredSort, "p");
    Term zero = d_solver.mkInteger(0);
    Term one = d_solver.mkInteger(1);
    Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
    Term f_y = d_solver.mkTerm(APPLY_UF, f, y);
    Term sum = d_solver.mkTerm(ADD, f_x, f_y);
    Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
    Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);

    d_solver.assertFormula(d_solver.mkTerm(LEQ, zero, f_x));
    d_solver.assertFormula(d_solver.mkTerm(LEQ, zero, f_y));
    d_solver.assertFormula(d_solver.mkTerm(LEQ, sum, one));
    d_solver.assertFormula(p_0.notTerm());
    d_solver.assertFormula(p_f_y);
    assertTrue(d_solver.checkSat().isSat());
    assertDoesNotThrow(() -> d_solver.getValue(x));
    assertDoesNotThrow(() -> d_solver.getValue(y));
    assertDoesNotThrow(() -> d_solver.getValue(z));
    assertDoesNotThrow(() -> d_solver.getValue(sum));
    assertDoesNotThrow(() -> d_solver.getValue(p_f_y));

    Term[] b = d_solver.getValue(new Term[] {x, y, z});

    Solver slv = new Solver();
    assertThrows(CVC5ApiException.class, () -> slv.getValue(x));
  }

  @Test
  void getModelDomainElements()
  {
    d_solver.setOption("produce-models", "true");
    Sort uSort = d_solver.mkUninterpretedSort("u");
    Sort intSort = d_solver.getIntegerSort();
    Term x = d_solver.mkConst(uSort, "x");
    Term y = d_solver.mkConst(uSort, "y");
    Term z = d_solver.mkConst(uSort, "z");
    Term f = d_solver.mkTerm(DISTINCT, x, y, z);
    d_solver.assertFormula(f);
    d_solver.checkSat();
    assertDoesNotThrow(() -> d_solver.getModelDomainElements(uSort));
    assertTrue(d_solver.getModelDomainElements(uSort).length >= 3);
    assertThrows(CVC5ApiException.class, () -> d_solver.getModelDomainElements(intSort));
  }

  @Test
  void getModelDomainElements2()
  {
    d_solver.setOption("produce-models", "true");
    d_solver.setOption("finite-model-find", "true");
    Sort uSort = d_solver.mkUninterpretedSort("u");
    Term x = d_solver.mkVar(uSort, "x");
    Term y = d_solver.mkVar(uSort, "y");
    Term eq = d_solver.mkTerm(EQUAL, x, y);
    Term bvl = d_solver.mkTerm(VARIABLE_LIST, x, y);
    Term f = d_solver.mkTerm(FORALL, bvl, eq);
    d_solver.assertFormula(f);
    d_solver.checkSat();
    assertDoesNotThrow(() -> d_solver.getModelDomainElements(uSort));
    // a model for the above must interpret u as size 1
    assertTrue(d_solver.getModelDomainElements(uSort).length == 1);
  }

  @Test
  void isModelCoreSymbol()
  {
    d_solver.setOption("produce-models", "true");
    d_solver.setOption("model-cores", "simple");
    Sort uSort = d_solver.mkUninterpretedSort("u");
    Term x = d_solver.mkConst(uSort, "x");
    Term y = d_solver.mkConst(uSort, "y");
    Term z = d_solver.mkConst(uSort, "z");
    Term zero = d_solver.mkInteger(0);
    Term f = d_solver.mkTerm(NOT, d_solver.mkTerm(EQUAL, x, y));
    d_solver.assertFormula(f);
    d_solver.checkSat();
    assertTrue(d_solver.isModelCoreSymbol(x));
    assertTrue(d_solver.isModelCoreSymbol(y));
    assertFalse(d_solver.isModelCoreSymbol(z));
    assertThrows(CVC5ApiException.class, () -> d_solver.isModelCoreSymbol(zero));
  }

  @Test
  void getModel()
  {
    d_solver.setOption("produce-models", "true");
    Sort uSort = d_solver.mkUninterpretedSort("u");
    Term x = d_solver.mkConst(uSort, "x");
    Term y = d_solver.mkConst(uSort, "y");
    Term z = d_solver.mkConst(uSort, "z");
    Term f = d_solver.mkTerm(NOT, d_solver.mkTerm(EQUAL, x, y));
    d_solver.assertFormula(f);
    d_solver.checkSat();
    Sort[] sorts = new Sort[] {uSort};
    Term[] terms = new Term[] {x, y};
    assertDoesNotThrow(() -> d_solver.getModel(sorts, terms));
    Term nullTerm = new Term();
    Term[] terms2 = new Term[] {x, y, nullTerm};
    assertThrows(CVC5ApiException.class, () -> d_solver.getModel(sorts, terms2));
  }

  @Test
  void getModel2()
  {
    d_solver.setOption("produce-models", "true");
    Sort[] sorts = new Sort[] {};
    Term[] terms = new Term[] {};
    assertThrows(CVC5ApiException.class, () -> d_solver.getModel(sorts, terms));
  }

  @Test
  void getModel3()
  {
    d_solver.setOption("produce-models", "true");
    Sort[] sorts = new Sort[] {};
    final Term[] terms = new Term[] {};
    d_solver.checkSat();
    assertDoesNotThrow(() -> d_solver.getModel(sorts, terms));
    Sort integer = d_solver.getIntegerSort();
    Sort[] sorts2 = new Sort[] {integer};
    assertThrows(CVC5ApiException.class, () -> d_solver.getModel(sorts2, terms));
  }

  @Test
  void getQuantifierElimination()
  {
    Term x = d_solver.mkVar(d_solver.getBooleanSort(), "x");
    Term forall = d_solver.mkTerm(
        FORALL, d_solver.mkTerm(VARIABLE_LIST, x), d_solver.mkTerm(OR, x, d_solver.mkTerm(NOT, x)));
    assertThrows(CVC5ApiException.class, () -> d_solver.getQuantifierElimination(new Term()));
    Solver slv = new Solver();
    assertThrows(
        CVC5ApiException.class, () -> d_solver.getQuantifierElimination(slv.mkBoolean(false)));

    assertDoesNotThrow(() -> d_solver.getQuantifierElimination(forall));
  }

  @Test
  void getQuantifierEliminationDisjunct()
  {
    Term x = d_solver.mkVar(d_solver.getBooleanSort(), "x");
    Term forall = d_solver.mkTerm(
        FORALL, d_solver.mkTerm(VARIABLE_LIST, x), d_solver.mkTerm(OR, x, d_solver.mkTerm(NOT, x)));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.getQuantifierEliminationDisjunct(new Term()));

    Solver slv = new Solver();
    assertThrows(CVC5ApiException.class,
        () -> d_solver.getQuantifierEliminationDisjunct(slv.mkBoolean(false)));

    assertDoesNotThrow(() -> d_solver.getQuantifierEliminationDisjunct(forall));
  }

  @Test
  void declareSepHeap() throws CVC5ApiException
  {
    d_solver.setLogic("ALL");
    d_solver.setOption("incremental", "false");
    Sort integer = d_solver.getIntegerSort();
    assertDoesNotThrow(() -> d_solver.declareSepHeap(integer, integer));
    // cannot declare separation logic heap more than once
    assertThrows(CVC5ApiException.class, () -> d_solver.declareSepHeap(integer, integer));
  }

  /**
   * Helper function for testGetSeparation{Heap,Nil}TermX. Asserts and checks
   * some simple separation logic constraints.
   */

  void checkSimpleSeparationConstraints(Solver solver)
  {
    Sort integer = solver.getIntegerSort();
    // declare the separation heap
    solver.declareSepHeap(integer, integer);
    Term x = solver.mkConst(integer, "x");
    Term p = solver.mkConst(integer, "p");
    Term heap = solver.mkTerm(SEP_PTO, p, x);
    solver.assertFormula(heap);
    Term nil = solver.mkSepNil(integer);
    solver.assertFormula(nil.eqTerm(solver.mkInteger(5)));
    solver.checkSat();
  }

  @Test
  void getValueSepHeap1() throws CVC5ApiException
  {
    d_solver.setLogic("QF_BV");
    d_solver.setOption("incremental", "false");
    d_solver.setOption("produce-models", "true");
    Term t = d_solver.mkTrue();
    d_solver.assertFormula(t);
    assertThrows(CVC5ApiException.class, () -> d_solver.getValueSepHeap());
  }

  @Test
  void getValueSepHeap2() throws CVC5ApiException
  {
    d_solver.setLogic("ALL");
    d_solver.setOption("incremental", "false");
    d_solver.setOption("produce-models", "false");
    checkSimpleSeparationConstraints(d_solver);
    assertThrows(CVC5ApiException.class, () -> d_solver.getValueSepHeap());
  }

  @Test
  void getValueSepHeap3() throws CVC5ApiException
  {
    d_solver.setLogic("ALL");
    d_solver.setOption("incremental", "false");
    d_solver.setOption("produce-models", "true");
    Term t = d_solver.mkFalse();
    d_solver.assertFormula(t);
    d_solver.checkSat();
    assertThrows(CVC5ApiException.class, () -> d_solver.getValueSepHeap());
  }

  @Test
  void getValueSepHeap4() throws CVC5ApiException
  {
    d_solver.setLogic("ALL");
    d_solver.setOption("incremental", "false");
    d_solver.setOption("produce-models", "true");
    Term t = d_solver.mkTrue();
    d_solver.assertFormula(t);
    d_solver.checkSat();
    assertThrows(CVC5ApiException.class, () -> d_solver.getValueSepHeap());
  }

  @Test
  void getValueSepHeap5() throws CVC5ApiException
  {
    d_solver.setLogic("ALL");
    d_solver.setOption("incremental", "false");
    d_solver.setOption("produce-models", "true");
    checkSimpleSeparationConstraints(d_solver);
    assertDoesNotThrow(() -> d_solver.getValueSepHeap());
  }

  @Test
  void getValueSepNil1() throws CVC5ApiException
  {
    d_solver.setLogic("QF_BV");
    d_solver.setOption("incremental", "false");
    d_solver.setOption("produce-models", "true");
    Term t = d_solver.mkTrue();
    d_solver.assertFormula(t);
    assertThrows(CVC5ApiException.class, () -> d_solver.getValueSepNil());
  }

  @Test
  void getValueSepNil2() throws CVC5ApiException
  {
    d_solver.setLogic("ALL");
    d_solver.setOption("incremental", "false");
    d_solver.setOption("produce-models", "false");
    checkSimpleSeparationConstraints(d_solver);
    assertThrows(CVC5ApiException.class, () -> d_solver.getValueSepNil());
  }

  @Test
  void getValueSepNil3() throws CVC5ApiException
  {
    d_solver.setLogic("ALL");
    d_solver.setOption("incremental", "false");
    d_solver.setOption("produce-models", "true");
    Term t = d_solver.mkFalse();
    d_solver.assertFormula(t);
    d_solver.checkSat();
    assertThrows(CVC5ApiException.class, () -> d_solver.getValueSepNil());
  }

  @Test
  void getValueSepNil4() throws CVC5ApiException
  {
    d_solver.setLogic("ALL");
    d_solver.setOption("incremental", "false");
    d_solver.setOption("produce-models", "true");
    Term t = d_solver.mkTrue();
    d_solver.assertFormula(t);
    d_solver.checkSat();
    assertThrows(CVC5ApiException.class, () -> d_solver.getValueSepNil());
  }

  @Test
  void getValueSepNil5() throws CVC5ApiException
  {
    d_solver.setLogic("ALL");
    d_solver.setOption("incremental", "false");
    d_solver.setOption("produce-models", "true");
    checkSimpleSeparationConstraints(d_solver);
    assertDoesNotThrow(() -> d_solver.getValueSepNil());
  }

  @Test
  void push1()
  {
    d_solver.setOption("incremental", "true");
    assertDoesNotThrow(() -> d_solver.push(1));
    assertThrows(CVC5ApiException.class, () -> d_solver.setOption("incremental", "false"));
    assertThrows(CVC5ApiException.class, () -> d_solver.setOption("incremental", "true"));
  }

  @Test
  void push2()
  {
    d_solver.setOption("incremental", "false");
    assertThrows(CVC5ApiException.class, () -> d_solver.push(1));
  }

  @Test
  void pop1()
  {
    d_solver.setOption("incremental", "false");
    assertThrows(CVC5ApiException.class, () -> d_solver.pop(1));
  }

  @Test
  void pop2()
  {
    d_solver.setOption("incremental", "true");
    assertThrows(CVC5ApiException.class, () -> d_solver.pop(1));
  }

  @Test
  void pop3()
  {
    d_solver.setOption("incremental", "true");
    assertDoesNotThrow(() -> d_solver.push(1));
    assertDoesNotThrow(() -> d_solver.pop(1));
    assertThrows(CVC5ApiException.class, () -> d_solver.pop(1));
  }

  @Test
  void blockModel1()
  {
    Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
    d_solver.assertFormula(x.eqTerm(x));
    d_solver.checkSat();
    assertThrows(CVC5ApiException.class, () -> d_solver.blockModel(BlockModelsMode.LITERALS));
  }

  @Test
  void blockModel2() throws CVC5ApiException
  {
    d_solver.setOption("produce-models", "true");
    Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
    d_solver.assertFormula(x.eqTerm(x));
    assertThrows(CVC5ApiException.class, () -> d_solver.blockModel(BlockModelsMode.LITERALS));
  }

  @Test
  void blockModel3() throws CVC5ApiException
  {
    d_solver.setOption("produce-models", "true");
    Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
    d_solver.assertFormula(x.eqTerm(x));
    d_solver.checkSat();
    assertDoesNotThrow(() -> d_solver.blockModel(BlockModelsMode.LITERALS));
  }

  @Test
  void blockModelValues1() throws CVC5ApiException
  {
    d_solver.setOption("produce-models", "true");
    Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
    d_solver.assertFormula(x.eqTerm(x));
    d_solver.checkSat();
    assertThrows(CVC5ApiException.class, () -> d_solver.blockModelValues(new Term[] {}));
    assertThrows(CVC5ApiException.class, () -> d_solver.blockModelValues(new Term[] {new Term()}));
    Solver slv = new Solver();
    assertDoesNotThrow(() -> d_solver.blockModelValues(new Term[] {slv.mkBoolean(false)}));
  }

  @Test
  void blockModelValues2() throws CVC5ApiException
  {
    d_solver.setOption("produce-models", "true");
    Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
    d_solver.assertFormula(x.eqTerm(x));
    d_solver.checkSat();
    assertDoesNotThrow(() -> d_solver.blockModelValues(new Term[] {x}));
  }

  @Test
  void blockModelValues3() throws CVC5ApiException
  {
    Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
    d_solver.assertFormula(x.eqTerm(x));
    d_solver.checkSat();
    assertThrows(CVC5ApiException.class, () -> d_solver.blockModelValues(new Term[] {x}));
  }

  @Test
  void blockModelValues4() throws CVC5ApiException
  {
    d_solver.setOption("produce-models", "true");
    Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
    d_solver.assertFormula(x.eqTerm(x));
    assertThrows(CVC5ApiException.class, () -> d_solver.blockModelValues(new Term[] {x}));
  }

  @Test
  void blockModelValues5() throws CVC5ApiException
  {
    d_solver.setOption("produce-models", "true");
    Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
    d_solver.assertFormula(x.eqTerm(x));
    d_solver.checkSat();
    assertDoesNotThrow(() -> d_solver.blockModelValues(new Term[] {x}));
  }

  @Test
  void getInstantiations() throws CVC5ApiException
  {
    Sort iSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Term p = d_solver.declareFun("p", new Sort[] {iSort}, boolSort);
    Term x = d_solver.mkVar(iSort, "x");
    Term bvl = d_solver.mkTerm(VARIABLE_LIST, new Term[] {x});
    Term app = d_solver.mkTerm(APPLY_UF, new Term[] {p, x});
    Term q = d_solver.mkTerm(FORALL, new Term[] {bvl, app});
    d_solver.assertFormula(q);
    Term five = d_solver.mkInteger(5);
    Term app2 = d_solver.mkTerm(NOT, new Term[] {d_solver.mkTerm(APPLY_UF, new Term[] {p, five})});
    d_solver.assertFormula(app2);
    assertThrows(CVC5ApiException.class, () -> d_solver.getInstantiations());
    d_solver.checkSat();
    assertDoesNotThrow(() -> d_solver.getInstantiations());
  }

  @Test
  void setInfo() throws CVC5ApiException
  {
    assertThrows(CVC5ApiException.class, () -> d_solver.setInfo("cvc4-lagic", "QF_BV"));
    assertThrows(CVC5ApiException.class, () -> d_solver.setInfo("cvc2-logic", "QF_BV"));
    assertThrows(CVC5ApiException.class, () -> d_solver.setInfo("cvc4-logic", "asdf"));

    assertDoesNotThrow(() -> d_solver.setInfo("source", "asdf"));
    assertDoesNotThrow(() -> d_solver.setInfo("category", "asdf"));
    assertDoesNotThrow(() -> d_solver.setInfo("difficulty", "asdf"));
    assertDoesNotThrow(() -> d_solver.setInfo("filename", "asdf"));
    assertDoesNotThrow(() -> d_solver.setInfo("license", "asdf"));
    assertDoesNotThrow(() -> d_solver.setInfo("name", "asdf"));
    assertDoesNotThrow(() -> d_solver.setInfo("notes", "asdf"));

    assertDoesNotThrow(() -> d_solver.setInfo("smt-lib-version", "2"));
    assertDoesNotThrow(() -> d_solver.setInfo("smt-lib-version", "2.0"));
    assertDoesNotThrow(() -> d_solver.setInfo("smt-lib-version", "2.5"));
    assertDoesNotThrow(() -> d_solver.setInfo("smt-lib-version", "2.6"));
    assertThrows(CVC5ApiException.class, () -> d_solver.setInfo("smt-lib-version", ".0"));

    assertDoesNotThrow(() -> d_solver.setInfo("status", "sat"));
    assertDoesNotThrow(() -> d_solver.setInfo("status", "unsat"));
    assertDoesNotThrow(() -> d_solver.setInfo("status", "unknown"));
    assertThrows(CVC5ApiException.class, () -> d_solver.setInfo("status", "asdf"));
  }

  @Test
  void simplifyApplySubs() throws CVC5ApiException
  {
    d_solver.setOption("incremental", "true");
    Sort intSort = d_tm.getIntegerSort();
    Term x = d_solver.mkConst(intSort, "x");
    Term zero = d_solver.mkInteger(0);
    Term eq = d_solver.mkTerm(EQUAL, x, zero);
    d_solver.assertFormula(eq);
    assertDoesNotThrow(() -> d_solver.checkSat());

    assertEquals(d_solver.simplify(x, false), x);
    assertEquals(d_solver.simplify(x, true), zero);
  }

  @Test
  void simplify() throws CVC5ApiException
  {
    assertThrows(CVC5ApiException.class, () -> d_solver.simplify(new Term()));

    Sort bvSort = d_solver.mkBitVectorSort(32);
    Sort uSort = d_solver.mkUninterpretedSort("u");
    Sort funSort1 = d_solver.mkFunctionSort(new Sort[] {bvSort, bvSort}, bvSort);
    Sort funSort2 = d_solver.mkFunctionSort(uSort, d_solver.getIntegerSort());
    DatatypeDecl consListSpec = d_solver.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", d_solver.getIntegerSort());
    cons.addSelectorSelf("tail");
    consListSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
    consListSpec.addConstructor(nil);
    Sort consListSort = d_solver.mkDatatypeSort(consListSpec);

    Term x = d_solver.mkConst(bvSort, "x");
    assertDoesNotThrow(() -> d_solver.simplify(x));
    Term a = d_solver.mkConst(bvSort, "a");
    assertDoesNotThrow(() -> d_solver.simplify(a));
    Term b = d_solver.mkConst(bvSort, "b");
    assertDoesNotThrow(() -> d_solver.simplify(b));
    Term x_eq_x = d_solver.mkTerm(EQUAL, x, x);
    assertDoesNotThrow(() -> d_solver.simplify(x_eq_x));
    assertNotEquals(d_solver.mkTrue(), x_eq_x);
    assertEquals(d_solver.mkTrue(), d_solver.simplify(x_eq_x));
    Term x_eq_b = d_solver.mkTerm(EQUAL, x, b);
    assertDoesNotThrow(() -> d_solver.simplify(x_eq_b));
    assertNotEquals(d_solver.mkTrue(), x_eq_b);
    assertNotEquals(d_solver.mkTrue(), d_solver.simplify(x_eq_b));
    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.simplify(x));

    Term i1 = d_solver.mkConst(d_solver.getIntegerSort(), "i1");
    assertDoesNotThrow(() -> d_solver.simplify(i1));
    Term i2 = d_solver.mkTerm(MULT, i1, d_solver.mkInteger("23"));
    assertDoesNotThrow(() -> d_solver.simplify(i2));
    assertNotEquals(i1, i2);
    assertNotEquals(i1, d_solver.simplify(i2));
    Term i3 = d_solver.mkTerm(ADD, i1, d_solver.mkInteger(0));
    assertDoesNotThrow(() -> d_solver.simplify(i3));
    assertNotEquals(i1, i3);
    assertEquals(i1, d_solver.simplify(i3));

    Datatype consList = consListSort.getDatatype();
    Term dt1 = d_solver.mkTerm(APPLY_CONSTRUCTOR,
        consList.getConstructor("cons").getTerm(),
        d_solver.mkInteger(0),
        d_solver.mkTerm(APPLY_CONSTRUCTOR, consList.getConstructor("nil").getTerm()));
    assertDoesNotThrow(() -> d_solver.simplify(dt1));
    Term dt2 = d_solver.mkTerm(
        APPLY_SELECTOR, consList.getConstructor("cons").getSelector("head").getTerm(), dt1);
    assertDoesNotThrow(() -> d_solver.simplify(dt2));

    Term b1 = d_solver.mkVar(bvSort, "b1");
    assertDoesNotThrow(() -> d_solver.simplify(b1));
    Term b2 = d_solver.mkVar(bvSort, "b1");
    assertDoesNotThrow(() -> d_solver.simplify(b2));
    Term b3 = d_solver.mkVar(uSort, "b3");
    assertDoesNotThrow(() -> d_solver.simplify(b3));
    Term v1 = d_solver.mkConst(bvSort, "v1");
    assertDoesNotThrow(() -> d_solver.simplify(v1));
    Term v2 = d_solver.mkConst(d_solver.getIntegerSort(), "v2");
    assertDoesNotThrow(() -> d_solver.simplify(v2));
    Term f1 = d_solver.mkConst(funSort1, "f1");
    assertDoesNotThrow(() -> d_solver.simplify(f1));
    Term f2 = d_solver.mkConst(funSort2, "f2");
    assertDoesNotThrow(() -> d_solver.simplify(f2));
    d_solver.defineFunsRec(new Term[] {f1, f2}, new Term[][] {{b1, b2}, {b3}}, new Term[] {v1, v2});
    assertDoesNotThrow(() -> d_solver.simplify(f1));
    assertDoesNotThrow(() -> d_solver.simplify(f2));
  }

  @Test
  void assertFormula()
  {
    assertDoesNotThrow(() -> d_solver.assertFormula(d_solver.mkTrue()));
    assertThrows(CVC5ApiException.class, () -> d_solver.assertFormula(new Term()));
    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.assertFormula(d_solver.mkTrue()));
  }

  @Test
  void checkSat() throws CVC5ApiException
  {
    d_solver.setOption("incremental", "false");
    assertDoesNotThrow(() -> d_solver.checkSat());
    assertThrows(CVC5ApiException.class, () -> d_solver.checkSat());
  }

  @Test
  void checkSatAssuming() throws CVC5ApiException
  {
    d_solver.setOption("incremental", "false");
    assertDoesNotThrow(() -> d_solver.checkSatAssuming(d_solver.mkTrue()));
    assertThrows(CVC5ApiException.class, () -> d_solver.checkSatAssuming(d_solver.mkTrue()));
    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.checkSatAssuming(d_solver.mkTrue()));
  }

  @Test
  void checkSatAssuming1() throws CVC5ApiException
  {
    Sort boolSort = d_solver.getBooleanSort();
    Term x = d_solver.mkConst(boolSort, "x");
    Term y = d_solver.mkConst(boolSort, "y");
    Term z = d_solver.mkTerm(AND, x, y);
    d_solver.setOption("incremental", "true");
    assertDoesNotThrow(() -> d_solver.checkSatAssuming(d_solver.mkTrue()));
    assertThrows(CVC5ApiException.class, () -> d_solver.checkSatAssuming(new Term()));
    assertDoesNotThrow(() -> d_solver.checkSatAssuming(d_solver.mkTrue()));
    assertDoesNotThrow(() -> d_solver.checkSatAssuming(z));
    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.checkSatAssuming(d_solver.mkTrue()));
  }

  @Test
  void checkSatAssuming2() throws CVC5ApiException
  {
    d_solver.setOption("incremental", "true");

    Sort uSort = d_solver.mkUninterpretedSort("u");
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort uToIntSort = d_solver.mkFunctionSort(uSort, intSort);
    Sort intPredSort = d_solver.mkFunctionSort(intSort, boolSort);

    Term n = new Term();
    // Constants
    Term x = d_solver.mkConst(uSort, "x");
    Term y = d_solver.mkConst(uSort, "y");
    // Functions
    Term f = d_solver.mkConst(uToIntSort, "f");
    Term p = d_solver.mkConst(intPredSort, "p");
    // Values
    Term zero = d_solver.mkInteger(0);
    Term one = d_solver.mkInteger(1);
    // Terms
    Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
    Term f_y = d_solver.mkTerm(APPLY_UF, f, y);
    Term sum = d_solver.mkTerm(ADD, f_x, f_y);
    Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
    Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
    // Assertions
    Term assertions = d_solver.mkTerm(AND,
        new Term[] {
            d_solver.mkTerm(LEQ, zero, f_x), // 0 <= f(x)
            d_solver.mkTerm(LEQ, zero, f_y), // 0 <= f(y)
            d_solver.mkTerm(LEQ, sum, one), // f(x) + f(y) <= 1
            p_0.notTerm(), // not p(0)
            p_f_y // p(f(y))
        });

    assertDoesNotThrow(() -> d_solver.checkSatAssuming(d_solver.mkTrue()));
    d_solver.assertFormula(assertions);
    assertDoesNotThrow(() -> d_solver.checkSatAssuming(d_solver.mkTerm(DISTINCT, x, y)));
    assertDoesNotThrow(()
                           -> d_solver.checkSatAssuming(
                               new Term[] {d_solver.mkFalse(), d_solver.mkTerm(DISTINCT, x, y)}));
    assertThrows(CVC5ApiException.class, () -> d_solver.checkSatAssuming(n));
    assertThrows(CVC5ApiException.class,
        () -> d_solver.checkSatAssuming(new Term[] {n, d_solver.mkTerm(DISTINCT, x, y)}));

    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.checkSatAssuming(d_solver.mkTrue()));
  }

  @Test
  void setLogic() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_solver.setLogic("AUFLIRA"));
    assertThrows(CVC5ApiException.class, () -> d_solver.setLogic("AF_BV"));
    d_solver.assertFormula(d_solver.mkTrue());
    assertThrows(CVC5ApiException.class, () -> d_solver.setLogic("AUFLIRA"));
  }

  @Test
  void isLogicSet() throws CVC5ApiException
  {
    assertFalse(d_solver.isLogicSet());
    assertDoesNotThrow(() -> d_solver.setLogic("QF_BV"));
    assertTrue(d_solver.isLogicSet());
  }

  @Test
  void getLogic() throws CVC5ApiException
  {
    assertThrows(CVC5ApiException.class, () -> d_solver.getLogic());
    assertDoesNotThrow(() -> d_solver.setLogic("QF_BV"));
    assertEquals(d_solver.getLogic(), "QF_BV");
  }

  @Test
  void setOption() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_solver.setOption("bv-sat-solver", "minisat"));
    assertThrows(CVC5ApiException.class, () -> d_solver.setOption("bv-sat-solver", "1"));
    d_solver.assertFormula(d_solver.mkTrue());
    assertThrows(CVC5ApiException.class, () -> d_solver.setOption("bv-sat-solver", "minisat"));
  }

  @Test
  void resetAssertions() throws CVC5ApiException
  {
    d_solver.setOption("incremental", "true");

    Sort bvSort = d_solver.mkBitVectorSort(4);
    Term one = d_solver.mkBitVector(4, 1);
    Term x = d_solver.mkConst(bvSort, "x");
    Term ule = d_solver.mkTerm(BITVECTOR_ULE, x, one);
    Term srem = d_solver.mkTerm(BITVECTOR_SREM, one, x);
    d_solver.push(4);
    Term slt = d_solver.mkTerm(BITVECTOR_SLT, srem, one);
    d_solver.resetAssertions();
    d_solver.checkSatAssuming(new Term[] {slt, ule});
  }

  @Test
  void declareSygusVar() throws CVC5ApiException
  {
    d_solver.setOption("sygus", "true");
    Sort boolSort = d_solver.getBooleanSort();
    Sort intSort = d_solver.getIntegerSort();
    Sort funSort = d_solver.mkFunctionSort(intSort, boolSort);

    assertDoesNotThrow(() -> d_solver.declareSygusVar("", boolSort));
    assertDoesNotThrow(() -> d_solver.declareSygusVar("", funSort));
    assertDoesNotThrow(() -> d_solver.declareSygusVar(("b"), boolSort));

    assertThrows(CVC5ApiException.class, () -> d_solver.declareSygusVar("", new Sort()));
    assertThrows(CVC5ApiException.class, () -> d_solver.declareSygusVar("a", new Sort()));

    Solver slv = new Solver();
    slv.setOption("sygus", "true");
    assertDoesNotThrow(() -> slv.declareSygusVar("", boolSort));
  }

  @Test
  void mkGrammar() throws CVC5ApiException
  {
    Term nullTerm = new Term();
    Term boolTerm = d_solver.mkBoolean(true);
    Term boolVar = d_solver.mkVar(d_solver.getBooleanSort());
    Term intVar = d_solver.mkVar(d_solver.getIntegerSort());

    assertDoesNotThrow(() -> d_solver.mkGrammar(new Term[] {}, new Term[] {intVar}));
    assertDoesNotThrow(() -> d_solver.mkGrammar(new Term[] {boolVar}, new Term[] {intVar}));

    assertThrows(CVC5ApiException.class, () -> d_solver.mkGrammar(new Term[] {}, new Term[] {}));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.mkGrammar(new Term[] {}, new Term[] {nullTerm}));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.mkGrammar(new Term[] {}, new Term[] {boolTerm}));
    assertThrows(CVC5ApiException.class,
        () -> d_solver.mkGrammar(new Term[] {boolTerm}, new Term[] {intVar}));

    Solver slv = new Solver();
    slv.setOption("sygus", "true");
    Term boolVar2 = slv.mkVar(slv.getBooleanSort());
    Term intVar2 = slv.mkVar(slv.getIntegerSort());
    assertDoesNotThrow(() -> slv.mkGrammar(new Term[] {boolVar2}, new Term[] {intVar2}));

    assertDoesNotThrow(() -> slv.mkGrammar(new Term[] {boolVar}, new Term[] {intVar2}));
    assertDoesNotThrow(() -> slv.mkGrammar(new Term[] {boolVar2}, new Term[] {intVar}));
  }

  @Test
  void synthFun() throws CVC5ApiException
  {
    d_solver.setOption("sygus", "true");
    Sort nullSort = new Sort();
    Sort bool = d_solver.getBooleanSort();
    Sort integer = d_solver.getIntegerSort();

    Term nullTerm = new Term();
    Term x = d_solver.mkVar(bool);

    Term start1 = d_solver.mkVar(bool);
    Term start2 = d_solver.mkVar(integer);

    Grammar g1 = d_solver.mkGrammar(new Term[] {x}, new Term[] {start1});
    g1.addRule(start1, d_solver.mkBoolean(false));

    Grammar g2 = d_solver.mkGrammar(new Term[] {x}, new Term[] {start2});
    g2.addRule(start2, d_solver.mkInteger(0));

    assertDoesNotThrow(() -> d_solver.synthFun("", new Term[] {}, bool));
    assertDoesNotThrow(() -> d_solver.synthFun("f1", new Term[] {x}, bool));
    assertDoesNotThrow(() -> d_solver.synthFun("f2", new Term[] {x}, bool, g1));

    assertThrows(
        CVC5ApiException.class, () -> d_solver.synthFun("f3", new Term[] {nullTerm}, bool));
    assertThrows(CVC5ApiException.class, () -> d_solver.synthFun("f4", new Term[] {}, nullSort));
    assertThrows(CVC5ApiException.class, () -> d_solver.synthFun("f6", new Term[] {x}, bool, g2));

    Solver slv = new Solver();
    slv.setOption("sygus", "true");
    Term x2 = slv.mkVar(slv.getBooleanSort());
    assertDoesNotThrow(() -> slv.synthFun("f1", new Term[] {x2}, slv.getBooleanSort()));

    assertDoesNotThrow(() -> slv.synthFun("", new Term[] {}, d_solver.getBooleanSort()));
    assertDoesNotThrow(() -> slv.synthFun("f1", new Term[] {x}, d_solver.getBooleanSort()));
  }

  @Test
  void addSygusConstraint() throws CVC5ApiException
  {
    d_solver.setOption("sygus", "true");
    Term nullTerm = new Term();
    Term boolTerm = d_solver.mkBoolean(true);
    Term intTerm = d_solver.mkInteger(1);

    assertDoesNotThrow(() -> d_solver.addSygusConstraint(boolTerm));
    assertThrows(CVC5ApiException.class, () -> d_solver.addSygusConstraint(nullTerm));
    assertThrows(CVC5ApiException.class, () -> d_solver.addSygusConstraint(intTerm));

    Solver slv = new Solver();
    slv.setOption("sygus", "true");
    assertDoesNotThrow(() -> slv.addSygusConstraint(boolTerm));
  }

  @Test
  void getSygusConstraints()
  {
    d_solver.setOption("sygus", "true");
    Term trueTerm = d_solver.mkBoolean(true);
    Term falseTerm = d_solver.mkBoolean(false);
    d_solver.addSygusConstraint(trueTerm);
    d_solver.addSygusConstraint(falseTerm);
    Term[] constraints = d_solver.getSygusConstraints();
    assertEquals(constraints[0], trueTerm);
    assertEquals(constraints[1], falseTerm);
  }

  @Test
  void addSygusAssume()
  {
    d_solver.setOption("sygus", "true");
    Term nullTerm = new Term();
    Term boolTerm = d_solver.mkBoolean(false);
    Term intTerm = d_solver.mkInteger(1);

    assertDoesNotThrow(() -> d_solver.addSygusAssume(boolTerm));
    assertThrows(CVC5ApiException.class, () -> d_solver.addSygusAssume(nullTerm));
    assertThrows(CVC5ApiException.class, () -> d_solver.addSygusAssume(intTerm));

    Solver slv = new Solver();
    slv.setOption("sygus", "true");
    assertDoesNotThrow(() -> slv.addSygusAssume(boolTerm));
  }

  @Test
  void getSygusAssumptions()
  {
    d_solver.setOption("sygus", "true");
    Term trueTerm = d_solver.mkBoolean(true);
    Term falseTerm = d_solver.mkBoolean(false);
    d_solver.addSygusAssume(trueTerm);
    d_solver.addSygusAssume(falseTerm);
    Term[] assumptions = d_solver.getSygusAssumptions();
    assertEquals(assumptions[0], trueTerm);
    assertEquals(assumptions[1], falseTerm);
  }

  @Test
  void addSygusInvConstraint() throws CVC5ApiException
  {
    d_solver.setOption("sygus", "true");
    Sort bool = d_solver.getBooleanSort();
    Sort real = d_solver.getRealSort();

    Term nullTerm = new Term();
    Term intTerm = d_solver.mkInteger(1);

    Term inv = d_solver.declareFun("inv", new Sort[] {real}, bool);
    Term pre = d_solver.declareFun("pre", new Sort[] {real}, bool);
    Term trans = d_solver.declareFun("trans", new Sort[] {real, real}, bool);
    Term post = d_solver.declareFun("post", new Sort[] {real}, bool);

    Term inv1 = d_solver.declareFun("inv1", new Sort[] {real}, real);

    Term trans1 = d_solver.declareFun("trans1", new Sort[] {bool, real}, bool);
    Term trans2 = d_solver.declareFun("trans2", new Sort[] {real, bool}, bool);
    Term trans3 = d_solver.declareFun("trans3", new Sort[] {real, real}, real);

    assertDoesNotThrow(() -> d_solver.addSygusInvConstraint(inv, pre, trans, post));

    assertThrows(
        CVC5ApiException.class, () -> d_solver.addSygusInvConstraint(nullTerm, pre, trans, post));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.addSygusInvConstraint(inv, nullTerm, trans, post));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.addSygusInvConstraint(inv, pre, nullTerm, post));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.addSygusInvConstraint(inv, pre, trans, nullTerm));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.addSygusInvConstraint(intTerm, pre, trans, post));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.addSygusInvConstraint(inv1, pre, trans, post));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.addSygusInvConstraint(inv, trans, trans, post));
    assertThrows(CVC5ApiException.class, () -> d_solver.addSygusInvConstraint(inv, pre, pre, post));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.addSygusInvConstraint(inv, pre, trans1, post));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.addSygusInvConstraint(inv, pre, trans2, post));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.addSygusInvConstraint(inv, pre, trans3, post));
    assertThrows(
        CVC5ApiException.class, () -> d_solver.addSygusInvConstraint(inv, pre, trans, trans));

    Solver slv = new Solver();
    slv.setOption("sygus", "true");
    Sort boolean2 = slv.getBooleanSort();
    Sort real2 = slv.getRealSort();
    Term inv22 = slv.declareFun("inv", new Sort[] {real2}, boolean2);
    Term pre22 = slv.declareFun("pre", new Sort[] {real2}, boolean2);
    Term trans22 = slv.declareFun("trans", new Sort[] {real2, real2}, boolean2);
    Term post22 = slv.declareFun("post", new Sort[] {real2}, boolean2);
    assertDoesNotThrow(() -> slv.addSygusInvConstraint(inv22, pre22, trans22, post22));

    assertDoesNotThrow(() -> slv.addSygusInvConstraint(inv, pre22, trans22, post22));
    assertDoesNotThrow(() -> slv.addSygusInvConstraint(inv22, pre, trans22, post22));
    assertDoesNotThrow(() -> slv.addSygusInvConstraint(inv22, pre22, trans, post22));
    assertDoesNotThrow(() -> slv.addSygusInvConstraint(inv22, pre22, trans22, post));
  }

  @Test
  void checkSynth() throws CVC5ApiException
  {
    assertThrows(CVC5ApiException.class, () -> d_solver.checkSynth());
    d_solver.setOption("sygus", "true");
    assertDoesNotThrow(() -> d_solver.checkSynth());
  }

  @Test
  void getSynthSolution() throws CVC5ApiException
  {
    d_solver.setOption("sygus", "true");
    d_solver.setOption("incremental", "false");

    Term nullTerm = new Term();
    Term x = d_solver.mkBoolean(false);
    Term f = d_solver.synthFun("f", new Term[] {}, d_solver.getBooleanSort());

    assertThrows(CVC5ApiException.class, () -> d_solver.getSynthSolution(f));

    SynthResult sr = d_solver.checkSynth();
    assertEquals(sr.hasSolution(), true);

    assertDoesNotThrow(() -> d_solver.getSynthSolution(f));
    assertDoesNotThrow(() -> d_solver.getSynthSolution(f));

    assertThrows(CVC5ApiException.class, () -> d_solver.getSynthSolution(nullTerm));
    assertThrows(CVC5ApiException.class, () -> d_solver.getSynthSolution(x));

    Solver slv = new Solver();
    assertThrows(CVC5ApiException.class, () -> slv.getSynthSolution(f));
  }

  @Test
  void getSynthSolutions() throws CVC5ApiException
  {
    d_solver.setOption("sygus", "true");
    d_solver.setOption("incremental", "false");

    Term nullTerm = new Term();
    Term x = d_solver.mkBoolean(false);
    Term f = d_solver.synthFun("f", new Term[] {}, d_solver.getBooleanSort());

    assertThrows(CVC5ApiException.class, () -> d_solver.getSynthSolutions(new Term[] {}));
    assertThrows(CVC5ApiException.class, () -> d_solver.getSynthSolutions(new Term[] {f}));

    d_solver.checkSynth();

    assertDoesNotThrow(() -> d_solver.getSynthSolutions(new Term[] {f}));
    assertDoesNotThrow(() -> d_solver.getSynthSolutions(new Term[] {f, f}));

    assertThrows(CVC5ApiException.class, () -> d_solver.getSynthSolutions(new Term[] {}));
    assertThrows(CVC5ApiException.class, () -> d_solver.getSynthSolutions(new Term[] {nullTerm}));
    assertThrows(CVC5ApiException.class, () -> d_solver.getSynthSolutions(new Term[] {x}));

    Solver slv = new Solver();
    assertThrows(CVC5ApiException.class, () -> slv.getSynthSolutions(new Term[] {x}));
  }
  @Test
  void checkSynthNext() throws CVC5ApiException
  {
    d_solver.setOption("sygus", "true");
    d_solver.setOption("incremental", "true");
    Term f = d_solver.synthFun("f", new Term[] {}, d_solver.getBooleanSort());

    SynthResult sr = d_solver.checkSynth();
    assertEquals(sr.hasSolution(), true);
    assertDoesNotThrow(() -> d_solver.getSynthSolutions(new Term[] {f}));
    sr = d_solver.checkSynthNext();
    assertEquals(sr.hasSolution(), true);
    assertDoesNotThrow(() -> d_solver.getSynthSolutions(new Term[] {f}));
  }

  @Test
  void checkSynthNext2() throws CVC5ApiException
  {
    d_solver.setOption("sygus", "true");
    d_solver.setOption("incremental", "false");
    Term f = d_solver.synthFun("f", new Term[] {}, d_solver.getBooleanSort());

    d_solver.checkSynth();
    assertThrows(CVC5ApiException.class, () -> d_solver.checkSynthNext());
  }

  @Test
  void checkSynthNext3() throws CVC5ApiException
  {
    d_solver.setOption("sygus", "true");
    d_solver.setOption("incremental", "true");
    Term f = d_solver.synthFun("f", new Term[] {}, d_solver.getBooleanSort());

    assertThrows(CVC5ApiException.class, () -> d_solver.checkSynthNext());
  }

  @Test
  void findSynth() throws CVC5ApiException
  {
    d_solver.setOption("sygus", "true");
    Sort boolSort = d_solver.getBooleanSort();
    Term start = d_solver.mkVar(boolSort);
    Grammar g = d_solver.mkGrammar(new Term[] {}, new Term[] {start});
    Term truen = d_solver.mkBoolean(true);
    Term falsen = d_solver.mkBoolean(false);
    g.addRule(start, truen);
    g.addRule(start, falsen);
    Term f = d_solver.synthFun("f", new Term[] {}, d_solver.getBooleanSort(), g);

    // should enumerate based on the grammar of the function to synthesize above
    Term t = d_solver.findSynth(FindSynthTarget.ENUM);
    assertTrue(!t.isNull() && t.getSort().isBoolean());
  }

  @Test
  void findSynth2() throws CVC5ApiException
  {
    d_solver.setOption("sygus", "true");
    d_solver.setOption("incremental", "true");
    Sort boolSort = d_solver.getBooleanSort();
    Term start = d_solver.mkVar(boolSort);
    Grammar g = d_solver.mkGrammar(new Term[] {}, new Term[] {start});
    Term truen = d_solver.mkBoolean(true);
    Term falsen = d_solver.mkBoolean(false);
    g.addRule(start, truen);
    g.addRule(start, falsen);

    // should enumerate true/false
    Term t = d_solver.findSynth(FindSynthTarget.ENUM, g);
    assertTrue(!t.isNull() && t.getSort().isBoolean());
    t = d_solver.findSynthNext();
    assertTrue(!t.isNull() && t.getSort().isBoolean());
  }

  @Test
  void tupleProject() throws CVC5ApiException
  {
    Term[] elements = new Term[] {d_solver.mkBoolean(true),
        d_solver.mkInteger(3),
        d_solver.mkString("C"),
        d_solver.mkTerm(SET_SINGLETON, d_solver.mkString("Z"))};

    Term tuple = d_solver.mkTuple(elements);

    int[] indices1 = new int[] {};
    int[] indices2 = new int[] {0};
    int[] indices3 = new int[] {0, 1};
    int[] indices4 = new int[] {0, 0, 2, 2, 3, 3, 0};
    int[] indices5 = new int[] {4};
    int[] indices6 = new int[] {0, 4};

    assertDoesNotThrow(() -> d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices1), tuple));
    assertDoesNotThrow(() -> d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices2), tuple));
    assertDoesNotThrow(() -> d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices3), tuple));
    assertDoesNotThrow(() -> d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices4), tuple));

    assertThrows(CVC5ApiException.class,
        () -> d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices5), tuple));
    assertThrows(CVC5ApiException.class,
        () -> d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices6), tuple));

    int[] indices = new int[] {0, 3, 2, 0, 1, 2};

    Op op = d_solver.mkOp(TUPLE_PROJECT, indices);
    Term projection = d_solver.mkTerm(op, tuple);

    Datatype datatype = tuple.getSort().getDatatype();
    DatatypeConstructor constructor = datatype.getConstructor(0);

    for (int i = 0; i < indices.length; i++)
    {
      Term selectorTerm = constructor.getSelector(indices[i]).getTerm();
      Term selectedTerm = d_solver.mkTerm(APPLY_SELECTOR, selectorTerm, tuple);
      Term simplifiedTerm = d_solver.simplify(selectedTerm);
      assertEquals(elements[indices[i]], simplifiedTerm);
    }

    assertEquals("((_ tuple.project 0 3 2 0 1 2) (tuple true 3 \"C\" "
            + "(set.singleton \"Z\")))",
        projection.toString());
  }

  @Test
  void declareOracleFunError() throws CVC5ApiException
  {
    Sort iSort = d_solver.getIntegerSort();
    // cannot declare without option
    assertThrows(CVC5ApiException.class,
        ()
            -> d_solver.declareOracleFun(
                "f", new Sort[] {iSort}, iSort, (input) -> d_solver.mkInteger(0)));
    d_solver.setOption("oracles", "true");
    Sort nullSort = new Sort();
    // bad sort
    assertThrows(CVC5ApiException.class,
        ()
            -> d_solver.declareOracleFun(
                "f", new Sort[] {nullSort}, iSort, (input) -> d_solver.mkInteger(0)));
  }

  @Test
  void declareOracleFunUnsat() throws CVC5ApiException
  {
    d_solver.setOption("oracles", "true");
    Sort iSort = d_solver.getIntegerSort();
    // f is the function implementing (lambda ((x Int)) (+ x 1))
    Term f = d_solver.declareOracleFun("f", new Sort[] {iSort}, iSort, (input) -> {
      if (input[0].getIntegerValue().signum() > -1)
      {
        return d_solver.mkInteger(input[0].getIntegerValue().add(new BigInteger("1")).toString());
      }
      return d_solver.mkInteger(0);
    });
    Term three = d_solver.mkInteger(3);
    Term five = d_solver.mkInteger(5);
    Term eq =
        d_solver.mkTerm(EQUAL, new Term[] {d_solver.mkTerm(APPLY_UF, new Term[] {f, three}), five});
    d_solver.assertFormula(eq);
    // (f 3) = 5
    assertTrue(d_solver.checkSat().isUnsat());
  }

  @Test
  void declareOracleFunSat() throws CVC5ApiException
  {
    d_solver.setOption("oracles", "true");
    d_solver.setOption("produce-models", "true");
    Sort iSort = d_solver.getIntegerSort();

    // f is the function implementing (lambda ((x Int)) (% x 10))
    Term f = d_solver.declareOracleFun("f", new Sort[] {iSort}, iSort, (input) -> {
      if (input[0].getIntegerValue().signum() > -1)
      {
        return d_solver.mkInteger(input[0].getIntegerValue().mod(new BigInteger("10")).toString());
      }
      return d_solver.mkInteger(0);
    });
    Term seven = d_solver.mkInteger(7);
    Term x = d_solver.mkConst(iSort, "x");
    Term lb = d_solver.mkTerm(Kind.GEQ, new Term[] {x, d_solver.mkInteger(0)});
    d_solver.assertFormula(lb);
    Term ub = d_solver.mkTerm(Kind.LEQ, new Term[] {x, d_solver.mkInteger(100)});
    d_solver.assertFormula(ub);
    Term eq = d_solver.mkTerm(
        Kind.EQUAL, new Term[] {d_solver.mkTerm(APPLY_UF, new Term[] {f, x}), seven});
    d_solver.assertFormula(eq);
    // x >= 0 ^ x <= 100 ^ (f x) = 7
    assertTrue(d_solver.checkSat().isSat());
    Term xval = d_solver.getValue(x);
    assertTrue(xval.getIntegerValue().signum() > -1);
    assertTrue(xval.getIntegerValue().mod(new BigInteger("10")).equals(new BigInteger("7")));
  }

  @Test
  void declareOracleFunSat2() throws CVC5ApiException
  {
    d_solver.setOption("oracles", "true");
    d_solver.setOption("produce-models", "true");
    Sort iSort = d_solver.getIntegerSort();
    Sort bSort = d_solver.getBooleanSort();
    // eq is the function implementing (lambda ((x Int) (y Int)) (= x y))
    Term eq = d_solver.declareOracleFun("eq", new Sort[] {iSort, iSort}, bSort, (input) -> {
      return d_solver.mkBoolean(input[0].equals(input[1]));
    });
    Term x = d_solver.mkConst(iSort, "x");
    Term y = d_solver.mkConst(iSort, "y");
    Term neq = d_solver.mkTerm(
        Kind.NOT, new Term[] {d_solver.mkTerm(Kind.APPLY_UF, new Term[] {eq, x, y})});
    d_solver.assertFormula(neq);
    // (not (eq x y))
    assertTrue(d_solver.checkSat().isSat());
    Term xval = d_solver.getValue(x);
    Term yval = d_solver.getValue(y);
    assertFalse(xval.equals(yval));
  }

  class PluginUnsat extends AbstractPlugin
  {
    public PluginUnsat(TermManager tm)
    {
      super(tm);
    }

    @Override
    public Term[] check()
    {
      // add the "false" lemma.
      Term flem = d_tm.mkBoolean(false);
      return new Term[] {flem};
    }
    @Override
    public void notifySatClause(Term cl)
    {
    }

    @Override
    public void notifyTheoryLemma(Term lem)
    {
    }
    @Override
    public String getName()
    {
      return "PluginUnsat";
    }
  }

  @Test
  void pluginUnsat()
  {
    PluginUnsat pu = new PluginUnsat(d_tm);
    d_solver.addPlugin(pu);
    assertTrue(pu.getName().equals("PluginUnsat"));
    // should be unsat since the plugin above asserts "false" as a lemma
    assertTrue(d_solver.checkSat().isUnsat());
  }

  class PluginListen extends AbstractPlugin
  {
    public PluginListen(TermManager tm)
    {
      super(tm);
    }
    @Override
    public Term[] check()
    {
      return new Term[0];
    }
    @Override
    public void notifySatClause(Term cl)
    {
      d_hasSeenSatClause = true;
    }
    public boolean hasSeenSatClause()
    {
      return d_hasSeenSatClause;
    }
    @Override
    public void notifyTheoryLemma(Term lem)
    {
      d_hasSeenTheoryLemma = true;
    }
    public boolean hasSeenTheoryLemma()
    {
      return d_hasSeenTheoryLemma;
    }
    @Override
    public String getName()
    {
      return "PluginListen";
    }

    /** Reference to the term manager */
    private TermManager d_tm;
    /** have we seen a theory lemma? */
    private boolean d_hasSeenTheoryLemma;
    /** have we seen a SAT clause? */
    private boolean d_hasSeenSatClause;
  };

  @Test
  void pluginListen()
  {
    // NOTE: this shouldn't be necessary but ensures notifySatClause is called here.
    d_solver.setOption("plugin-notify-sat-clause-in-solve", "false");
    PluginListen pl = new PluginListen(d_tm);
    d_solver.addPlugin(pl);
    Sort stringSort = d_tm.getStringSort();
    Term x = d_tm.mkConst(stringSort, "x");
    Term y = d_tm.mkConst(stringSort, "y");
    Term ctn1 = d_tm.mkTerm(Kind.STRING_CONTAINS, new Term[] {x, y});
    Term ctn2 = d_tm.mkTerm(Kind.STRING_CONTAINS, new Term[] {y, x});
    d_solver.assertFormula(d_tm.mkTerm(Kind.OR, new Term[] {ctn1, ctn2}));
    Term lx = d_tm.mkTerm(Kind.STRING_LENGTH, new Term[] {x});
    Term ly = d_tm.mkTerm(Kind.STRING_LENGTH, new Term[] {y});
    Term lc = d_tm.mkTerm(Kind.GT, new Term[] {lx, ly});
    d_solver.assertFormula(lc);
    assertTrue(d_solver.checkSat().isSat());
    // above input formulas should induce a theory lemma and SAT clause learning
    assertTrue(pl.hasSeenTheoryLemma());
    assertTrue(pl.hasSeenSatClause());
  }

  @Test
  void getVersion() throws CVC5ApiException
  {
    System.out.println(d_solver.getVersion());
  }

  @Test
  void verticalBars() throws CVC5ApiException
  {
    Term a = d_solver.declareFun("|a |", new Sort[] {}, d_solver.getRealSort());
    assertEquals("|a |", a.toString());
  }

  @Test
  void multipleSolvers() throws CVC5ApiException
  {
    Term function1, function2, value1, value2, definedFunction;
    Sort integerSort;
    Term zero;
    {
      Solver s1 = new Solver();
      s1.setLogic("ALL");
      s1.setOption("produce-models", "true");
      integerSort = s1.getIntegerSort();
      function1 = s1.declareFun("f1", new Sort[] {}, s1.getIntegerSort());
      Term x = s1.mkVar(integerSort, "x");
      zero = s1.mkInteger(0);
      definedFunction = s1.defineFun("f", new Term[] {x}, integerSort, zero);
      s1.assertFormula(function1.eqTerm(zero));
      s1.checkSat();
      value1 = s1.getValue(function1);
    }
    assertEquals(zero, value1);
    {
      Solver s2 = new Solver();
      s2.setLogic("ALL");
      s2.setOption("produce-models", "true");
      function2 = s2.declareFun("function2", new Sort[] {}, integerSort);
      s2.assertFormula(function2.eqTerm(value1));
      s2.checkSat();
      value2 = s2.getValue(function2);
    }
    assertEquals(value1, value2);
    {
      Solver s3 = new Solver();
      s3.setLogic("ALL");
      s3.setOption("produce-models", "true");
      function2 = s3.declareFun("function3", new Sort[] {}, integerSort);
      Term apply = s3.mkTerm(APPLY_UF, new Term[] {definedFunction, zero});
      s3.assertFormula(function2.eqTerm(apply));
      s3.checkSat();
      Term value3 = s3.getValue(function2);
      assertEquals(value1, value3);
    }
  }
}
