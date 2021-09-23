/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Makai Mann, Andrew Reynolds, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Term class.
 */

package cvc5;

import static cvc5.Kind.*;
import static org.junit.jupiter.api.Assertions.*;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class TermTest {
  private Solver d_solver;

  @BeforeEach
  void setUp() {
    d_solver = new Solver();
  }

  @Test
  void eq() {
    Sort uSort = d_solver.mkUninterpretedSort("u");
    Term x = d_solver.mkVar(uSort, "x");
    Term y = d_solver.mkVar(uSort, "y");
    Term z = d_solver.getNullTerm();

    assertTrue(x == x);
    assertFalse(x != x);
    assertFalse(x == y);
    assertTrue(x != y);
    assertFalse((x == z));
    assertTrue(x != z);
  }

  @Test
  void getId() {
    Term n = d_solver.getNullTerm();
    assertThrows(CVC5ApiException.class, () -> n.getId());
    Term x = d_solver.mkVar(d_solver.getIntegerSort(), "x");
    assertDoesNotThrow(() -> x.getId());
    Term y = x;
    assertEquals(x.getId(), y.getId());

    Term z = d_solver.mkVar(d_solver.getIntegerSort(), "z");
    assertNotEquals(x.getId(), z.getId());
  }

  @Test
  void getKind() throws CVC5ApiException {
    Sort uSort = d_solver.mkUninterpretedSort("u");
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(uSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term n = d_solver.getNullTerm();
    assertThrows(CVC5ApiException.class, () -> n.getKind());
    Term x = d_solver.mkVar(uSort, "x");
    assertDoesNotThrow(() -> x.getKind());
    Term y = d_solver.mkVar(uSort, "y");
    assertDoesNotThrow(() -> y.getKind());

    Term f = d_solver.mkVar(funSort1, "f");
    assertDoesNotThrow(() -> f.getKind());
    Term p = d_solver.mkVar(funSort2, "p");
    assertDoesNotThrow(() -> p.getKind());

    Term zero = d_solver.mkInteger(0);
    assertDoesNotThrow(() -> zero.getKind());

    Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
    assertDoesNotThrow(() -> f_x.getKind());
    Term f_y = d_solver.mkTerm(APPLY_UF, f, y);
    assertDoesNotThrow(() -> f_y.getKind());
    Term sum = d_solver.mkTerm(PLUS, f_x, f_y);
    assertDoesNotThrow(() -> sum.getKind());
    Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
    assertDoesNotThrow(() -> p_0.getKind());
    Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
    assertDoesNotThrow(() -> p_f_y.getKind());

    // Sequence kinds do not exist internally, test that the API properly
    // converts them back.
    Sort seqSort = d_solver.mkSequenceSort(intSort);
    Term s = d_solver.mkConst(seqSort, "s");
    Term ss = d_solver.mkTerm(SEQ_CONCAT, s, s);
    assertEquals(ss.getKind(), SEQ_CONCAT);
  }

  @Test
  void getSort() throws CVC5ApiException {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term n = d_solver.getNullTerm();
    assertThrows(CVC5ApiException.class, () -> n.getSort());
    Term x = d_solver.mkVar(bvSort, "x");
    assertDoesNotThrow(() -> x.getSort());
    assertEquals(x.getSort(), bvSort);
    Term y = d_solver.mkVar(bvSort, "y");
    assertDoesNotThrow(() -> y.getSort());
    assertEquals(y.getSort(), bvSort);

    Term f = d_solver.mkVar(funSort1, "f");
    assertDoesNotThrow(() -> f.getSort());
    assertEquals(f.getSort(), funSort1);
    Term p = d_solver.mkVar(funSort2, "p");
    assertDoesNotThrow(() -> p.getSort());
    assertEquals(p.getSort(), funSort2);

    Term zero = d_solver.mkInteger(0);
    assertDoesNotThrow(() -> zero.getSort());
    assertEquals(zero.getSort(), intSort);

    Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
    assertDoesNotThrow(() -> f_x.getSort());
    assertEquals(f_x.getSort(), intSort);
    Term f_y = d_solver.mkTerm(APPLY_UF, f, y);
    assertDoesNotThrow(() -> f_y.getSort());
    assertEquals(f_y.getSort(), intSort);
    Term sum = d_solver.mkTerm(PLUS, f_x, f_y);
    assertDoesNotThrow(() -> sum.getSort());
    assertEquals(sum.getSort(), intSort);
    Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
    assertDoesNotThrow(() -> p_0.getSort());
    assertEquals(p_0.getSort(), boolSort);
    Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
    assertDoesNotThrow(() -> p_f_y.getSort());
    assertEquals(p_f_y.getSort(), boolSort);
  }

  @Test
  void getOp() throws CVC5ApiException {
    Sort intsort = d_solver.getIntegerSort();
    Sort bvsort = d_solver.mkBitVectorSort(8);
    Sort arrsort = d_solver.mkArraySort(bvsort, intsort);
    Sort funsort = d_solver.mkFunctionSort(intsort, bvsort);

    Term x = d_solver.mkConst(intsort, "x");
    Term a = d_solver.mkConst(arrsort, "a");
    Term b = d_solver.mkConst(bvsort, "b");

    assertFalse(x.hasOp());
    assertThrows(CVC5ApiException.class, () -> x.getOp());

    Term ab = d_solver.mkTerm(SELECT, a, b);
    Op ext = d_solver.mkOp(BITVECTOR_EXTRACT, 4, 0);
    Term extb = d_solver.mkTerm(ext, b);

    assertTrue(ab.hasOp());
    assertFalse(ab.getOp().isIndexed());
    // can compare directly to a Kind (will invoke Op constructor)
    assertTrue(extb.hasOp());
    assertTrue(extb.getOp().isIndexed());
    assertEquals(extb.getOp(), ext);

    Term f = d_solver.mkConst(funsort, "f");
    Term fx = d_solver.mkTerm(APPLY_UF, f, x);

    assertFalse(f.hasOp());
    assertThrows(CVC5ApiException.class, () -> f.getOp());
    assertTrue(fx.hasOp());
    List<Term> children = new ArrayList();

    Iterator<Term> iterator = fx.iterator();
    for (Term t : fx) {
      children.add(t);
    }

    // testing rebuild from op and children
    assertEquals(fx, d_solver.mkTerm(fx.getOp(), children));

    // Test Datatypes Ops
    Sort sort = d_solver.mkParamSort("T");
    DatatypeDecl listDecl = d_solver.mkDatatypeDecl("paramlist", sort);
    DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
    DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
    cons.addSelector("head", sort);
    cons.addSelectorSelf("tail");
    listDecl.addConstructor(cons);
    listDecl.addConstructor(nil);
    Sort listSort = d_solver.mkDatatypeSort(listDecl);
    Sort intListSort =
        listSort.instantiate(new Sort[] {d_solver.getIntegerSort()});
    Term c = d_solver.mkConst(intListSort, "c");
    Datatype list = listSort.getDatatype();
    // list datatype constructor and selector operator terms
    Term consOpTerm = list.getConstructorTerm("cons");
    Term nilOpTerm = list.getConstructorTerm("nil");
  }

  @Test
  void isNull() throws CVC5ApiException {
    Term x = d_solver.getNullTerm();
    assertTrue(x.isNull());
    x = d_solver.mkVar(d_solver.mkBitVectorSort(4), "x");
    assertFalse(x.isNull());
  }

  @Test
  void notTerm() throws CVC5ApiException {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    assertThrows(
        CVC5ApiException.class, () -> d_solver.getNullTerm().notTerm());
    Term b = d_solver.mkTrue();
    assertDoesNotThrow(() -> b.notTerm());
    Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
    assertThrows(CVC5ApiException.class, () -> x.notTerm());
    Term f = d_solver.mkVar(funSort1, "f");
    assertThrows(CVC5ApiException.class, () -> f.notTerm());
    Term p = d_solver.mkVar(funSort2, "p");
    assertThrows(CVC5ApiException.class, () -> p.notTerm());
    Term zero = d_solver.mkInteger(0);
    assertThrows(CVC5ApiException.class, () -> zero.notTerm());
    Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
    assertThrows(CVC5ApiException.class, () -> f_x.notTerm());
    Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
    assertThrows(CVC5ApiException.class, () -> sum.notTerm());
    Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
    assertDoesNotThrow(() -> p_0.notTerm());
    Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
    assertDoesNotThrow(() -> p_f_x.notTerm());
  }

  @Test
  void andTerm() throws CVC5ApiException {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term b = d_solver.mkTrue();
    assertThrows(
        CVC5ApiException.class, () -> d_solver.getNullTerm().andTerm(b));
    assertThrows(
        CVC5ApiException.class, () -> b.andTerm(d_solver.getNullTerm()));
    assertDoesNotThrow(() -> b.andTerm(b));
    Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
    assertThrows(CVC5ApiException.class, () -> x.andTerm(b));
    assertThrows(CVC5ApiException.class, () -> x.andTerm(x));
    Term f = d_solver.mkVar(funSort1, "f");
    assertThrows(CVC5ApiException.class, () -> f.andTerm(b));
    assertThrows(CVC5ApiException.class, () -> f.andTerm(x));
    assertThrows(CVC5ApiException.class, () -> f.andTerm(f));
    Term p = d_solver.mkVar(funSort2, "p");
    assertThrows(CVC5ApiException.class, () -> p.andTerm(b));
    assertThrows(CVC5ApiException.class, () -> p.andTerm(x));
    assertThrows(CVC5ApiException.class, () -> p.andTerm(f));
    assertThrows(CVC5ApiException.class, () -> p.andTerm(p));
    Term zero = d_solver.mkInteger(0);
    assertThrows(CVC5ApiException.class, () -> zero.andTerm(b));
    assertThrows(CVC5ApiException.class, () -> zero.andTerm(x));
    assertThrows(CVC5ApiException.class, () -> zero.andTerm(f));
    assertThrows(CVC5ApiException.class, () -> zero.andTerm(p));
    assertThrows(CVC5ApiException.class, () -> zero.andTerm(zero));
    Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
    assertThrows(CVC5ApiException.class, () -> f_x.andTerm(b));
    assertThrows(CVC5ApiException.class, () -> f_x.andTerm(x));
    assertThrows(CVC5ApiException.class, () -> f_x.andTerm(f));
    assertThrows(CVC5ApiException.class, () -> f_x.andTerm(p));
    assertThrows(CVC5ApiException.class, () -> f_x.andTerm(zero));
    assertThrows(CVC5ApiException.class, () -> f_x.andTerm(f_x));
    Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
    assertThrows(CVC5ApiException.class, () -> sum.andTerm(b));
    assertThrows(CVC5ApiException.class, () -> sum.andTerm(x));
    assertThrows(CVC5ApiException.class, () -> sum.andTerm(f));
    assertThrows(CVC5ApiException.class, () -> sum.andTerm(p));
    assertThrows(CVC5ApiException.class, () -> sum.andTerm(zero));
    assertThrows(CVC5ApiException.class, () -> sum.andTerm(f_x));
    assertThrows(CVC5ApiException.class, () -> sum.andTerm(sum));
    Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
    assertDoesNotThrow(() -> p_0.andTerm(b));
    assertThrows(CVC5ApiException.class, () -> p_0.andTerm(x));
    assertThrows(CVC5ApiException.class, () -> p_0.andTerm(f));
    assertThrows(CVC5ApiException.class, () -> p_0.andTerm(p));
    assertThrows(CVC5ApiException.class, () -> p_0.andTerm(zero));
    assertThrows(CVC5ApiException.class, () -> p_0.andTerm(f_x));
    assertThrows(CVC5ApiException.class, () -> p_0.andTerm(sum));
    assertDoesNotThrow(() -> p_0.andTerm(p_0));
    Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
    assertDoesNotThrow(() -> p_f_x.andTerm(b));
    assertThrows(CVC5ApiException.class, () -> p_f_x.andTerm(x));
    assertThrows(CVC5ApiException.class, () -> p_f_x.andTerm(f));
    assertThrows(CVC5ApiException.class, () -> p_f_x.andTerm(p));
    assertThrows(CVC5ApiException.class, () -> p_f_x.andTerm(zero));
    assertThrows(CVC5ApiException.class, () -> p_f_x.andTerm(f_x));
    assertThrows(CVC5ApiException.class, () -> p_f_x.andTerm(sum));
    assertDoesNotThrow(() -> p_f_x.andTerm(p_0));
    assertDoesNotThrow(() -> p_f_x.andTerm(p_f_x));
  }

  @Test
  void orTerm() throws CVC5ApiException {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term b = d_solver.mkTrue();
    assertThrows(
        CVC5ApiException.class, () -> d_solver.getNullTerm().orTerm(b));
    assertThrows(
        CVC5ApiException.class, () -> b.orTerm(d_solver.getNullTerm()));
    assertDoesNotThrow(() -> b.orTerm(b));
    Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
    assertThrows(CVC5ApiException.class, () -> x.orTerm(b));
    assertThrows(CVC5ApiException.class, () -> x.orTerm(x));
    Term f = d_solver.mkVar(funSort1, "f");
    assertThrows(CVC5ApiException.class, () -> f.orTerm(b));
    assertThrows(CVC5ApiException.class, () -> f.orTerm(x));
    assertThrows(CVC5ApiException.class, () -> f.orTerm(f));
    Term p = d_solver.mkVar(funSort2, "p");
    assertThrows(CVC5ApiException.class, () -> p.orTerm(b));
    assertThrows(CVC5ApiException.class, () -> p.orTerm(x));
    assertThrows(CVC5ApiException.class, () -> p.orTerm(f));
    assertThrows(CVC5ApiException.class, () -> p.orTerm(p));
    Term zero = d_solver.mkInteger(0);
    assertThrows(CVC5ApiException.class, () -> zero.orTerm(b));
    assertThrows(CVC5ApiException.class, () -> zero.orTerm(x));
    assertThrows(CVC5ApiException.class, () -> zero.orTerm(f));
    assertThrows(CVC5ApiException.class, () -> zero.orTerm(p));
    assertThrows(CVC5ApiException.class, () -> zero.orTerm(zero));
    Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
    assertThrows(CVC5ApiException.class, () -> f_x.orTerm(b));
    assertThrows(CVC5ApiException.class, () -> f_x.orTerm(x));
    assertThrows(CVC5ApiException.class, () -> f_x.orTerm(f));
    assertThrows(CVC5ApiException.class, () -> f_x.orTerm(p));
    assertThrows(CVC5ApiException.class, () -> f_x.orTerm(zero));
    assertThrows(CVC5ApiException.class, () -> f_x.orTerm(f_x));
    Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
    assertThrows(CVC5ApiException.class, () -> sum.orTerm(b));
    assertThrows(CVC5ApiException.class, () -> sum.orTerm(x));
    assertThrows(CVC5ApiException.class, () -> sum.orTerm(f));
    assertThrows(CVC5ApiException.class, () -> sum.orTerm(p));
    assertThrows(CVC5ApiException.class, () -> sum.orTerm(zero));
    assertThrows(CVC5ApiException.class, () -> sum.orTerm(f_x));
    assertThrows(CVC5ApiException.class, () -> sum.orTerm(sum));
    Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
    assertDoesNotThrow(() -> p_0.orTerm(b));
    assertThrows(CVC5ApiException.class, () -> p_0.orTerm(x));
    assertThrows(CVC5ApiException.class, () -> p_0.orTerm(f));
    assertThrows(CVC5ApiException.class, () -> p_0.orTerm(p));
    assertThrows(CVC5ApiException.class, () -> p_0.orTerm(zero));
    assertThrows(CVC5ApiException.class, () -> p_0.orTerm(f_x));
    assertThrows(CVC5ApiException.class, () -> p_0.orTerm(sum));
    assertDoesNotThrow(() -> p_0.orTerm(p_0));
    Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
    assertDoesNotThrow(() -> p_f_x.orTerm(b));
    assertThrows(CVC5ApiException.class, () -> p_f_x.orTerm(x));
    assertThrows(CVC5ApiException.class, () -> p_f_x.orTerm(f));
    assertThrows(CVC5ApiException.class, () -> p_f_x.orTerm(p));
    assertThrows(CVC5ApiException.class, () -> p_f_x.orTerm(zero));
    assertThrows(CVC5ApiException.class, () -> p_f_x.orTerm(f_x));
    assertThrows(CVC5ApiException.class, () -> p_f_x.orTerm(sum));
    assertDoesNotThrow(() -> p_f_x.orTerm(p_0));
    assertDoesNotThrow(() -> p_f_x.orTerm(p_f_x));
  }

  @Test
  void xorTerm() throws CVC5ApiException {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term b = d_solver.mkTrue();
    assertThrows(
        CVC5ApiException.class, () -> d_solver.getNullTerm().xorTerm(b));
    assertThrows(
        CVC5ApiException.class, () -> b.xorTerm(d_solver.getNullTerm()));
    assertDoesNotThrow(() -> b.xorTerm(b));
    Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
    assertThrows(CVC5ApiException.class, () -> x.xorTerm(b));
    assertThrows(CVC5ApiException.class, () -> x.xorTerm(x));
    Term f = d_solver.mkVar(funSort1, "f");
    assertThrows(CVC5ApiException.class, () -> f.xorTerm(b));
    assertThrows(CVC5ApiException.class, () -> f.xorTerm(x));
    assertThrows(CVC5ApiException.class, () -> f.xorTerm(f));
    Term p = d_solver.mkVar(funSort2, "p");
    assertThrows(CVC5ApiException.class, () -> p.xorTerm(b));
    assertThrows(CVC5ApiException.class, () -> p.xorTerm(x));
    assertThrows(CVC5ApiException.class, () -> p.xorTerm(f));
    assertThrows(CVC5ApiException.class, () -> p.xorTerm(p));
    Term zero = d_solver.mkInteger(0);
    assertThrows(CVC5ApiException.class, () -> zero.xorTerm(b));
    assertThrows(CVC5ApiException.class, () -> zero.xorTerm(x));
    assertThrows(CVC5ApiException.class, () -> zero.xorTerm(f));
    assertThrows(CVC5ApiException.class, () -> zero.xorTerm(p));
    assertThrows(CVC5ApiException.class, () -> zero.xorTerm(zero));
    Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
    assertThrows(CVC5ApiException.class, () -> f_x.xorTerm(b));
    assertThrows(CVC5ApiException.class, () -> f_x.xorTerm(x));
    assertThrows(CVC5ApiException.class, () -> f_x.xorTerm(f));
    assertThrows(CVC5ApiException.class, () -> f_x.xorTerm(p));
    assertThrows(CVC5ApiException.class, () -> f_x.xorTerm(zero));
    assertThrows(CVC5ApiException.class, () -> f_x.xorTerm(f_x));
    Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
    assertThrows(CVC5ApiException.class, () -> sum.xorTerm(b));
    assertThrows(CVC5ApiException.class, () -> sum.xorTerm(x));
    assertThrows(CVC5ApiException.class, () -> sum.xorTerm(f));
    assertThrows(CVC5ApiException.class, () -> sum.xorTerm(p));
    assertThrows(CVC5ApiException.class, () -> sum.xorTerm(zero));
    assertThrows(CVC5ApiException.class, () -> sum.xorTerm(f_x));
    assertThrows(CVC5ApiException.class, () -> sum.xorTerm(sum));
    Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
    assertDoesNotThrow(() -> p_0.xorTerm(b));
    assertThrows(CVC5ApiException.class, () -> p_0.xorTerm(x));
    assertThrows(CVC5ApiException.class, () -> p_0.xorTerm(f));
    assertThrows(CVC5ApiException.class, () -> p_0.xorTerm(p));
    assertThrows(CVC5ApiException.class, () -> p_0.xorTerm(zero));
    assertThrows(CVC5ApiException.class, () -> p_0.xorTerm(f_x));
    assertThrows(CVC5ApiException.class, () -> p_0.xorTerm(sum));
    assertDoesNotThrow(() -> p_0.xorTerm(p_0));
    Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
    assertDoesNotThrow(() -> p_f_x.xorTerm(b));
    assertThrows(CVC5ApiException.class, () -> p_f_x.xorTerm(x));
    assertThrows(CVC5ApiException.class, () -> p_f_x.xorTerm(f));
    assertThrows(CVC5ApiException.class, () -> p_f_x.xorTerm(p));
    assertThrows(CVC5ApiException.class, () -> p_f_x.xorTerm(zero));
    assertThrows(CVC5ApiException.class, () -> p_f_x.xorTerm(f_x));
    assertThrows(CVC5ApiException.class, () -> p_f_x.xorTerm(sum));
    assertDoesNotThrow(() -> p_f_x.xorTerm(p_0));
    assertDoesNotThrow(() -> p_f_x.xorTerm(p_f_x));
  }

  @Test
  void eqTerm() throws CVC5ApiException {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term b = d_solver.mkTrue();
    assertThrows(
        CVC5ApiException.class, () -> d_solver.getNullTerm().eqTerm(b));
    assertThrows(
        CVC5ApiException.class, () -> b.eqTerm(d_solver.getNullTerm()));
    assertDoesNotThrow(() -> b.eqTerm(b));
    Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
    assertThrows(CVC5ApiException.class, () -> x.eqTerm(b));
    assertDoesNotThrow(() -> x.eqTerm(x));
    Term f = d_solver.mkVar(funSort1, "f");
    assertThrows(CVC5ApiException.class, () -> f.eqTerm(b));
    assertThrows(CVC5ApiException.class, () -> f.eqTerm(x));
    assertDoesNotThrow(() -> f.eqTerm(f));
    Term p = d_solver.mkVar(funSort2, "p");
    assertThrows(CVC5ApiException.class, () -> p.eqTerm(b));
    assertThrows(CVC5ApiException.class, () -> p.eqTerm(x));
    assertThrows(CVC5ApiException.class, () -> p.eqTerm(f));
    assertDoesNotThrow(() -> p.eqTerm(p));
    Term zero = d_solver.mkInteger(0);
    assertThrows(CVC5ApiException.class, () -> zero.eqTerm(b));
    assertThrows(CVC5ApiException.class, () -> zero.eqTerm(x));
    assertThrows(CVC5ApiException.class, () -> zero.eqTerm(f));
    assertThrows(CVC5ApiException.class, () -> zero.eqTerm(p));
    assertDoesNotThrow(() -> zero.eqTerm(zero));
    Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
    assertThrows(CVC5ApiException.class, () -> f_x.eqTerm(b));
    assertThrows(CVC5ApiException.class, () -> f_x.eqTerm(x));
    assertThrows(CVC5ApiException.class, () -> f_x.eqTerm(f));
    assertThrows(CVC5ApiException.class, () -> f_x.eqTerm(p));
    assertDoesNotThrow(() -> f_x.eqTerm(zero));
    assertDoesNotThrow(() -> f_x.eqTerm(f_x));
    Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
    assertThrows(CVC5ApiException.class, () -> sum.eqTerm(b));
    assertThrows(CVC5ApiException.class, () -> sum.eqTerm(x));
    assertThrows(CVC5ApiException.class, () -> sum.eqTerm(f));
    assertThrows(CVC5ApiException.class, () -> sum.eqTerm(p));
    assertDoesNotThrow(() -> sum.eqTerm(zero));
    assertDoesNotThrow(() -> sum.eqTerm(f_x));
    assertDoesNotThrow(() -> sum.eqTerm(sum));
    Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
    assertDoesNotThrow(() -> p_0.eqTerm(b));
    assertThrows(CVC5ApiException.class, () -> p_0.eqTerm(x));
    assertThrows(CVC5ApiException.class, () -> p_0.eqTerm(f));
    assertThrows(CVC5ApiException.class, () -> p_0.eqTerm(p));
    assertThrows(CVC5ApiException.class, () -> p_0.eqTerm(zero));
    assertThrows(CVC5ApiException.class, () -> p_0.eqTerm(f_x));
    assertThrows(CVC5ApiException.class, () -> p_0.eqTerm(sum));
    assertDoesNotThrow(() -> p_0.eqTerm(p_0));
    Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
    assertDoesNotThrow(() -> p_f_x.eqTerm(b));
    assertThrows(CVC5ApiException.class, () -> p_f_x.eqTerm(x));
    assertThrows(CVC5ApiException.class, () -> p_f_x.eqTerm(f));
    assertThrows(CVC5ApiException.class, () -> p_f_x.eqTerm(p));
    assertThrows(CVC5ApiException.class, () -> p_f_x.eqTerm(zero));
    assertThrows(CVC5ApiException.class, () -> p_f_x.eqTerm(f_x));
    assertThrows(CVC5ApiException.class, () -> p_f_x.eqTerm(sum));
    assertDoesNotThrow(() -> p_f_x.eqTerm(p_0));
    assertDoesNotThrow(() -> p_f_x.eqTerm(p_f_x));
  }

  @Test
  void impTerm() throws CVC5ApiException {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term b = d_solver.mkTrue();
    assertThrows(
        CVC5ApiException.class, () -> d_solver.getNullTerm().impTerm(b));
    assertThrows(
        CVC5ApiException.class, () -> b.impTerm(d_solver.getNullTerm()));
    assertDoesNotThrow(() -> b.impTerm(b));
    Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
    assertThrows(CVC5ApiException.class, () -> x.impTerm(b));
    assertThrows(CVC5ApiException.class, () -> x.impTerm(x));
    Term f = d_solver.mkVar(funSort1, "f");
    assertThrows(CVC5ApiException.class, () -> f.impTerm(b));
    assertThrows(CVC5ApiException.class, () -> f.impTerm(x));
    assertThrows(CVC5ApiException.class, () -> f.impTerm(f));
    Term p = d_solver.mkVar(funSort2, "p");
    assertThrows(CVC5ApiException.class, () -> p.impTerm(b));
    assertThrows(CVC5ApiException.class, () -> p.impTerm(x));
    assertThrows(CVC5ApiException.class, () -> p.impTerm(f));
    assertThrows(CVC5ApiException.class, () -> p.impTerm(p));
    Term zero = d_solver.mkInteger(0);
    assertThrows(CVC5ApiException.class, () -> zero.impTerm(b));
    assertThrows(CVC5ApiException.class, () -> zero.impTerm(x));
    assertThrows(CVC5ApiException.class, () -> zero.impTerm(f));
    assertThrows(CVC5ApiException.class, () -> zero.impTerm(p));
    assertThrows(CVC5ApiException.class, () -> zero.impTerm(zero));
    Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
    assertThrows(CVC5ApiException.class, () -> f_x.impTerm(b));
    assertThrows(CVC5ApiException.class, () -> f_x.impTerm(x));
    assertThrows(CVC5ApiException.class, () -> f_x.impTerm(f));
    assertThrows(CVC5ApiException.class, () -> f_x.impTerm(p));
    assertThrows(CVC5ApiException.class, () -> f_x.impTerm(zero));
    assertThrows(CVC5ApiException.class, () -> f_x.impTerm(f_x));
    Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
    assertThrows(CVC5ApiException.class, () -> sum.impTerm(b));
    assertThrows(CVC5ApiException.class, () -> sum.impTerm(x));
    assertThrows(CVC5ApiException.class, () -> sum.impTerm(f));
    assertThrows(CVC5ApiException.class, () -> sum.impTerm(p));
    assertThrows(CVC5ApiException.class, () -> sum.impTerm(zero));
    assertThrows(CVC5ApiException.class, () -> sum.impTerm(f_x));
    assertThrows(CVC5ApiException.class, () -> sum.impTerm(sum));
    Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
    assertDoesNotThrow(() -> p_0.impTerm(b));
    assertThrows(CVC5ApiException.class, () -> p_0.impTerm(x));
    assertThrows(CVC5ApiException.class, () -> p_0.impTerm(f));
    assertThrows(CVC5ApiException.class, () -> p_0.impTerm(p));
    assertThrows(CVC5ApiException.class, () -> p_0.impTerm(zero));
    assertThrows(CVC5ApiException.class, () -> p_0.impTerm(f_x));
    assertThrows(CVC5ApiException.class, () -> p_0.impTerm(sum));
    assertDoesNotThrow(() -> p_0.impTerm(p_0));
    Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
    assertDoesNotThrow(() -> p_f_x.impTerm(b));
    assertThrows(CVC5ApiException.class, () -> p_f_x.impTerm(x));
    assertThrows(CVC5ApiException.class, () -> p_f_x.impTerm(f));
    assertThrows(CVC5ApiException.class, () -> p_f_x.impTerm(p));
    assertThrows(CVC5ApiException.class, () -> p_f_x.impTerm(zero));
    assertThrows(CVC5ApiException.class, () -> p_f_x.impTerm(f_x));
    assertThrows(CVC5ApiException.class, () -> p_f_x.impTerm(sum));
    assertDoesNotThrow(() -> p_f_x.impTerm(p_0));
    assertDoesNotThrow(() -> p_f_x.impTerm(p_f_x));
  }

  @Test
  void iteTerm() throws CVC5ApiException {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term b = d_solver.mkTrue();
    assertThrows(
        CVC5ApiException.class, () -> d_solver.getNullTerm().iteTerm(b, b));
    assertThrows(
        CVC5ApiException.class, () -> b.iteTerm(d_solver.getNullTerm(), b));
    assertThrows(
        CVC5ApiException.class, () -> b.iteTerm(b, d_solver.getNullTerm()));
    assertDoesNotThrow(() -> b.iteTerm(b, b));
    Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
    assertDoesNotThrow(() -> b.iteTerm(x, x));
    assertDoesNotThrow(() -> b.iteTerm(b, b));
    assertThrows(CVC5ApiException.class, () -> b.iteTerm(x, b));
    assertThrows(CVC5ApiException.class, () -> x.iteTerm(x, x));
    assertThrows(CVC5ApiException.class, () -> x.iteTerm(x, b));
    Term f = d_solver.mkVar(funSort1, "f");
    assertThrows(CVC5ApiException.class, () -> f.iteTerm(b, b));
    assertThrows(CVC5ApiException.class, () -> x.iteTerm(b, x));
    Term p = d_solver.mkVar(funSort2, "p");
    assertThrows(CVC5ApiException.class, () -> p.iteTerm(b, b));
    assertThrows(CVC5ApiException.class, () -> p.iteTerm(x, b));
    Term zero = d_solver.mkInteger(0);
    assertThrows(CVC5ApiException.class, () -> zero.iteTerm(x, x));
    assertThrows(CVC5ApiException.class, () -> zero.iteTerm(x, b));
    Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
    assertThrows(CVC5ApiException.class, () -> f_x.iteTerm(b, b));
    assertThrows(CVC5ApiException.class, () -> f_x.iteTerm(b, x));
    Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
    assertThrows(CVC5ApiException.class, () -> sum.iteTerm(x, x));
    assertThrows(CVC5ApiException.class, () -> sum.iteTerm(b, x));
    Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
    assertDoesNotThrow(() -> p_0.iteTerm(b, b));
    assertDoesNotThrow(() -> p_0.iteTerm(x, x));
    assertThrows(CVC5ApiException.class, () -> p_0.iteTerm(x, b));
    Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
    assertDoesNotThrow(() -> p_f_x.iteTerm(b, b));
    assertDoesNotThrow(() -> p_f_x.iteTerm(x, x));
    assertThrows(CVC5ApiException.class, () -> p_f_x.iteTerm(x, b));
  }

  @Test
  void termAssignment() {
    Term t1 = d_solver.mkInteger(1);
    Term t2 = t1;
    t2 = d_solver.mkInteger(2);
    assertEquals(t1, d_solver.mkInteger(1));
  }

  @Test
  void termCompare() {
    Term t1 = d_solver.mkInteger(1);
    Term t2 =
        d_solver.mkTerm(PLUS, d_solver.mkInteger(2), d_solver.mkInteger(2));
    Term t3 =
        d_solver.mkTerm(PLUS, d_solver.mkInteger(2), d_solver.mkInteger(2));
    assertTrue(t2.compareTo(t3) >= 0);
    assertTrue(t2.compareTo(t3) <= 0);
    assertTrue((t1.compareTo(t2) > 0) != (t1.compareTo(t2) < 0));
    assertTrue(
        (t1.compareTo(t2) > 0 || t1.equals(t2)) == (t1.compareTo(t2) >= 0));
  }

  @Test
  void termChildren() throws CVC5ApiException {
    // simple term 2+3
    Term two = d_solver.mkInteger(2);
    Term t1 = d_solver.mkTerm(PLUS, two, d_solver.mkInteger(3));
    assertEquals(t1.getChild(0), two);
    assertEquals(t1.getNumChildren(), 2);
    Term tnull = d_solver.getNullTerm();
    assertThrows(CVC5ApiException.class, () -> tnull.getNumChildren());

    // apply term f(2)
    Sort intSort = d_solver.getIntegerSort();
    Sort fsort = d_solver.mkFunctionSort(intSort, intSort);
    Term f = d_solver.mkConst(fsort, "f");
    Term t2 = d_solver.mkTerm(APPLY_UF, f, two);
    // due to our higher-order view of terms, we treat f as a child of APPLY_UF
    assertEquals(t2.getNumChildren(), 2);
    assertEquals(t2.getChild(0), f);
    assertEquals(t2.getChild(1), two);
    assertThrows(CVC5ApiException.class, () -> tnull.getChild(0));
  }

  @Test
  void getInteger() throws CVC5ApiException {
    Term int1 = d_solver.mkInteger("-18446744073709551616");
    Term int2 = d_solver.mkInteger("-18446744073709551615");
    Term int3 = d_solver.mkInteger("-4294967296");
    Term int4 = d_solver.mkInteger("-4294967295");
    Term int5 = d_solver.mkInteger("-10");
    Term int6 = d_solver.mkInteger("0");
    Term int7 = d_solver.mkInteger("10");
    Term int8 = d_solver.mkInteger("4294967295");
    Term int9 = d_solver.mkInteger("4294967296");
    Term int10 = d_solver.mkInteger("18446744073709551615");
    Term int11 = d_solver.mkInteger("18446744073709551616");
    Term int12 = d_solver.mkInteger("-0");

    assertThrows(CVC5ApiException.class, () -> d_solver.mkInteger(""));
    assertThrows(CVC5ApiException.class, () -> d_solver.mkInteger("-"));
    assertThrows(CVC5ApiException.class, () -> d_solver.mkInteger("-1-"));
    assertThrows(CVC5ApiException.class, () -> d_solver.mkInteger("0.0"));
    assertThrows(CVC5ApiException.class, () -> d_solver.mkInteger("-0.1"));
    assertThrows(CVC5ApiException.class, () -> d_solver.mkInteger("012"));
    assertThrows(CVC5ApiException.class, () -> d_solver.mkInteger("0000"));
    assertThrows(CVC5ApiException.class, () -> d_solver.mkInteger("-01"));
    assertThrows(CVC5ApiException.class, () -> d_solver.mkInteger("-00"));

    assertTrue(!int1.isInt() && !int1.isLong() && int1.isInteger());
    assertEquals(int1.getInteger(), "-18446744073709551616");
    assertTrue(!int2.isInt() && !int2.isLong() && int2.isInteger());
    assertEquals(int2.getInteger(), "-18446744073709551615");
    assertTrue(!int3.isInt() && int3.isLong() && int3.isInteger());
    assertEquals(int3.getLong(), -4294967296L);
    assertEquals(int3.getInteger(), "-4294967296");
    assertTrue(!int4.isInt() && int4.isLong() && int4.isInteger());
    assertEquals(int4.getLong(), -4294967295L);
    assertEquals(int4.getInteger(), "-4294967295");
    assertTrue(int5.isInt() && int5.isLong() && int5.isInteger());
    assertEquals(int5.getInt(), -10);
    assertEquals(int5.getLong(), -10);
    assertEquals(int5.getInteger(), "-10");
    assertTrue(int6.isInt() && int6.isLong() && int6.isInteger());
    assertEquals(int6.getInt(), 0);
    assertEquals(int6.getLong(), 0);
    assertEquals(int6.getInteger(), "0");
    assertTrue(int7.isInt() && int7.isLong() && int7.isInteger());
    assertEquals(int7.getInt(), 10);
    assertEquals(int7.getLong(), 10);
    assertEquals(int7.getInteger(), "10");
    assertTrue(!int8.isInt() && int8.isLong() && int8.isInteger());
    assertEquals(Integer.toUnsignedLong(int8.getInt()), 4294967295L);
    assertEquals(int8.getLong(), 4294967295L);
    assertEquals(int8.getInteger(), "4294967295");
    assertTrue(!int9.isInt() && int9.isLong() && int9.isInteger());
    assertEquals(int9.getLong(), 4294967296L);
    assertEquals(int9.getInteger(), "4294967296");
    assertTrue(!int10.isInt() && !int10.isLong() && int10.isInteger());

    assertEquals(Long.compareUnsigned(int10.getLong(),
                     new BigInteger("18446744073709551615").longValue()),
        0);
    assertEquals(int10.getInteger(), "18446744073709551615");
    assertTrue(!int11.isInt() && !int11.isLong() && int11.isInteger());
    assertEquals(int11.getInteger(), "18446744073709551616");
  }

  @Test
  void getString() {
    Term s1 = d_solver.mkString("abcde");
    assertTrue(s1.isString());
    assertEquals(s1.getString(), "abcde");
  }

  @Test
  void substitute() {
    Term x = d_solver.mkConst(d_solver.getIntegerSort(), "x");
    Term one = d_solver.mkInteger(1);
    Term ttrue = d_solver.mkTrue();
    Term xpx = d_solver.mkTerm(PLUS, x, x);
    Term onepone = d_solver.mkTerm(PLUS, one, one);

    assertEquals(xpx.substitute(x, one), onepone);
    assertEquals(onepone.substitute(one, x), xpx);
    // incorrect due to type
    assertThrows(CVC5ApiException.class, () -> xpx.substitute(one, ttrue));

    // simultaneous substitution
    Term y = d_solver.mkConst(d_solver.getIntegerSort(), "y");
    Term xpy = d_solver.mkTerm(PLUS, x, y);
    Term xpone = d_solver.mkTerm(PLUS, y, one);
    List<Term> es = new ArrayList<>();
    List<Term> rs = new ArrayList<>();
    es.add(x);
    rs.add(y);
    es.add(y);
    rs.add(one);
    assertEquals(xpy.substitute(es, rs), xpone);

    // incorrect substitution due to arity
    rs.remove(rs.size() - 1);
    assertThrows(CVC5ApiException.class, () -> xpy.substitute(es, rs));

    // incorrect substitution due to types
    rs.add(ttrue);
    assertThrows(CVC5ApiException.class, () -> xpy.substitute(es, rs));

    // null cannot substitute
    Term tnull = d_solver.getNullTerm();
    assertThrows(CVC5ApiException.class, () -> tnull.substitute(one, x));
    assertThrows(CVC5ApiException.class, () -> xpx.substitute(tnull, x));
    assertThrows(CVC5ApiException.class, () -> xpx.substitute(x, tnull));
    rs.remove(rs.size() - 1);
    rs.add(tnull);
    assertThrows(CVC5ApiException.class, () -> xpy.substitute(es, rs));
    es.clear();
    rs.clear();
    es.add(x);
    rs.add(y);
    assertThrows(CVC5ApiException.class, () -> tnull.substitute(es, rs));
    es.add(tnull);
    rs.add(one);
    assertThrows(CVC5ApiException.class, () -> xpx.substitute(es, rs));
  }

  @Test
  void constArray() throws CVC5ApiException {
    Sort intsort = d_solver.getIntegerSort();
    Sort arrsort = d_solver.mkArraySort(intsort, intsort);
    Term a = d_solver.mkConst(arrsort, "a");
    Term one = d_solver.mkInteger(1);
    Term constarr = d_solver.mkConstArray(arrsort, one);

    assertEquals(constarr.getKind(), CONST_ARRAY);
    assertEquals(constarr.getConstArrayBase(), one);
    assertThrows(CVC5ApiException.class, () -> a.getConstArrayBase());

    arrsort =
        d_solver.mkArraySort(d_solver.getRealSort(), d_solver.getRealSort());
    Term zero_array = d_solver.mkConstArray(arrsort, d_solver.mkReal(0));
    Term stores = d_solver.mkTerm(
        STORE, zero_array, d_solver.mkReal(1), d_solver.mkReal(2));
    stores =
        d_solver.mkTerm(STORE, stores, d_solver.mkReal(2), d_solver.mkReal(3));
    stores =
        d_solver.mkTerm(STORE, stores, d_solver.mkReal(4), d_solver.mkReal(5));
  }

  @Test
  void constSequenceElements() throws CVC5ApiException {
    Sort realsort = d_solver.getRealSort();
    Sort seqsort = d_solver.mkSequenceSort(realsort);
    Term s = d_solver.mkEmptySequence(seqsort);

    assertEquals(s.getKind(), CONST_SEQUENCE);
    // empty sequence has zero elements
    List<Term> cs = Arrays.asList(s.getConstSequenceElements());
    assertTrue(cs.isEmpty());

    // A seq.unit app is not a constant sequence (regardless of whether it is
    // applied to a constant).
    Term su = d_solver.mkTerm(SEQ_UNIT, d_solver.mkReal(1));
    assertThrows(CVC5ApiException.class, () -> su.getConstSequenceElements());
  }

  @Test
  void termScopedToString() {
    Sort intsort = d_solver.getIntegerSort();
    Term x = d_solver.mkConst(intsort, "x");
    assertEquals(x.toString(), "x");
    Solver solver2;
    assertEquals(x.toString(), "x");
  }
}
