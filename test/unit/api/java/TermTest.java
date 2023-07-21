/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Term class.
 */

package tests;
import static io.github.cvc5.Kind.*;
import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class TermTest
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
  void eq()
  {
    Sort uSort = d_solver.mkUninterpretedSort("u");
    Term x = d_solver.mkVar(uSort, "x");
    Term y = d_solver.mkVar(uSort, "y");
    Term z = new Term();

    assertTrue(x == x);
    assertFalse(x != x);
    assertFalse(x == y);
    assertTrue(x != y);
    assertFalse((x == z));
    assertTrue(x != z);
  }

  @Test
  void getId()
  {
    Term n = new Term();
    assertThrows(CVC5ApiException.class, () -> n.getId());
    Term x = d_solver.mkVar(d_solver.getIntegerSort(), "x");
    assertDoesNotThrow(() -> x.getId());
    Term y = x;
    assertEquals(x.getId(), y.getId());

    Term z = d_solver.mkVar(d_solver.getIntegerSort(), "z");
    assertNotEquals(x.getId(), z.getId());
  }

  @Test
  void getKind() throws CVC5ApiException
  {
    Sort uSort = d_solver.mkUninterpretedSort("u");
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(uSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term n = new Term();
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
    Term sum = d_solver.mkTerm(ADD, f_x, f_y);
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
  void getSort() throws CVC5ApiException
  {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term n = new Term();
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
    Term sum = d_solver.mkTerm(ADD, f_x, f_y);
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
  void getOp() throws CVC5ApiException
  {
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
    for (Term t : fx)
    {
      children.add(t);
    }

    // testing rebuild from op and children
    assertEquals(fx, d_solver.mkTerm(fx.getOp(), children.toArray(new Term[0])));

    // Test Datatypes Ops
    Sort sort = d_solver.mkParamSort("T");
    DatatypeDecl listDecl = d_solver.mkDatatypeDecl("paramlist", new Sort[] {sort});
    DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
    DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
    cons.addSelector("head", sort);
    cons.addSelectorSelf("tail");
    listDecl.addConstructor(cons);
    listDecl.addConstructor(nil);
    Sort listSort = d_solver.mkDatatypeSort(listDecl);
    Sort intListSort = listSort.instantiate(new Sort[] {d_solver.getIntegerSort()});
    Term c = d_solver.mkConst(intListSort, "c");
    Datatype list = listSort.getDatatype();
    // list datatype constructor and selector operator terms
    Term consOpTerm = list.getConstructor("cons").getTerm();
    Term nilOpTerm = list.getConstructor("nil").getTerm();
  }

  @Test
  void hasGetSymbol() throws CVC5ApiException
  {
    Term n = new Term();
    Term t = d_solver.mkBoolean(true);
    Term c = d_solver.mkConst(d_solver.getBooleanSort(), "|\\|");

    assertThrows(CVC5ApiException.class, () -> n.hasSymbol());
    assertFalse(t.hasSymbol());
    assertTrue(c.hasSymbol());

    assertThrows(CVC5ApiException.class, () -> n.getSymbol());
    assertThrows(CVC5ApiException.class, () -> t.getSymbol());
    assertEquals(c.getSymbol(), "|\\|");
  }

  @Test
  void isNull() throws CVC5ApiException
  {
    Term x = new Term();
    assertTrue(x.isNull());
    x = d_solver.mkVar(d_solver.mkBitVectorSort(4), "x");
    assertFalse(x.isNull());
  }

  @Test
  void notTerm() throws CVC5ApiException
  {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    assertThrows(CVC5ApiException.class, () -> new Term().notTerm());
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
    Term sum = d_solver.mkTerm(ADD, f_x, f_x);
    assertThrows(CVC5ApiException.class, () -> sum.notTerm());
    Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
    assertDoesNotThrow(() -> p_0.notTerm());
    Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
    assertDoesNotThrow(() -> p_f_x.notTerm());
  }

  @Test
  void andTerm() throws CVC5ApiException
  {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term b = d_solver.mkTrue();
    assertThrows(CVC5ApiException.class, () -> new Term().andTerm(b));
    assertThrows(CVC5ApiException.class, () -> b.andTerm(new Term()));
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
    Term sum = d_solver.mkTerm(ADD, f_x, f_x);
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
  void orTerm() throws CVC5ApiException
  {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term b = d_solver.mkTrue();
    assertThrows(CVC5ApiException.class, () -> new Term().orTerm(b));
    assertThrows(CVC5ApiException.class, () -> b.orTerm(new Term()));
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
    Term sum = d_solver.mkTerm(ADD, f_x, f_x);
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
  void xorTerm() throws CVC5ApiException
  {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term b = d_solver.mkTrue();
    assertThrows(CVC5ApiException.class, () -> new Term().xorTerm(b));
    assertThrows(CVC5ApiException.class, () -> b.xorTerm(new Term()));
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
    Term sum = d_solver.mkTerm(ADD, f_x, f_x);
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
  void eqTerm() throws CVC5ApiException
  {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term b = d_solver.mkTrue();
    assertThrows(CVC5ApiException.class, () -> new Term().eqTerm(b));
    assertThrows(CVC5ApiException.class, () -> b.eqTerm(new Term()));
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
    Term sum = d_solver.mkTerm(ADD, f_x, f_x);
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
  void impTerm() throws CVC5ApiException
  {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term b = d_solver.mkTrue();
    assertThrows(CVC5ApiException.class, () -> new Term().impTerm(b));
    assertThrows(CVC5ApiException.class, () -> b.impTerm(new Term()));
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
    Term sum = d_solver.mkTerm(ADD, f_x, f_x);
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
  void iteTerm() throws CVC5ApiException
  {
    Sort bvSort = d_solver.mkBitVectorSort(8);
    Sort intSort = d_solver.getIntegerSort();
    Sort boolSort = d_solver.getBooleanSort();
    Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
    Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);

    Term b = d_solver.mkTrue();
    assertThrows(CVC5ApiException.class, () -> new Term().iteTerm(b, b));
    assertThrows(CVC5ApiException.class, () -> b.iteTerm(new Term(), b));
    assertThrows(CVC5ApiException.class, () -> b.iteTerm(b, new Term()));
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
    Term sum = d_solver.mkTerm(ADD, f_x, f_x);
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
  void termAssignment()
  {
    Term t1 = d_solver.mkInteger(1);
    Term t2 = t1;
    t2 = d_solver.mkInteger(2);
    assertEquals(t1, d_solver.mkInteger(1));
  }

  @Test
  void termCompare()
  {
    Term t1 = d_solver.mkInteger(1);
    Term t2 = d_solver.mkTerm(ADD, d_solver.mkInteger(2), d_solver.mkInteger(2));
    Term t3 = d_solver.mkTerm(ADD, d_solver.mkInteger(2), d_solver.mkInteger(2));
    assertTrue(t2.compareTo(t3) >= 0);
    assertTrue(t2.compareTo(t3) <= 0);
    assertTrue((t1.compareTo(t2) > 0) != (t1.compareTo(t2) < 0));
    assertTrue((t1.compareTo(t2) > 0 || t1.equals(t2)) == (t1.compareTo(t2) >= 0));
  }

  @Test
  void termChildren() throws CVC5ApiException
  {
    // simple term 2+3
    Term two = d_solver.mkInteger(2);
    Term t1 = d_solver.mkTerm(ADD, two, d_solver.mkInteger(3));
    assertEquals(t1.getChild(0), two);
    assertEquals(t1.getNumChildren(), 2);
    Term tnull = new Term();
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
  void getIntegerValue() throws CVC5ApiException
  {
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

    assertTrue(int1.isIntegerValue());
    assertEquals(int1.getIntegerValue().toString(), "-18446744073709551616");
    assertEquals(int1.getRealOrIntegerValueSign(), -1);
    assertTrue(int2.isIntegerValue());
    assertEquals(int2.getIntegerValue().toString(), "-18446744073709551615");
    assertTrue(int3.isIntegerValue());
    assertEquals(int3.getIntegerValue().longValue(), -4294967296L);
    assertEquals(int3.getIntegerValue().toString(), "-4294967296");
    assertTrue(int4.isIntegerValue());
    assertEquals(int4.getIntegerValue().longValue(), -4294967295L);
    assertEquals(int4.getIntegerValue().toString(), "-4294967295");
    assertTrue(int5.isIntegerValue());
    assertEquals(int5.getIntegerValue().intValue(), -10);
    assertEquals(int5.getIntegerValue().intValue(), -10);
    assertEquals(int5.getIntegerValue().toString(), "-10");
    assertTrue(int6.isIntegerValue());
    assertEquals(int6.getIntegerValue().intValue(), 0);
    assertEquals(int6.getIntegerValue().intValue(), 0);
    assertEquals(int6.getIntegerValue().toString(), "0");
    assertEquals(int6.getRealOrIntegerValueSign(), 0);
    assertTrue(int7.isIntegerValue());
    assertEquals(int7.getIntegerValue().intValue(), 10);
    assertEquals(int7.getIntegerValue().intValue(), 10);
    assertEquals(int7.getIntegerValue().toString(), "10");
    assertEquals(int7.getRealOrIntegerValueSign(), 1);
    assertTrue(int8.isIntegerValue());
    assertEquals(int8.getIntegerValue().longValue(), 4294967295L);
    assertEquals(int8.getIntegerValue().toString(), "4294967295");
    assertTrue(int9.isIntegerValue());
    assertEquals(int9.getIntegerValue().longValue(), 4294967296L);
    assertEquals(int9.getIntegerValue().toString(), "4294967296");
    assertTrue(int10.isIntegerValue());

    assertEquals(int10.getIntegerValue().toString(), "18446744073709551615");
    assertTrue(int11.isIntegerValue());
    assertEquals(int11.getIntegerValue().toString(), "18446744073709551616");
  }

  @Test
  void getString()
  {
    Term s1 = d_solver.mkString("abcde");
    assertTrue(s1.isStringValue());
    assertEquals(s1.getStringValue(), "abcde");
  }

  @Test
  void getReal() throws CVC5ApiException
  {
    Term real1 = d_solver.mkReal("0");
    Term real2 = d_solver.mkReal(".0");
    Term real3 = d_solver.mkReal("-17");
    Term real4 = d_solver.mkReal("-3/5");
    Term real5 = d_solver.mkReal("12.7");
    Term real6 = d_solver.mkReal("1/4294967297");
    Term real7 = d_solver.mkReal("4294967297");
    Term real8 = d_solver.mkReal("1/18446744073709551617");
    Term real9 = d_solver.mkReal("18446744073709551617");
    Term real10 = d_solver.mkReal("2343.2343");

    assertTrue(real1.isRealValue());
    assertTrue(real2.isRealValue());
    assertTrue(real3.isRealValue());
    assertTrue(real4.isRealValue());
    assertTrue(real5.isRealValue());
    assertTrue(real6.isRealValue());
    assertTrue(real7.isRealValue());
    assertTrue(real8.isRealValue());
    assertTrue(real9.isRealValue());
    assertTrue(real10.isRealValue());

    assertEquals("0/1", Utils.getRational(real1.getRealValue()));
    assertEquals("0/1", Utils.getRational(real2.getRealValue()));
    assertEquals("-17/1", Utils.getRational(real3.getRealValue()));
    assertEquals("-3/5", Utils.getRational(real4.getRealValue()));
    assertEquals("127/10", Utils.getRational(real5.getRealValue()));
    assertEquals("1/4294967297", Utils.getRational(real6.getRealValue()));
    assertEquals("4294967297/1", Utils.getRational(real7.getRealValue()));
    assertEquals("1/18446744073709551617", Utils.getRational(real8.getRealValue()));
    assertEquals("18446744073709551617/1", Utils.getRational(real9.getRealValue()));
    assertEquals("23432343/10000", Utils.getRational(real10.getRealValue()));
  }

  @Test
  void getConstArrayBase()
  {
    Sort intsort = d_solver.getIntegerSort();
    Sort arrsort = d_solver.mkArraySort(intsort, intsort);
    Term one = d_solver.mkInteger(1);
    Term constarr = d_solver.mkConstArray(arrsort, one);

    assertTrue(constarr.isConstArray());
    assertEquals(one, constarr.getConstArrayBase());

    Term a = d_solver.mkConst(arrsort, "a");
    assertThrows(CVC5ApiException.class, () -> a.getConstArrayBase());
    assertThrows(CVC5ApiException.class, () -> one.getConstArrayBase());
  }

  @Test
  void getBoolean()
  {
    Term b1 = d_solver.mkBoolean(true);
    Term b2 = d_solver.mkBoolean(false);

    assertTrue(b1.isBooleanValue());
    assertTrue(b2.isBooleanValue());
    assertTrue(b1.getBooleanValue());
    assertFalse(b2.getBooleanValue());
  }

  @Test
  void getBitVector() throws CVC5ApiException
  {
    Term b1 = d_solver.mkBitVector(8, 15);
    Term b2 = d_solver.mkBitVector(8, "00001111", 2);
    Term b3 = d_solver.mkBitVector(8, "15", 10);
    Term b4 = d_solver.mkBitVector(8, "0f", 16);
    Term b5 = d_solver.mkBitVector(9, "00001111", 2);
    Term b6 = d_solver.mkBitVector(9, "15", 10);
    Term b7 = d_solver.mkBitVector(9, "0f", 16);

    assertTrue(b1.isBitVectorValue());
    assertTrue(b2.isBitVectorValue());
    assertTrue(b3.isBitVectorValue());
    assertTrue(b4.isBitVectorValue());
    assertTrue(b5.isBitVectorValue());
    assertTrue(b6.isBitVectorValue());
    assertTrue(b7.isBitVectorValue());

    assertEquals("00001111", b1.getBitVectorValue(2));
    assertEquals("15", b1.getBitVectorValue(10));
    assertEquals("f", b1.getBitVectorValue(16));
    assertEquals("00001111", b2.getBitVectorValue(2));
    assertEquals("15", b2.getBitVectorValue(10));
    assertEquals("f", b2.getBitVectorValue(16));
    assertEquals("00001111", b3.getBitVectorValue(2));
    assertEquals("15", b3.getBitVectorValue(10));
    assertEquals("f", b3.getBitVectorValue(16));
    assertEquals("00001111", b4.getBitVectorValue(2));
    assertEquals("15", b4.getBitVectorValue(10));
    assertEquals("f", b4.getBitVectorValue(16));
    assertEquals("000001111", b5.getBitVectorValue(2));
    assertEquals("15", b5.getBitVectorValue(10));
    assertEquals("f", b5.getBitVectorValue(16));
    assertEquals("000001111", b6.getBitVectorValue(2));
    assertEquals("15", b6.getBitVectorValue(10));
    assertEquals("f", b6.getBitVectorValue(16));
    assertEquals("000001111", b7.getBitVectorValue(2));
    assertEquals("15", b7.getBitVectorValue(10));
    assertEquals("f", b7.getBitVectorValue(16));
  }

  @Test
  void getUninterpretedSortValue() throws CVC5ApiException
  {
    d_solver.setOption("produce-models", "true");
    Sort uSort = d_solver.mkUninterpretedSort("u");
    Term x = d_solver.mkConst(uSort, "x");
    Term y = d_solver.mkConst(uSort, "y");
    d_solver.assertFormula(d_solver.mkTerm(EQUAL, x, y));
    assertTrue(d_solver.checkSat().isSat());
    Term vx = d_solver.getValue(x);
    Term vy = d_solver.getValue(y);
    assertEquals(vx.isUninterpretedSortValue(), vy.isUninterpretedSortValue());
    assertDoesNotThrow(() -> vx.getUninterpretedSortValue());
    assertDoesNotThrow(() -> vy.getUninterpretedSortValue());
  }

  @Test
  void isRoundingModeValue() throws CVC5ApiException
  {
    assertFalse(d_solver.mkInteger(15).isRoundingModeValue());
    assertTrue(
        d_solver.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_EVEN).isRoundingModeValue());
    assertFalse(d_solver.mkConst(d_solver.getRoundingModeSort()).isRoundingModeValue());
  }

  @Test
  void getRoundingModeValue() throws CVC5ApiException
  {
    assertThrows(CVC5ApiException.class, () -> d_solver.mkInteger(15).getRoundingModeValue());
    assertEquals(
        d_solver.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_EVEN).getRoundingModeValue(),
        RoundingMode.ROUND_NEAREST_TIES_TO_EVEN);
    assertEquals(d_solver.mkRoundingMode(RoundingMode.ROUND_TOWARD_POSITIVE).getRoundingModeValue(),
        RoundingMode.ROUND_TOWARD_POSITIVE);
    assertEquals(d_solver.mkRoundingMode(RoundingMode.ROUND_TOWARD_NEGATIVE).getRoundingModeValue(),
        RoundingMode.ROUND_TOWARD_NEGATIVE);
    assertEquals(d_solver.mkRoundingMode(RoundingMode.ROUND_TOWARD_ZERO).getRoundingModeValue(),
        RoundingMode.ROUND_TOWARD_ZERO);
    assertEquals(
        d_solver.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_AWAY).getRoundingModeValue(),
        RoundingMode.ROUND_NEAREST_TIES_TO_AWAY);
  }

  @Test
  void getTuple()
  {
    Term t1 = d_solver.mkInteger(15);
    Term t2 = d_solver.mkReal(17, 25);
    Term t3 = d_solver.mkString("abc");

    Term tup = d_solver.mkTuple(new Term[] {t1, t2, t3});

    assertTrue(tup.isTupleValue());
    assertEquals(Arrays.asList((new Term[] {t1, t2, t3})), Arrays.asList(tup.getTupleValue()));
  }

  @Test
  void getFloatingPoint() throws CVC5ApiException
  {
    Term bvval = d_solver.mkBitVector(16, "0000110000000011", 2);
    Term fp = d_solver.mkFloatingPoint(5, 11, bvval);

    assertTrue(fp.isFloatingPointValue());
    assertFalse(fp.isFloatingPointPosZero());
    assertFalse(fp.isFloatingPointNegZero());
    assertFalse(fp.isFloatingPointPosInf());
    assertFalse(fp.isFloatingPointNegInf());
    assertFalse(fp.isFloatingPointNaN());
    assertEquals(new Triplet<Long, Long, Term>(5L, 11L, bvval), fp.getFloatingPointValue());

    assertTrue(d_solver.mkFloatingPointPosZero(5, 11).isFloatingPointPosZero());
    assertTrue(d_solver.mkFloatingPointNegZero(5, 11).isFloatingPointNegZero());
    assertTrue(d_solver.mkFloatingPointPosInf(5, 11).isFloatingPointPosInf());
    assertTrue(d_solver.mkFloatingPointNegInf(5, 11).isFloatingPointNegInf());
    assertTrue(d_solver.mkFloatingPointNaN(5, 11).isFloatingPointNaN());
  }

  @Test
  void getSet()
  {
    Sort s = d_solver.mkSetSort(d_solver.getIntegerSort());

    Term i1 = d_solver.mkInteger(5);
    Term i2 = d_solver.mkInteger(7);

    Term s1 = d_solver.mkEmptySet(s);
    Term s2 = d_solver.mkTerm(Kind.SET_SINGLETON, i1);
    Term s3 = d_solver.mkTerm(Kind.SET_SINGLETON, i1);
    Term s4 = d_solver.mkTerm(Kind.SET_SINGLETON, i2);
    Term s5 = d_solver.mkTerm(Kind.SET_UNION, s2, d_solver.mkTerm(Kind.SET_UNION, s3, s4));

    assertTrue(s1.isSetValue());
    assertTrue(s2.isSetValue());
    assertTrue(s3.isSetValue());
    assertTrue(s4.isSetValue());
    assertFalse(s5.isSetValue());
    s5 = d_solver.simplify(s5);
    assertTrue(s5.isSetValue());

    assertSetsEquality(new Term[] {}, s1.getSetValue());
    assertSetsEquality(new Term[] {i1}, s2.getSetValue());
    assertSetsEquality(new Term[] {i1}, s3.getSetValue());
    assertSetsEquality(new Term[] {i2}, s4.getSetValue());
    assertSetsEquality(new Term[] {i1, i2}, s5.getSetValue());
  }

  private void assertSetsEquality(Term[] A, Set<Term> B)
  {
    List<Term> a = Arrays.stream(A).sorted().collect(Collectors.toList());
    List<Term> b = B.stream().sorted().collect(Collectors.toList());
    assertEquals(a, b);
  }

  @Test
  void getSequence()
  {
    Sort s = d_solver.mkSequenceSort(d_solver.getIntegerSort());

    Term i1 = d_solver.mkInteger(5);
    Term i2 = d_solver.mkInteger(7);

    Term s1 = d_solver.mkEmptySequence(s);
    Term s2 = d_solver.mkTerm(Kind.SEQ_UNIT, i1);
    Term s3 = d_solver.mkTerm(Kind.SEQ_UNIT, i1);
    Term s4 = d_solver.mkTerm(Kind.SEQ_UNIT, i2);
    Term s5 = d_solver.mkTerm(Kind.SEQ_CONCAT, s2, d_solver.mkTerm(Kind.SEQ_CONCAT, s3, s4));

    assertTrue(s1.isSequenceValue());
    assertTrue(!s2.isSequenceValue());
    assertTrue(!s3.isSequenceValue());
    assertTrue(!s4.isSequenceValue());
    assertTrue(!s5.isSequenceValue());

    s2 = d_solver.simplify(s2);
    s3 = d_solver.simplify(s3);
    s4 = d_solver.simplify(s4);
    s5 = d_solver.simplify(s5);

    assertEquals(Arrays.asList(new Term[] {}), Arrays.asList(s1.getSequenceValue()));
    assertEquals(Arrays.asList(new Term[] {i1}), Arrays.asList(s2.getSequenceValue()));
    assertEquals(Arrays.asList(new Term[] {i1}), Arrays.asList(s3.getSequenceValue()));
    assertEquals(Arrays.asList(new Term[] {i2}), Arrays.asList(s4.getSequenceValue()));
    assertEquals(Arrays.asList(new Term[] {i1, i1, i2}), Arrays.asList(s5.getSequenceValue()));
  }

  @Test
  void getCardinalityConstraint() throws CVC5ApiException
  {
    Sort su = d_solver.mkUninterpretedSort("u");
    Term t = d_solver.mkCardinalityConstraint(su, 3);
    assertTrue(t.isCardinalityConstraint());
    Pair<Sort, BigInteger> cc = t.getCardinalityConstraint();
    assertEquals(cc.first, su);
    assertEquals(cc.second, new BigInteger("3"));
    Term x = d_solver.mkConst(d_solver.getIntegerSort(), "x");
    assertFalse(x.isCardinalityConstraint());
    assertThrows(CVC5ApiException.class, () -> x.getCardinalityConstraint());
    Term nullt = new Term();
    assertThrows(CVC5ApiException.class, () -> nullt.isCardinalityConstraint());
  }

  @Test
  void getRealAlgebraicNumber() throws CVC5ApiException
  {
    d_solver.setOption("produce-models", "true");
    d_solver.setLogic("QF_NRA");
    Sort realsort = d_solver.getRealSort();
    Term x = d_solver.mkConst(realsort, "x");
    Term x2 = d_solver.mkTerm(MULT, x, x);
    Term two = d_solver.mkReal(2, 1);
    Term eq = d_solver.mkTerm(EQUAL, x2, two);
    d_solver.assertFormula(eq);
    // Note that check-sat should only return "sat" if libpoly is enabled.
    // Otherwise, we do not test the following functionality.
    if (d_solver.checkSat().isSat())
    {
      // We find a model for (x*x = 2), where x should be a real algebraic number.
      // We assert that its defining polynomial is non-null and its lower and
      // upper bounds are real.
      Term vx = d_solver.getValue(x);
      assertTrue(vx.isRealAlgebraicNumber());
      Term y = d_solver.mkVar(realsort, "y");
      Term poly = vx.getRealAlgebraicNumberDefiningPolynomial(y);
      assertTrue(!poly.isNull());
      Term lb = vx.getRealAlgebraicNumberLowerBound();
      assertTrue(lb.isRealValue());
      Term ub = vx.getRealAlgebraicNumberUpperBound();
      assertTrue(ub.isRealValue());
    }
  }

  @Test
  void substitute()
  {
    Term x = d_solver.mkConst(d_solver.getIntegerSort(), "x");
    Term one = d_solver.mkInteger(1);
    Term ttrue = d_solver.mkTrue();
    Term xpx = d_solver.mkTerm(ADD, x, x);
    Term onepone = d_solver.mkTerm(ADD, one, one);

    assertEquals(xpx.substitute(x, one), onepone);
    assertEquals(onepone.substitute(one, x), xpx);
    // incorrect due to type
    assertThrows(CVC5ApiException.class, () -> xpx.substitute(one, ttrue));

    // simultaneous substitution
    Term y = d_solver.mkConst(d_solver.getIntegerSort(), "y");
    Term xpy = d_solver.mkTerm(ADD, x, y);
    Term xpone = d_solver.mkTerm(ADD, y, one);
    List<Term> es = new ArrayList<>();
    List<Term> rs = new ArrayList<>();
    es.add(x);
    rs.add(y);
    es.add(y);
    rs.add(one);
    assertEquals(xpy.substitute(es.toArray(new Term[0]), rs.toArray(new Term[0])), xpone);

    // incorrect substitution due to arity
    rs.remove(rs.size() - 1);
    assertThrows(CVC5ApiException.class,
        () -> xpy.substitute(es.toArray(new Term[0]), rs.toArray(new Term[0])));

    // incorrect substitution due to types
    rs.add(ttrue);
    assertThrows(CVC5ApiException.class,
        () -> xpy.substitute(es.toArray(new Term[0]), rs.toArray(new Term[0])));

    // null cannot substitute
    Term tnull = new Term();
    assertThrows(CVC5ApiException.class, () -> tnull.substitute(one, x));
    assertThrows(CVC5ApiException.class, () -> xpx.substitute(tnull, x));
    assertThrows(CVC5ApiException.class, () -> xpx.substitute(x, tnull));
    rs.remove(rs.size() - 1);
    rs.add(tnull);
    assertThrows(CVC5ApiException.class,
        () -> xpy.substitute(es.toArray(new Term[0]), rs.toArray(new Term[0])));
    es.clear();
    rs.clear();
    es.add(x);
    rs.add(y);
    assertThrows(CVC5ApiException.class,
        () -> tnull.substitute(es.toArray(new Term[0]), rs.toArray(new Term[0])));
    es.add(tnull);
    rs.add(one);
    assertThrows(CVC5ApiException.class,
        () -> xpx.substitute(es.toArray(new Term[0]), rs.toArray(new Term[0])));
  }

  @Test
  void constArray() throws CVC5ApiException
  {
    Sort intsort = d_solver.getIntegerSort();
    Sort arrsort = d_solver.mkArraySort(intsort, intsort);
    Term a = d_solver.mkConst(arrsort, "a");
    Term one = d_solver.mkInteger(1);
    Term two = d_solver.mkBitVector(2, 2);
    Term iconst = d_solver.mkConst(intsort);
    Term constarr = d_solver.mkConstArray(arrsort, one);

    assertThrows(CVC5ApiException.class, () -> d_solver.mkConstArray(arrsort, two));
    assertThrows(CVC5ApiException.class, () -> d_solver.mkConstArray(arrsort, iconst));

    assertEquals(constarr.getKind(), CONST_ARRAY);
    assertEquals(constarr.getConstArrayBase(), one);
    assertThrows(CVC5ApiException.class, () -> a.getConstArrayBase());

    Sort arrsort2 = d_solver.mkArraySort(d_solver.getRealSort(), d_solver.getRealSort());
    Term zero_array = d_solver.mkConstArray(arrsort2, d_solver.mkReal(0));
    Term stores = d_solver.mkTerm(STORE, zero_array, d_solver.mkReal(1), d_solver.mkReal(2));
    stores = d_solver.mkTerm(STORE, stores, d_solver.mkReal(2), d_solver.mkReal(3));
    stores = d_solver.mkTerm(STORE, stores, d_solver.mkReal(4), d_solver.mkReal(5));
  }

  @Test
  void getSequenceValue() throws CVC5ApiException
  {
    Sort realsort = d_solver.getRealSort();
    Sort seqsort = d_solver.mkSequenceSort(realsort);
    Term s = d_solver.mkEmptySequence(seqsort);

    assertEquals(s.getKind(), CONST_SEQUENCE);
    // empty sequence has zero elements
    Term[] cs = s.getSequenceValue();
    assertTrue(cs.length == 0);

    // A seq.unit app is not a constant sequence (regardless of whether it is
    // applied to a constant).
    Term su = d_solver.mkTerm(SEQ_UNIT, d_solver.mkReal(1));
    assertThrows(CVC5ApiException.class, () -> su.getSequenceValue());
  }

  @Test
  void termScopedToString()
  {
    Sort intsort = d_solver.getIntegerSort();
    Term x = d_solver.mkConst(intsort, "x");
    assertEquals(x.toString(), "x");
    Solver solver2;
    assertEquals(x.toString(), "x");
  }
}
