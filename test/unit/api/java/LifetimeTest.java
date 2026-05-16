/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the lifetime guarantees of the Java API.
 *
 * The native objects underlying Java wrappers (Sort, Term, Op, Datatype,
 * Grammar, Proof, ...) keep the internal node manager alive while they are in
 * use. We exercise this deterministically by explicitly freeing the native
 * term manager (and solver) via deletePointer() rather than relying on the
 * garbage collector, then continuing to use objects derived from them.
 *
 * Mirrors test/unit/api/cpp/api_lifetime_black.cpp.
 */

package tests;

import static io.github.cvc5.Kind.*;
import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

class LifetimeTest
{
  @AfterEach
  void tearDown()
  {
    Context.deletePointers();
  }

  @Test
  void sortOutlivesTermManager()
  {
    TermManager tm = new TermManager();
    Sort s = tm.getIntegerSort();
    Sort arr = tm.mkArraySort(s, tm.getBooleanSort());
    // Deterministically free the native term manager.
    tm.deletePointer();
    assertTrue(s.isInteger());
    assertTrue(arr.isArray());
    assertEquals(s, arr.getArrayIndexSort());
    assertDoesNotThrow(() -> s.toString());
  }

  @Test
  void termOutlivesTermManager() throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Sort intSort = tm.getIntegerSort();
    Term x = tm.mkConst(intSort, "x");
    Term t = tm.mkTerm(ADD, x, tm.mkInteger(1));
    tm.deletePointer();
    assertEquals(ADD, t.getKind());
    assertEquals(intSort, t.getSort());
    assertEquals(2, t.getNumChildren());
    assertDoesNotThrow(() -> t.toString());
  }

  @Test
  void opOutlivesTermManager() throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Op op = tm.mkOp(BITVECTOR_EXTRACT, 4, 0);
    tm.deletePointer();
    assertTrue(op.isIndexed());
    assertEquals(BITVECTOR_EXTRACT, op.getKind());
    assertEquals(2, op.getNumIndices());
    assertDoesNotThrow(() -> op.get(0));
    assertDoesNotThrow(() -> op.toString());
  }

  @Test
  void termIteratorOutlivesTermManager()
  {
    TermManager tm = new TermManager();
    Sort b = tm.getBooleanSort();
    Term t = tm.mkTerm(AND, tm.mkConst(b, "x"), tm.mkConst(b, "y"));
    // Iterating over t (which constructs term iterators) must still be safe.
    tm.deletePointer();
    int count = 0;
    for (Term child : t)
    {
      assertFalse(child.isNull());
      count++;
    }
    assertEquals(2, count);
  }

  @Test
  void datatypeOutlivesTermManager() throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    DatatypeDecl decl = tm.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = tm.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", tm.getIntegerSort());
    cons.addSelectorSelf("tail");
    decl.addConstructor(cons);
    DatatypeConstructorDecl nil = tm.mkDatatypeConstructorDecl("nil");
    decl.addConstructor(nil);
    Sort listSort = tm.mkDatatypeSort(decl);
    // The datatype, its constructors and selectors (and their iterators)
    // must still be usable after the term manager is gone.
    tm.deletePointer();
    Datatype dt = listSort.getDatatype();
    assertEquals("list", dt.getName());
    assertEquals(2, dt.getNumConstructors());

    int numCtors = 0;
    for (DatatypeConstructor ctor : dt)
    {
      assertFalse(ctor.getName().isEmpty());
      for (DatatypeSelector sel : ctor)
      {
        assertFalse(sel.getName().isEmpty());
      }
      numCtors++;
    }
    assertEquals(2, numCtors);

    DatatypeConstructor consCtor = dt.getConstructor("cons");
    assertEquals("cons", consCtor.getName());
    DatatypeSelector head = consCtor.getSelector("head");
    assertEquals("head", head.getName());
    assertTrue(head.getCodomainSort().isInteger());
  }

  @Test
  void solverOutlivesTermManager() throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    // Free the native term manager while the solver is still in use. The
    // solver keeps its own (shared) reference to the node manager.
    tm.deletePointer();
    TermManager tm2 = solver.getTermManager();
    Term x = tm2.mkConst(tm2.getBooleanSort(), "x");
    solver.assertFormula(x);
    assertTrue(solver.checkSat().isSat());
  }

  @Test
  void valueOutlivesSolverAndTermManager() throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    solver.setOption("produce-models", "true");
    Sort intSort = tm.getIntegerSort();
    Term x = tm.mkConst(intSort, "x");
    solver.assertFormula(tm.mkTerm(GT, x, tm.mkInteger(0)));
    assertTrue(solver.checkSat().isSat());
    Term value = solver.getValue(x);
    // Deterministically free the native solver and term manager.
    solver.deletePointer();
    tm.deletePointer();
    assertFalse(value.isNull());
    assertTrue(value.getSort().isInteger());
    assertDoesNotThrow(() -> value.toString());
  }

  @Test
  void grammarOutlivesSolverAndTermManager() throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    solver.setOption("sygus", "true");
    Sort b = tm.getBooleanSort();
    Term start = tm.mkVar(b);
    Grammar g = solver.mkGrammar(new Term[] {}, new Term[] {start});
    g.addRule(start, tm.mkBoolean(false));
    solver.deletePointer();
    tm.deletePointer();
    assertNotEquals("", g.toString());
  }

  @Test
  void proofOutlivesSolverAndTermManager() throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    solver.setOption("produce-proofs", "true");
    Sort b = tm.getBooleanSort();
    Term x = tm.mkConst(b, "x");
    solver.assertFormula(x);
    solver.assertFormula(x.notTerm());
    assertFalse(solver.checkSat().isSat());
    Proof proof = solver.getProof()[0];
    // Deterministically free the native solver and term manager.
    solver.deletePointer();
    tm.deletePointer();
    assertDoesNotThrow(() -> proof.getRule());
    assertDoesNotThrow(() -> proof.getResult());
    assertDoesNotThrow(() -> proof.getChildren());
  }
}
