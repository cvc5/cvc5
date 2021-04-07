package cvc5;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class TermTest
{
  private Solver d_solver;

  @BeforeEach void setUp()
  {
    d_solver = new Solver();
  }

  @AfterEach void tearDown()
  {
    // d_solver.deletePointer();
  }

  @Test void eq()
  {
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

    @Test void  getId()
    {
      Term n = d_solver.getNullTerm();
      assertThrows(CVC5ApiException.class, () -> n.getId());
      Term x = d_solver.mkVar(d_solver.getIntegerSort(), "x");
      assertDoesNotThrow(() -> x.getId());
      Term y = x;
      assertEquals(x.getId(), y.getId());

      Term z = d_solver.mkVar(d_solver.getIntegerSort(), "z");
      assertNotEquals(x.getId(), z.getId());
    }

//    @Test void  getKind)
//    {
//      Sort uSort = d_solver.mkUninterpretedSort("u");
//      Sort intSort = d_solver.getIntegerSort();
//      Sort boolSort = d_solver.getBooleanSort();
//      Sort funSort1 = d_solver.mkFunctionSort(uSort, intSort);
//      Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);
//
//      Term n;
//      assertThrows(n.getKind(), CVC4ApiException);
//      Term x = d_solver.mkVar(uSort, "x");
//      assertDoesNotThrow(() -> x.getKind());
//      Term y = d_solver.mkVar(uSort, "y");
//      assertDoesNotThrow(() -> y.getKind());
//
//      Term f = d_solver.mkVar(funSort1, "f");
//      assertDoesNotThrow(() -> f.getKind());
//      Term p = d_solver.mkVar(funSort2, "p");
//      assertDoesNotThrow(() -> p.getKind());
//
//      Term zero = d_solver.mkInteger(0);
//      assertDoesNotThrow(() -> zero.getKind());
//
//      Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
//      assertDoesNotThrow(() -> f_x.getKind());
//      Term f_y = d_solver.mkTerm(APPLY_UF, f, y);
//      assertDoesNotThrow(() -> f_y.getKind());
//      Term sum = d_solver.mkTerm(PLUS, f_x, f_y);
//      assertDoesNotThrow(() -> sum.getKind());
//      Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
//      assertDoesNotThrow(() -> p_0.getKind());
//      Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
//      assertDoesNotThrow(() -> p_f_y.getKind());
//
//      // Sequence kinds do not exist internally, test that the API properly
//      // converts them back.
//      Sort seqSort = d_solver.mkSequenceSort(intSort);
//      Term s = d_solver.mkConst(seqSort, "s");
//      Term ss = d_solver.mkTerm(SEQ_CONCAT, s, s);
//      assertEquals(ss.getKind(), SEQ_CONCAT);
//    }
//
//    @Test void  getSort)
//    {
//      Sort bvSort = d_solver.mkBitVectorSort(8);
//      Sort intSort = d_solver.getIntegerSort();
//      Sort boolSort = d_solver.getBooleanSort();
//      Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
//      Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);
//
//      Term n;
//      assertThrows(n.getSort(), CVC4ApiException);
//      Term x = d_solver.mkVar(bvSort, "x");
//      assertDoesNotThrow(() -> x.getSort());
//      assertEquals(x.getSort(), bvSort);
//      Term y = d_solver.mkVar(bvSort, "y");
//      assertDoesNotThrow(() -> y.getSort());
//      assertEquals(y.getSort(), bvSort);
//
//      Term f = d_solver.mkVar(funSort1, "f");
//      assertDoesNotThrow(() -> f.getSort());
//      assertEquals(f.getSort(), funSort1);
//      Term p = d_solver.mkVar(funSort2, "p");
//      assertDoesNotThrow(() -> p.getSort());
//      assertEquals(p.getSort(), funSort2);
//
//      Term zero = d_solver.mkInteger(0);
//      assertDoesNotThrow(() -> zero.getSort());
//      assertEquals(zero.getSort(), intSort);
//
//      Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
//      assertDoesNotThrow(() -> f_x.getSort());
//      assertEquals(f_x.getSort(), intSort);
//      Term f_y = d_solver.mkTerm(APPLY_UF, f, y);
//      assertDoesNotThrow(() -> f_y.getSort());
//      assertEquals(f_y.getSort(), intSort);
//      Term sum = d_solver.mkTerm(PLUS, f_x, f_y);
//      assertDoesNotThrow(() -> sum.getSort());
//      assertEquals(sum.getSort(), intSort);
//      Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
//      assertDoesNotThrow(() -> p_0.getSort());
//      assertEquals(p_0.getSort(), boolSort);
//      Term p_f_y = d_solver.mkTerm(APPLY_UF, p, f_y);
//      assertDoesNotThrow(() -> p_f_y.getSort());
//      assertEquals(p_f_y.getSort(), boolSort);
//    }
//
//    @Test void  getOp)
//    {
//      Sort intsort = d_solver.getIntegerSort();
//      Sort bvsort = d_solver.mkBitVectorSort(8);
//      Sort arrsort = d_solver.mkArraySort(bvsort, intsort);
//      Sort funsort = d_solver.mkFunctionSort(intsort, bvsort);
//
//      Term x = d_solver.mkConst(intsort, "x");
//      Term a = d_solver.mkConst(arrsort, "a");
//      Term b = d_solver.mkConst(bvsort, "b");
//
//      assertFalse(x.hasOp());
//      assertThrows(x.getOp(), CVC4ApiException);
//
//      Term ab = d_solver.mkTerm(SELECT, a, b);
//      Op ext = d_solver.mkOp(BITVECTOR_EXTRACT, 4, 0);
//      Term extb = d_solver.mkTerm(ext, b);
//
//      assertTrue(ab.hasOp());
//      assertFalse(ab.getOp().isIndexed());
//      // can compare directly to a Kind (will invoke Op constructor)
//      assertTrue(extb.hasOp());
//      assertTrue(extb.getOp().isIndexed());
//      assertEquals(extb.getOp(), ext);
//
//      Term f = d_solver.mkConst(funsort, "f");
//      Term fx = d_solver.mkTerm(APPLY_UF, f, x);
//
//      assertFalse(f.hasOp());
//      assertThrows(f.getOp(), CVC4ApiException);
//      assertTrue(fx.hasOp());
//      std::vector<Term> children(fx.begin(), fx.end());
//      // testing rebuild from op and children
//      assertEquals(fx, d_solver.mkTerm(fx.getOp(), children));
//
//      // Test Datatypes Ops
//      Sort sort = d_solver.mkParamSort("T");
//      DatatypeDecl listDecl = d_solver.mkDatatypeDecl("paramlist", sort);
//      DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
//      DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
//      cons.addSelector("head", sort);
//      cons.addSelectorSelf("tail");
//      listDecl.addConstructor(cons);
//      listDecl.addConstructor(nil);
//      Sort listSort = d_solver.mkDatatypeSort(listDecl);
//      Sort intListSort = listSort.instantiate(std::vector<Sort>{d_solver.getIntegerSort()});
//      Term c = d_solver.mkConst(intListSort, "c");
//      Datatype list = listSort.getDatatype();
//      // list datatype constructor and selector operator terms
//      Term consOpTerm = list.getConstructorTerm("cons");
//      Term nilOpTerm = list.getConstructorTerm("nil");
//      Term headOpTerm = list["cons"].getSelectorTerm("head");
//      Term tailOpTerm = list["cons"].getSelectorTerm("tail");
//
//      Term nilTerm = d_solver.mkTerm(APPLY_CONSTRUCTOR, nilOpTerm);
//      Term consTerm =
//          d_solver.mkTerm(APPLY_CONSTRUCTOR, consOpTerm, d_solver.mkInteger(0), nilTerm);
//      Term headTerm = d_solver.mkTerm(APPLY_SELECTOR, headOpTerm, consTerm);
//      Term tailTerm = d_solver.mkTerm(APPLY_SELECTOR, tailOpTerm, consTerm);
//
//      assertTrue(nilTerm.hasOp());
//      assertTrue(consTerm.hasOp());
//      assertTrue(headTerm.hasOp());
//      assertTrue(tailTerm.hasOp());
//
//      // Test rebuilding
//      children.clear();
//      children.insert(children.begin(), headTerm.begin(), headTerm.end());
//      assertEquals(headTerm, d_solver.mkTerm(headTerm.getOp(), children));
//    }
//
//    @Test void  isNull)
//    {
//      Term x;
//      assertTrue(x.isNull());
//      x = d_solver.mkVar(d_solver.mkBitVectorSort(4), "x");
//      assertFalse(x.isNull());
//    }
//
//    @Test void  notTerm)
//    {
//      Sort bvSort = d_solver.mkBitVectorSort(8);
//      Sort intSort = d_solver.getIntegerSort();
//      Sort boolSort = d_solver.getBooleanSort();
//      Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
//      Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);
//
//      assertThrows(Term().notTerm(), CVC4ApiException);
//      Term b = d_solver.mkTrue();
//      assertDoesNotThrow(() -> b.notTerm());
//      Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
//      assertThrows(x.notTerm(), CVC4ApiException);
//      Term f = d_solver.mkVar(funSort1, "f");
//      assertThrows(f.notTerm(), CVC4ApiException);
//      Term p = d_solver.mkVar(funSort2, "p");
//      assertThrows(p.notTerm(), CVC4ApiException);
//      Term zero = d_solver.mkInteger(0);
//      assertThrows(zero.notTerm(), CVC4ApiException);
//      Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
//      assertThrows(f_x.notTerm(), CVC4ApiException);
//      Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
//      assertThrows(sum.notTerm(), CVC4ApiException);
//      Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
//      assertDoesNotThrow(() -> p_0.notTerm());
//      Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
//      assertDoesNotThrow(() -> p_f_x.notTerm());
//    }
//
//    @Test void  andTerm)
//    {
//      Sort bvSort = d_solver.mkBitVectorSort(8);
//      Sort intSort = d_solver.getIntegerSort();
//      Sort boolSort = d_solver.getBooleanSort();
//      Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
//      Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);
//
//      Term b = d_solver.mkTrue();
//      assertThrows(Term().andTerm(b), CVC4ApiException);
//      assertThrows(b.andTerm(Term()), CVC4ApiException);
//      assertDoesNotThrow(() -> b.andTerm(b));
//      Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
//      assertThrows(x.andTerm(b), CVC4ApiException);
//      assertThrows(x.andTerm(x), CVC4ApiException);
//      Term f = d_solver.mkVar(funSort1, "f");
//      assertThrows(f.andTerm(b), CVC4ApiException);
//      assertThrows(f.andTerm(x), CVC4ApiException);
//      assertThrows(f.andTerm(f), CVC4ApiException);
//      Term p = d_solver.mkVar(funSort2, "p");
//      assertThrows(p.andTerm(b), CVC4ApiException);
//      assertThrows(p.andTerm(x), CVC4ApiException);
//      assertThrows(p.andTerm(f), CVC4ApiException);
//      assertThrows(p.andTerm(p), CVC4ApiException);
//      Term zero = d_solver.mkInteger(0);
//      assertThrows(zero.andTerm(b), CVC4ApiException);
//      assertThrows(zero.andTerm(x), CVC4ApiException);
//      assertThrows(zero.andTerm(f), CVC4ApiException);
//      assertThrows(zero.andTerm(p), CVC4ApiException);
//      assertThrows(zero.andTerm(zero), CVC4ApiException);
//      Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
//      assertThrows(f_x.andTerm(b), CVC4ApiException);
//      assertThrows(f_x.andTerm(x), CVC4ApiException);
//      assertThrows(f_x.andTerm(f), CVC4ApiException);
//      assertThrows(f_x.andTerm(p), CVC4ApiException);
//      assertThrows(f_x.andTerm(zero), CVC4ApiException);
//      assertThrows(f_x.andTerm(f_x), CVC4ApiException);
//      Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
//      assertThrows(sum.andTerm(b), CVC4ApiException);
//      assertThrows(sum.andTerm(x), CVC4ApiException);
//      assertThrows(sum.andTerm(f), CVC4ApiException);
//      assertThrows(sum.andTerm(p), CVC4ApiException);
//      assertThrows(sum.andTerm(zero), CVC4ApiException);
//      assertThrows(sum.andTerm(f_x), CVC4ApiException);
//      assertThrows(sum.andTerm(sum), CVC4ApiException);
//      Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
//      assertDoesNotThrow(() -> p_0.andTerm(b));
//      assertThrows(p_0.andTerm(x), CVC4ApiException);
//      assertThrows(p_0.andTerm(f), CVC4ApiException);
//      assertThrows(p_0.andTerm(p), CVC4ApiException);
//      assertThrows(p_0.andTerm(zero), CVC4ApiException);
//      assertThrows(p_0.andTerm(f_x), CVC4ApiException);
//      assertThrows(p_0.andTerm(sum), CVC4ApiException);
//      assertDoesNotThrow(() -> p_0.andTerm(p_0));
//      Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
//      assertDoesNotThrow(() -> p_f_x.andTerm(b));
//      assertThrows(p_f_x.andTerm(x), CVC4ApiException);
//      assertThrows(p_f_x.andTerm(f), CVC4ApiException);
//      assertThrows(p_f_x.andTerm(p), CVC4ApiException);
//      assertThrows(p_f_x.andTerm(zero), CVC4ApiException);
//      assertThrows(p_f_x.andTerm(f_x), CVC4ApiException);
//      assertThrows(p_f_x.andTerm(sum), CVC4ApiException);
//      assertDoesNotThrow(() -> p_f_x.andTerm(p_0));
//      assertDoesNotThrow(() -> p_f_x.andTerm(p_f_x));
//    }
//
//    @Test void  orTerm)
//    {
//      Sort bvSort = d_solver.mkBitVectorSort(8);
//      Sort intSort = d_solver.getIntegerSort();
//      Sort boolSort = d_solver.getBooleanSort();
//      Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
//      Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);
//
//      Term b = d_solver.mkTrue();
//      assertThrows(Term().orTerm(b), CVC4ApiException);
//      assertThrows(b.orTerm(Term()), CVC4ApiException);
//      assertDoesNotThrow(() -> b.orTerm(b));
//      Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
//      assertThrows(x.orTerm(b), CVC4ApiException);
//      assertThrows(x.orTerm(x), CVC4ApiException);
//      Term f = d_solver.mkVar(funSort1, "f");
//      assertThrows(f.orTerm(b), CVC4ApiException);
//      assertThrows(f.orTerm(x), CVC4ApiException);
//      assertThrows(f.orTerm(f), CVC4ApiException);
//      Term p = d_solver.mkVar(funSort2, "p");
//      assertThrows(p.orTerm(b), CVC4ApiException);
//      assertThrows(p.orTerm(x), CVC4ApiException);
//      assertThrows(p.orTerm(f), CVC4ApiException);
//      assertThrows(p.orTerm(p), CVC4ApiException);
//      Term zero = d_solver.mkInteger(0);
//      assertThrows(zero.orTerm(b), CVC4ApiException);
//      assertThrows(zero.orTerm(x), CVC4ApiException);
//      assertThrows(zero.orTerm(f), CVC4ApiException);
//      assertThrows(zero.orTerm(p), CVC4ApiException);
//      assertThrows(zero.orTerm(zero), CVC4ApiException);
//      Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
//      assertThrows(f_x.orTerm(b), CVC4ApiException);
//      assertThrows(f_x.orTerm(x), CVC4ApiException);
//      assertThrows(f_x.orTerm(f), CVC4ApiException);
//      assertThrows(f_x.orTerm(p), CVC4ApiException);
//      assertThrows(f_x.orTerm(zero), CVC4ApiException);
//      assertThrows(f_x.orTerm(f_x), CVC4ApiException);
//      Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
//      assertThrows(sum.orTerm(b), CVC4ApiException);
//      assertThrows(sum.orTerm(x), CVC4ApiException);
//      assertThrows(sum.orTerm(f), CVC4ApiException);
//      assertThrows(sum.orTerm(p), CVC4ApiException);
//      assertThrows(sum.orTerm(zero), CVC4ApiException);
//      assertThrows(sum.orTerm(f_x), CVC4ApiException);
//      assertThrows(sum.orTerm(sum), CVC4ApiException);
//      Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
//      assertDoesNotThrow(() -> p_0.orTerm(b));
//      assertThrows(p_0.orTerm(x), CVC4ApiException);
//      assertThrows(p_0.orTerm(f), CVC4ApiException);
//      assertThrows(p_0.orTerm(p), CVC4ApiException);
//      assertThrows(p_0.orTerm(zero), CVC4ApiException);
//      assertThrows(p_0.orTerm(f_x), CVC4ApiException);
//      assertThrows(p_0.orTerm(sum), CVC4ApiException);
//      assertDoesNotThrow(() -> p_0.orTerm(p_0));
//      Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
//      assertDoesNotThrow(() -> p_f_x.orTerm(b));
//      assertThrows(p_f_x.orTerm(x), CVC4ApiException);
//      assertThrows(p_f_x.orTerm(f), CVC4ApiException);
//      assertThrows(p_f_x.orTerm(p), CVC4ApiException);
//      assertThrows(p_f_x.orTerm(zero), CVC4ApiException);
//      assertThrows(p_f_x.orTerm(f_x), CVC4ApiException);
//      assertThrows(p_f_x.orTerm(sum), CVC4ApiException);
//      assertDoesNotThrow(() -> p_f_x.orTerm(p_0));
//      assertDoesNotThrow(() -> p_f_x.orTerm(p_f_x));
//    }
//
//    @Test void  xorTerm)
//    {
//      Sort bvSort = d_solver.mkBitVectorSort(8);
//      Sort intSort = d_solver.getIntegerSort();
//      Sort boolSort = d_solver.getBooleanSort();
//      Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
//      Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);
//
//      Term b = d_solver.mkTrue();
//      assertThrows(Term().xorTerm(b), CVC4ApiException);
//      assertThrows(b.xorTerm(Term()), CVC4ApiException);
//      assertDoesNotThrow(() -> b.xorTerm(b));
//      Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
//      assertThrows(x.xorTerm(b), CVC4ApiException);
//      assertThrows(x.xorTerm(x), CVC4ApiException);
//      Term f = d_solver.mkVar(funSort1, "f");
//      assertThrows(f.xorTerm(b), CVC4ApiException);
//      assertThrows(f.xorTerm(x), CVC4ApiException);
//      assertThrows(f.xorTerm(f), CVC4ApiException);
//      Term p = d_solver.mkVar(funSort2, "p");
//      assertThrows(p.xorTerm(b), CVC4ApiException);
//      assertThrows(p.xorTerm(x), CVC4ApiException);
//      assertThrows(p.xorTerm(f), CVC4ApiException);
//      assertThrows(p.xorTerm(p), CVC4ApiException);
//      Term zero = d_solver.mkInteger(0);
//      assertThrows(zero.xorTerm(b), CVC4ApiException);
//      assertThrows(zero.xorTerm(x), CVC4ApiException);
//      assertThrows(zero.xorTerm(f), CVC4ApiException);
//      assertThrows(zero.xorTerm(p), CVC4ApiException);
//      assertThrows(zero.xorTerm(zero), CVC4ApiException);
//      Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
//      assertThrows(f_x.xorTerm(b), CVC4ApiException);
//      assertThrows(f_x.xorTerm(x), CVC4ApiException);
//      assertThrows(f_x.xorTerm(f), CVC4ApiException);
//      assertThrows(f_x.xorTerm(p), CVC4ApiException);
//      assertThrows(f_x.xorTerm(zero), CVC4ApiException);
//      assertThrows(f_x.xorTerm(f_x), CVC4ApiException);
//      Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
//      assertThrows(sum.xorTerm(b), CVC4ApiException);
//      assertThrows(sum.xorTerm(x), CVC4ApiException);
//      assertThrows(sum.xorTerm(f), CVC4ApiException);
//      assertThrows(sum.xorTerm(p), CVC4ApiException);
//      assertThrows(sum.xorTerm(zero), CVC4ApiException);
//      assertThrows(sum.xorTerm(f_x), CVC4ApiException);
//      assertThrows(sum.xorTerm(sum), CVC4ApiException);
//      Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
//      assertDoesNotThrow(() -> p_0.xorTerm(b));
//      assertThrows(p_0.xorTerm(x), CVC4ApiException);
//      assertThrows(p_0.xorTerm(f), CVC4ApiException);
//      assertThrows(p_0.xorTerm(p), CVC4ApiException);
//      assertThrows(p_0.xorTerm(zero), CVC4ApiException);
//      assertThrows(p_0.xorTerm(f_x), CVC4ApiException);
//      assertThrows(p_0.xorTerm(sum), CVC4ApiException);
//      assertDoesNotThrow(() -> p_0.xorTerm(p_0));
//      Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
//      assertDoesNotThrow(() -> p_f_x.xorTerm(b));
//      assertThrows(p_f_x.xorTerm(x), CVC4ApiException);
//      assertThrows(p_f_x.xorTerm(f), CVC4ApiException);
//      assertThrows(p_f_x.xorTerm(p), CVC4ApiException);
//      assertThrows(p_f_x.xorTerm(zero), CVC4ApiException);
//      assertThrows(p_f_x.xorTerm(f_x), CVC4ApiException);
//      assertThrows(p_f_x.xorTerm(sum), CVC4ApiException);
//      assertDoesNotThrow(() -> p_f_x.xorTerm(p_0));
//      assertDoesNotThrow(() -> p_f_x.xorTerm(p_f_x));
//    }
//
//    @Test void  eqTerm)
//    {
//      Sort bvSort = d_solver.mkBitVectorSort(8);
//      Sort intSort = d_solver.getIntegerSort();
//      Sort boolSort = d_solver.getBooleanSort();
//      Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
//      Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);
//
//      Term b = d_solver.mkTrue();
//      assertThrows(Term().eqTerm(b), CVC4ApiException);
//      assertThrows(b.eqTerm(Term()), CVC4ApiException);
//      assertDoesNotThrow(() -> b.eqTerm(b));
//      Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
//      assertThrows(x.eqTerm(b), CVC4ApiException);
//      assertDoesNotThrow(() -> x.eqTerm(x));
//      Term f = d_solver.mkVar(funSort1, "f");
//      assertThrows(f.eqTerm(b), CVC4ApiException);
//      assertThrows(f.eqTerm(x), CVC4ApiException);
//      assertDoesNotThrow(() -> f.eqTerm(f));
//      Term p = d_solver.mkVar(funSort2, "p");
//      assertThrows(p.eqTerm(b), CVC4ApiException);
//      assertThrows(p.eqTerm(x), CVC4ApiException);
//      assertThrows(p.eqTerm(f), CVC4ApiException);
//      assertDoesNotThrow(() -> p.eqTerm(p));
//      Term zero = d_solver.mkInteger(0);
//      assertThrows(zero.eqTerm(b), CVC4ApiException);
//      assertThrows(zero.eqTerm(x), CVC4ApiException);
//      assertThrows(zero.eqTerm(f), CVC4ApiException);
//      assertThrows(zero.eqTerm(p), CVC4ApiException);
//      assertDoesNotThrow(() -> zero.eqTerm(zero));
//      Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
//      assertThrows(f_x.eqTerm(b), CVC4ApiException);
//      assertThrows(f_x.eqTerm(x), CVC4ApiException);
//      assertThrows(f_x.eqTerm(f), CVC4ApiException);
//      assertThrows(f_x.eqTerm(p), CVC4ApiException);
//      assertDoesNotThrow(() -> f_x.eqTerm(zero));
//      assertDoesNotThrow(() -> f_x.eqTerm(f_x));
//      Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
//      assertThrows(sum.eqTerm(b), CVC4ApiException);
//      assertThrows(sum.eqTerm(x), CVC4ApiException);
//      assertThrows(sum.eqTerm(f), CVC4ApiException);
//      assertThrows(sum.eqTerm(p), CVC4ApiException);
//      assertDoesNotThrow(() -> sum.eqTerm(zero));
//      assertDoesNotThrow(() -> sum.eqTerm(f_x));
//      assertDoesNotThrow(() -> sum.eqTerm(sum));
//      Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
//      assertDoesNotThrow(() -> p_0.eqTerm(b));
//      assertThrows(p_0.eqTerm(x), CVC4ApiException);
//      assertThrows(p_0.eqTerm(f), CVC4ApiException);
//      assertThrows(p_0.eqTerm(p), CVC4ApiException);
//      assertThrows(p_0.eqTerm(zero), CVC4ApiException);
//      assertThrows(p_0.eqTerm(f_x), CVC4ApiException);
//      assertThrows(p_0.eqTerm(sum), CVC4ApiException);
//      assertDoesNotThrow(() -> p_0.eqTerm(p_0));
//      Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
//      assertDoesNotThrow(() -> p_f_x.eqTerm(b));
//      assertThrows(p_f_x.eqTerm(x), CVC4ApiException);
//      assertThrows(p_f_x.eqTerm(f), CVC4ApiException);
//      assertThrows(p_f_x.eqTerm(p), CVC4ApiException);
//      assertThrows(p_f_x.eqTerm(zero), CVC4ApiException);
//      assertThrows(p_f_x.eqTerm(f_x), CVC4ApiException);
//      assertThrows(p_f_x.eqTerm(sum), CVC4ApiException);
//      assertDoesNotThrow(() -> p_f_x.eqTerm(p_0));
//      assertDoesNotThrow(() -> p_f_x.eqTerm(p_f_x));
//    }
//
//    @Test void  impTerm)
//    {
//      Sort bvSort = d_solver.mkBitVectorSort(8);
//      Sort intSort = d_solver.getIntegerSort();
//      Sort boolSort = d_solver.getBooleanSort();
//      Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
//      Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);
//
//      Term b = d_solver.mkTrue();
//      assertThrows(Term().impTerm(b), CVC4ApiException);
//      assertThrows(b.impTerm(Term()), CVC4ApiException);
//      assertDoesNotThrow(() -> b.impTerm(b));
//      Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
//      assertThrows(x.impTerm(b), CVC4ApiException);
//      assertThrows(x.impTerm(x), CVC4ApiException);
//      Term f = d_solver.mkVar(funSort1, "f");
//      assertThrows(f.impTerm(b), CVC4ApiException);
//      assertThrows(f.impTerm(x), CVC4ApiException);
//      assertThrows(f.impTerm(f), CVC4ApiException);
//      Term p = d_solver.mkVar(funSort2, "p");
//      assertThrows(p.impTerm(b), CVC4ApiException);
//      assertThrows(p.impTerm(x), CVC4ApiException);
//      assertThrows(p.impTerm(f), CVC4ApiException);
//      assertThrows(p.impTerm(p), CVC4ApiException);
//      Term zero = d_solver.mkInteger(0);
//      assertThrows(zero.impTerm(b), CVC4ApiException);
//      assertThrows(zero.impTerm(x), CVC4ApiException);
//      assertThrows(zero.impTerm(f), CVC4ApiException);
//      assertThrows(zero.impTerm(p), CVC4ApiException);
//      assertThrows(zero.impTerm(zero), CVC4ApiException);
//      Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
//      assertThrows(f_x.impTerm(b), CVC4ApiException);
//      assertThrows(f_x.impTerm(x), CVC4ApiException);
//      assertThrows(f_x.impTerm(f), CVC4ApiException);
//      assertThrows(f_x.impTerm(p), CVC4ApiException);
//      assertThrows(f_x.impTerm(zero), CVC4ApiException);
//      assertThrows(f_x.impTerm(f_x), CVC4ApiException);
//      Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
//      assertThrows(sum.impTerm(b), CVC4ApiException);
//      assertThrows(sum.impTerm(x), CVC4ApiException);
//      assertThrows(sum.impTerm(f), CVC4ApiException);
//      assertThrows(sum.impTerm(p), CVC4ApiException);
//      assertThrows(sum.impTerm(zero), CVC4ApiException);
//      assertThrows(sum.impTerm(f_x), CVC4ApiException);
//      assertThrows(sum.impTerm(sum), CVC4ApiException);
//      Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
//      assertDoesNotThrow(() -> p_0.impTerm(b));
//      assertThrows(p_0.impTerm(x), CVC4ApiException);
//      assertThrows(p_0.impTerm(f), CVC4ApiException);
//      assertThrows(p_0.impTerm(p), CVC4ApiException);
//      assertThrows(p_0.impTerm(zero), CVC4ApiException);
//      assertThrows(p_0.impTerm(f_x), CVC4ApiException);
//      assertThrows(p_0.impTerm(sum), CVC4ApiException);
//      assertDoesNotThrow(() -> p_0.impTerm(p_0));
//      Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
//      assertDoesNotThrow(() -> p_f_x.impTerm(b));
//      assertThrows(p_f_x.impTerm(x), CVC4ApiException);
//      assertThrows(p_f_x.impTerm(f), CVC4ApiException);
//      assertThrows(p_f_x.impTerm(p), CVC4ApiException);
//      assertThrows(p_f_x.impTerm(zero), CVC4ApiException);
//      assertThrows(p_f_x.impTerm(f_x), CVC4ApiException);
//      assertThrows(p_f_x.impTerm(sum), CVC4ApiException);
//      assertDoesNotThrow(() -> p_f_x.impTerm(p_0));
//      assertDoesNotThrow(() -> p_f_x.impTerm(p_f_x));
//    }
//
//    @Test void  iteTerm)
//    {
//      Sort bvSort = d_solver.mkBitVectorSort(8);
//      Sort intSort = d_solver.getIntegerSort();
//      Sort boolSort = d_solver.getBooleanSort();
//      Sort funSort1 = d_solver.mkFunctionSort(bvSort, intSort);
//      Sort funSort2 = d_solver.mkFunctionSort(intSort, boolSort);
//
//      Term b = d_solver.mkTrue();
//      assertThrows(Term().iteTerm(b, b), CVC4ApiException);
//      assertThrows(b.iteTerm(Term(), b), CVC4ApiException);
//      assertThrows(b.iteTerm(b, Term()), CVC4ApiException);
//      assertDoesNotThrow(() -> b.iteTerm(b, b));
//      Term x = d_solver.mkVar(d_solver.mkBitVectorSort(8), "x");
//      assertDoesNotThrow(() -> b.iteTerm(x, x));
//      assertDoesNotThrow(() -> b.iteTerm(b, b));
//      assertThrows(b.iteTerm(x, b), CVC4ApiException);
//      assertThrows(x.iteTerm(x, x), CVC4ApiException);
//      assertThrows(x.iteTerm(x, b), CVC4ApiException);
//      Term f = d_solver.mkVar(funSort1, "f");
//      assertThrows(f.iteTerm(b, b), CVC4ApiException);
//      assertThrows(x.iteTerm(b, x), CVC4ApiException);
//      Term p = d_solver.mkVar(funSort2, "p");
//      assertThrows(p.iteTerm(b, b), CVC4ApiException);
//      assertThrows(p.iteTerm(x, b), CVC4ApiException);
//      Term zero = d_solver.mkInteger(0);
//      assertThrows(zero.iteTerm(x, x), CVC4ApiException);
//      assertThrows(zero.iteTerm(x, b), CVC4ApiException);
//      Term f_x = d_solver.mkTerm(APPLY_UF, f, x);
//      assertThrows(f_x.iteTerm(b, b), CVC4ApiException);
//      assertThrows(f_x.iteTerm(b, x), CVC4ApiException);
//      Term sum = d_solver.mkTerm(PLUS, f_x, f_x);
//      assertThrows(sum.iteTerm(x, x), CVC4ApiException);
//      assertThrows(sum.iteTerm(b, x), CVC4ApiException);
//      Term p_0 = d_solver.mkTerm(APPLY_UF, p, zero);
//      assertDoesNotThrow(() -> p_0.iteTerm(b, b));
//      assertDoesNotThrow(() -> p_0.iteTerm(x, x));
//      assertThrows(p_0.iteTerm(x, b), CVC4ApiException);
//      Term p_f_x = d_solver.mkTerm(APPLY_UF, p, f_x);
//      assertDoesNotThrow(() -> p_f_x.iteTerm(b, b));
//      assertDoesNotThrow(() -> p_f_x.iteTerm(x, x));
//      assertThrows(p_f_x.iteTerm(x, b), CVC4ApiException);
//    }
//
//    @Test void  termAssignment)
//    {
//      Term t1 = d_solver.mkInteger(1);
//      Term t2 = t1;
//      t2 = d_solver.mkInteger(2);
//      assertEquals(t1, d_solver.mkInteger(1));
//    }
//
//    @Test void  termCompare)
//    {
//      Term t1 = d_solver.mkInteger(1);
//      Term t2 = d_solver.mkTerm(PLUS, d_solver.mkInteger(2), d_solver.mkInteger(2));
//      Term t3 = d_solver.mkTerm(PLUS, d_solver.mkInteger(2), d_solver.mkInteger(2));
//      assertTrue(t2 >= t3);
//      assertTrue(t2 <= t3);
//      assertTrue((t1 > t2) != (t1 < t2));
//      assertTrue((t1 > t2 || t1 == t2) == (t1 >= t2));
//    }
//
//    @Test void  termChildren)
//    {
//      // simple term 2+3
//      Term two = d_solver.mkInteger(2);
//      Term t1 = d_solver.mkTerm(PLUS, two, d_solver.mkInteger(3));
//      assertEquals(t1[0], two);
//      assertEquals(t1.getNumChildren(), 2);
//      Term tnull;
//      assertThrows(tnull.getNumChildren(), CVC4ApiException);
//
//      // apply term f(2)
//      Sort intSort = d_solver.getIntegerSort();
//      Sort fsort = d_solver.mkFunctionSort(intSort, intSort);
//      Term f = d_solver.mkConst(fsort, "f");
//      Term t2 = d_solver.mkTerm(APPLY_UF, f, two);
//      // due to our higher-order view of terms, we treat f as a child of APPLY_UF
//      assertEquals(t2.getNumChildren(), 2);
//      assertEquals(t2[0], f);
//      assertEquals(t2[1], two);
//      assertThrows(tnull[0], CVC4ApiException);
//    }
//
//    @Test void  getInteger)
//    {
//      Term int1 = d_solver.mkInteger("-18446744073709551616");
//      Term int2 = d_solver.mkInteger("-18446744073709551615");
//      Term int3 = d_solver.mkInteger("-4294967296");
//      Term int4 = d_solver.mkInteger("-4294967295");
//      Term int5 = d_solver.mkInteger("-10");
//      Term int6 = d_solver.mkInteger("0");
//      Term int7 = d_solver.mkInteger("10");
//      Term int8 = d_solver.mkInteger("4294967295");
//      Term int9 = d_solver.mkInteger("4294967296");
//      Term int10 = d_solver.mkInteger("18446744073709551615");
//      Term int11 = d_solver.mkInteger("18446744073709551616");
//      Term int12 = d_solver.mkInteger("-0");
//
//      assertThrows(d_solver.mkInteger(""), CVC4ApiException);
//      assertThrows(d_solver.mkInteger("-"), CVC4ApiException);
//      assertThrows(d_solver.mkInteger("-1-"), CVC4ApiException);
//      assertThrows(d_solver.mkInteger("0.0"), CVC4ApiException);
//      assertThrows(d_solver.mkInteger("-0.1"), CVC4ApiException);
//      assertThrows(d_solver.mkInteger("012"), CVC4ApiException);
//      assertThrows(d_solver.mkInteger("0000"), CVC4ApiException);
//      assertThrows(d_solver.mkInteger("-01"), CVC4ApiException);
//      assertThrows(d_solver.mkInteger("-00"), CVC4ApiException);
//
//      assertTrue(!int1.isInt32() && !int1.isUInt32() && !int1.isInt64() && !int1.isUInt64()
//          && int1.isInteger());
//      assertEquals(int1.getInteger(), "-18446744073709551616");
//      assertTrue(!int2.isInt32() && !int2.isUInt32() && !int2.isInt64() && !int2.isUInt64()
//          && int2.isInteger());
//      assertEquals(int2.getInteger(), "-18446744073709551615");
//      assertTrue(!int3.isInt32() && !int3.isUInt32() && int3.isInt64() && !int3.isUInt64()
//          && int3.isInteger());
//      assertEquals(int3.getInt64(), -4294967296);
//      assertEquals(int3.getInteger(), "-4294967296");
//      assertTrue(!int4.isInt32() && !int4.isUInt32() && int4.isInt64() && !int4.isUInt64()
//          && int4.isInteger());
//      assertEquals(int4.getInt64(), -4294967295);
//      assertEquals(int4.getInteger(), "-4294967295");
//      assertTrue(int5.isInt32() && !int5.isUInt32() && int5.isInt64() && !int5.isUInt64()
//          && int5.isInteger());
//      assertEquals(int5.getInt32(), -10);
//      assertEquals(int5.getInt64(), -10);
//      assertEquals(int5.getInteger(), "-10");
//      assertTrue(int6.isInt32() && int6.isUInt32() && int6.isInt64() && int6.isUInt64()
//          && int6.isInteger());
//      assertEquals(int6.getInt32(), 0);
//      assertEquals(int6.getUInt32(), 0);
//      assertEquals(int6.getInt64(), 0);
//      assertEquals(int6.getUInt64(), 0);
//      assertEquals(int6.getInteger(), "0");
//      assertTrue(int7.isInt32() && int7.isUInt32() && int7.isInt64() && int7.isUInt64()
//          && int7.isInteger());
//      assertEquals(int7.getInt32(), 10);
//      assertEquals(int7.getUInt32(), 10);
//      assertEquals(int7.getInt64(), 10);
//      assertEquals(int7.getUInt64(), 10);
//      assertEquals(int7.getInteger(), "10");
//      assertTrue(!int8.isInt32() && int8.isUInt32() && int8.isInt64() && int8.isUInt64()
//          && int8.isInteger());
//      assertEquals(int8.getUInt32(), 4294967295);
//      assertEquals(int8.getInt64(), 4294967295);
//      assertEquals(int8.getUInt64(), 4294967295);
//      assertEquals(int8.getInteger(), "4294967295");
//      assertTrue(!int9.isInt32() && !int9.isUInt32() && int9.isInt64() && int9.isUInt64()
//          && int9.isInteger());
//      assertEquals(int9.getInt64(), 4294967296);
//      assertEquals(int9.getUInt64(), 4294967296);
//      assertEquals(int9.getInteger(), "4294967296");
//      assertTrue(!int10.isInt32() && !int10.isUInt32() && !int10.isInt64() && int10.isUInt64()
//          && int10.isInteger());
//      assertEquals(int10.getUInt64(), 18446744073709551615ull);
//      assertEquals(int10.getInteger(), "18446744073709551615");
//      assertTrue(!int11.isInt32() && !int11.isUInt32() && !int11.isInt64() && !int11.isUInt64()
//          && int11.isInteger());
//      assertEquals(int11.getInteger(), "18446744073709551616");
//    }
//
//    @Test void  getString)
//    {
//      Term s1 = d_solver.mkString("abcde");
//      assertTrue(s1.isString());
//      assertEquals(s1.getString(), L"abcde");
//    }
//
//    @Test void  substitute)
//    {
//      Term x = d_solver.mkConst(d_solver.getIntegerSort(), "x");
//      Term one = d_solver.mkInteger(1);
//      Term ttrue = d_solver.mkTrue();
//      Term xpx = d_solver.mkTerm(PLUS, x, x);
//      Term onepone = d_solver.mkTerm(PLUS, one, one);
//
//      assertEquals(xpx.substitute(x, one), onepone);
//      assertEquals(onepone.substitute(one, x), xpx);
//      // incorrect due to type
//      assertThrows(xpx.substitute(one, ttrue), CVC4ApiException);
//
//      // simultaneous substitution
//      Term y = d_solver.mkConst(d_solver.getIntegerSort(), "y");
//      Term xpy = d_solver.mkTerm(PLUS, x, y);
//      Term xpone = d_solver.mkTerm(PLUS, y, one);
//      std::vector<Term> es;
//      std::vector<Term> rs;
//      es.push_back(x);
//      rs.push_back(y);
//      es.push_back(y);
//      rs.push_back(one);
//      assertEquals(xpy.substitute(es, rs), xpone);
//
//      // incorrect substitution due to arity
//      rs.pop_back();
//      assertThrows(xpy.substitute(es, rs), CVC4ApiException);
//
//      // incorrect substitution due to types
//      rs.push_back(ttrue);
//      assertThrows(xpy.substitute(es, rs), CVC4ApiException);
//
//      // null cannot substitute
//      Term tnull;
//      assertThrows(tnull.substitute(one, x), CVC4ApiException);
//      assertThrows(xpx.substitute(tnull, x), CVC4ApiException);
//      assertThrows(xpx.substitute(x, tnull), CVC4ApiException);
//      rs.pop_back();
//      rs.push_back(tnull);
//      assertThrows(xpy.substitute(es, rs), CVC4ApiException);
//      es.clear();
//      rs.clear();
//      es.push_back(x);
//      rs.push_back(y);
//      assertThrows(tnull.substitute(es, rs), CVC4ApiException);
//      es.push_back(tnull);
//      rs.push_back(one);
//      assertThrows(xpx.substitute(es, rs), CVC4ApiException);
//    }
//
//    @Test void  constArray)
//    {
//      Sort intsort = d_solver.getIntegerSort();
//      Sort arrsort = d_solver.mkArraySort(intsort, intsort);
//      Term a = d_solver.mkConst(arrsort, "a");
//      Term one = d_solver.mkInteger(1);
//      Term constarr = d_solver.mkConstArray(arrsort, one);
//
//      assertEquals(constarr.getKind(), CONST_ARRAY);
//      assertEquals(constarr.getConstArrayBase(), one);
//      assertThrows(a.getConstArrayBase(), CVC4ApiException);
//
//      arrsort = d_solver.mkArraySort(d_solver.getRealSort(), d_solver.getRealSort());
//      Term zero_array = d_solver.mkConstArray(arrsort, d_solver.mkReal(0));
//      Term stores = d_solver.mkTerm(STORE, zero_array, d_solver.mkReal(1), d_solver.mkReal(2));
//      stores = d_solver.mkTerm(STORE, stores, d_solver.mkReal(2), d_solver.mkReal(3));
//      stores = d_solver.mkTerm(STORE, stores, d_solver.mkReal(4), d_solver.mkReal(5));
//    }
//
//    @Test void  constSequenceElements)
//    {
//      Sort realsort = d_solver.getRealSort();
//      Sort seqsort = d_solver.mkSequenceSort(realsort);
//      Term s = d_solver.mkEmptySequence(seqsort);
//
//      assertEquals(s.getKind(), CONST_SEQUENCE);
//      // empty sequence has zero elements
//      std::vector<Term> cs = s.getConstSequenceElements();
//      assertTrue(cs.empty());
//
//      // A seq.unit app is not a constant sequence (regardless of whether it is
//      // applied to a constant).
//      Term su = d_solver.mkTerm(SEQ_UNIT, d_solver.mkReal(1));
//      assertThrows(su.getConstSequenceElements(), CVC4ApiException);
//    }
//
//    @Test void  termScopedToString)
//    {
//      Sort intsort = d_solver.getIntegerSort();
//      Term x = d_solver.mkConst(intsort, "x");
//      assertEquals(x.toString(), "x");
//      Solver solver2;
//      assertEquals(x.toString(), "x");
//    }
}
