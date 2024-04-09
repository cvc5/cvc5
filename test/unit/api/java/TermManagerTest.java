/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the TermManager class of the Java API.
 */

package tests;

import static io.github.cvc5.Kind.*;
import static io.github.cvc5.RoundingMode.*;
import static io.github.cvc5.SortKind.*;
import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import java.math.BigInteger;
import java.util.*;
import java.util.concurrent.atomic.AtomicReference;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.function.Executable;

class TermManagerTest
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
  void getBooleanSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.getBooleanSort());
  }

  @Test
  void getIntegerSort()
  {
    assertDoesNotThrow(() -> d_tm.getIntegerSort());
  }

  @Test
  void getRealSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.getRealSort());
  }

  @Test
  void getRegExpSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.getRegExpSort());
  }

  @Test
  void getStringSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.getStringSort());
  }

  @Test
  void getRoundingModeSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.getRoundingModeSort());
  }

  @Test
  void mkArraySort() throws CVC5ApiException
  {
    Sort boolSort = d_tm.getBooleanSort();
    Sort intSort = d_tm.getIntegerSort();
    Sort realSort = d_tm.getRealSort();
    Sort bvSort = d_tm.mkBitVectorSort(32);
    assertDoesNotThrow(() -> d_tm.mkArraySort(boolSort, boolSort));
    assertDoesNotThrow(() -> d_tm.mkArraySort(intSort, intSort));
    assertDoesNotThrow(() -> d_tm.mkArraySort(realSort, realSort));
    assertDoesNotThrow(() -> d_tm.mkArraySort(bvSort, bvSort));
    assertDoesNotThrow(() -> d_tm.mkArraySort(boolSort, intSort));
    assertDoesNotThrow(() -> d_tm.mkArraySort(realSort, bvSort));

    Sort fpSort = d_tm.mkFloatingPointSort(3, 5);
    assertDoesNotThrow(() -> d_tm.mkArraySort(fpSort, fpSort));
    assertDoesNotThrow(() -> d_tm.mkArraySort(bvSort, fpSort));

    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkArraySort(boolSort, boolSort));
  }

  @Test
  void mkBitVectorSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkBitVectorSort(32));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVectorSort(0));
  }

  @Test
  void mkFloatingPointSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkFloatingPointSort(4, 8));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkFloatingPointSort(0, 8));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkFloatingPointSort(4, 0));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkFloatingPointSort(1, 8));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkFloatingPointSort(4, 1));
  }

  @Test
  void mkDatatypeSort() throws CVC5ApiException
  {
    DatatypeDecl dtypeSpec = d_tm.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", d_tm.getIntegerSort());
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    assertDoesNotThrow(() -> d_tm.mkDatatypeSort(dtypeSpec));

    assertThrows(CVC5ApiException.class, () -> d_tm.mkDatatypeSort(dtypeSpec));
    Solver slv = new Solver();
    assertThrows(CVC5ApiException.class, () -> slv.mkDatatypeSort(dtypeSpec));

    DatatypeDecl throwsDtypeSpec = d_tm.mkDatatypeDecl("list");
    assertThrows(CVC5ApiException.class, () -> d_tm.mkDatatypeSort(throwsDtypeSpec));
  }

  @Test
  void mkDatatypeSorts() throws CVC5ApiException
  {
    Solver slv = new Solver();

    DatatypeDecl dtypeSpec1 = d_tm.mkDatatypeDecl("list1");
    DatatypeConstructorDecl cons1 = d_tm.mkDatatypeConstructorDecl("cons1");
    cons1.addSelector("head1", d_tm.getIntegerSort());
    dtypeSpec1.addConstructor(cons1);
    DatatypeConstructorDecl nil1 = d_tm.mkDatatypeConstructorDecl("nil1");
    dtypeSpec1.addConstructor(nil1);
    DatatypeDecl dtypeSpec2 = d_tm.mkDatatypeDecl("list2");
    DatatypeConstructorDecl cons2 = d_tm.mkDatatypeConstructorDecl("cons2");
    cons2.addSelector("head2", d_tm.getIntegerSort());
    dtypeSpec2.addConstructor(cons2);
    DatatypeConstructorDecl nil2 = d_tm.mkDatatypeConstructorDecl("nil2");
    dtypeSpec2.addConstructor(nil2);
    DatatypeDecl[] decls = {dtypeSpec1, dtypeSpec2};
    assertDoesNotThrow(() -> d_tm.mkDatatypeSorts(decls));

    assertThrows(CVC5ApiException.class, () -> d_tm.mkDatatypeSorts(decls));
    assertThrows(CVC5ApiException.class, () -> slv.mkDatatypeSorts(decls));

    DatatypeDecl throwsDtypeSpec = d_tm.mkDatatypeDecl("list");
    DatatypeDecl[] throwsDecls = new DatatypeDecl[] {throwsDtypeSpec};
    assertThrows(CVC5ApiException.class, () -> d_tm.mkDatatypeSorts(throwsDecls));

    /* with unresolved sorts */
    Sort unresList = d_tm.mkUnresolvedDatatypeSort("ulist", 1);
    DatatypeDecl ulist = d_tm.mkDatatypeDecl("ulist");
    DatatypeConstructorDecl ucons = d_tm.mkDatatypeConstructorDecl("ucons");
    ucons.addSelector("car", unresList);
    ucons.addSelector("cdr", unresList);
    ulist.addConstructor(ucons);
    DatatypeConstructorDecl unil = d_tm.mkDatatypeConstructorDecl("unil");
    ulist.addConstructor(unil);
    DatatypeDecl[] udecls = new DatatypeDecl[] {ulist};
    assertDoesNotThrow(() -> d_tm.mkDatatypeSorts(udecls));

    assertThrows(CVC5ApiException.class, () -> d_tm.mkDatatypeSorts(udecls));
    assertThrows(CVC5ApiException.class, () -> slv.mkDatatypeSorts(udecls));

    /* mutually recursive with unresolved parameterized sorts */
    Sort p0 = d_tm.mkParamSort("p0");
    Sort p1 = d_tm.mkParamSort("p1");
    Sort u0 = d_tm.mkUnresolvedDatatypeSort("dt0", 1);
    Sort u1 = d_tm.mkUnresolvedDatatypeSort("dt1", 1);
    DatatypeDecl dtdecl0 = d_tm.mkDatatypeDecl("dt0", new Sort[] {p0});
    DatatypeDecl dtdecl1 = d_tm.mkDatatypeDecl("dt1", new Sort[] {p1});
    DatatypeConstructorDecl ctordecl0 = d_tm.mkDatatypeConstructorDecl("c0");
    ctordecl0.addSelector("s0", u1.instantiate(new Sort[] {p0}));
    DatatypeConstructorDecl ctordecl1 = d_tm.mkDatatypeConstructorDecl("c1");
    ctordecl1.addSelector("s1", u0.instantiate(new Sort[] {p1}));
    dtdecl0.addConstructor(ctordecl0);
    dtdecl1.addConstructor(ctordecl1);
    dtdecl1.addConstructor(d_tm.mkDatatypeConstructorDecl("nil"));
    Sort[] dt_sorts = d_tm.mkDatatypeSorts(new DatatypeDecl[] {dtdecl0, dtdecl1});
    Sort isort1 = dt_sorts[1].instantiate(new Sort[] {d_tm.getBooleanSort()});
    Term t1 = d_tm.mkConst(isort1, "t");
    Term t0 = d_tm.mkTerm(APPLY_SELECTOR,
        t1.getSort().getDatatype().getConstructor("c1").getSelector("s1").getTerm(),
        t1);
    assertEquals(dt_sorts[0].instantiate(new Sort[] {d_tm.getBooleanSort()}), t0.getSort());

    /* Note: More tests are in datatype_api_black. */
  }

  @Test
  void mkFunctionSort() throws CVC5ApiException
  {
    assertDoesNotThrow(
        () -> d_tm.mkFunctionSort(d_tm.mkUninterpretedSort("u"), d_tm.getIntegerSort()));
    Sort funSort = d_tm.mkFunctionSort(d_tm.mkUninterpretedSort("u"), d_tm.getIntegerSort());
    // function arguments are allowed
    assertDoesNotThrow(() -> d_tm.mkFunctionSort(funSort, d_tm.getIntegerSort()));
    // non-first-class arguments are not allowed
    Sort reSort = d_tm.getRegExpSort();
    assertThrows(CVC5ApiException.class, () -> d_tm.mkFunctionSort(reSort, d_tm.getIntegerSort()));

    assertThrows(CVC5ApiException.class, () -> d_tm.mkFunctionSort(d_tm.getIntegerSort(), funSort));

    assertDoesNotThrow(()
                           -> d_tm.mkFunctionSort(
                               new Sort[] {d_tm.mkUninterpretedSort("u"), d_tm.getIntegerSort()},
                               d_tm.getIntegerSort()));
    Sort funSort2 = d_tm.mkFunctionSort(d_tm.mkUninterpretedSort("u"), d_tm.getIntegerSort());
    // function arguments are allowed
    assertDoesNotThrow(
        ()
            -> d_tm.mkFunctionSort(
                new Sort[] {funSort2, d_tm.mkUninterpretedSort("u")}, d_tm.getIntegerSort()));
    assertThrows(CVC5ApiException.class,
        ()
            -> d_tm.mkFunctionSort(
                new Sort[] {d_tm.getIntegerSort(), d_tm.mkUninterpretedSort("u")}, funSort2));

    Solver slv = new Solver();
    assertDoesNotThrow(
        () -> slv.mkFunctionSort(d_tm.mkUninterpretedSort("u"), d_tm.getIntegerSort()));

    assertDoesNotThrow(
        () -> slv.mkFunctionSort(slv.mkUninterpretedSort("u"), d_tm.getIntegerSort()));

    Sort[] sorts1 = new Sort[] {d_tm.getBooleanSort(), slv.getIntegerSort(), d_tm.getIntegerSort()};
    Sort[] sorts2 = new Sort[] {slv.getBooleanSort(), slv.getIntegerSort()};
    assertDoesNotThrow(() -> slv.mkFunctionSort(sorts2, slv.getIntegerSort()));
    assertDoesNotThrow(() -> slv.mkFunctionSort(sorts1, slv.getIntegerSort()));
    assertDoesNotThrow(() -> slv.mkFunctionSort(sorts2, d_tm.getIntegerSort()));
  }

  @Test
  void mkParamSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkParamSort("T"));
    assertDoesNotThrow(() -> d_tm.mkParamSort(""));
  }

  @Test
  void mkPredicateSort()
  {
    assertDoesNotThrow(() -> d_tm.mkPredicateSort(new Sort[] {d_tm.getIntegerSort()}));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkPredicateSort(new Sort[] {}));
    Sort funSort = d_tm.mkFunctionSort(d_tm.mkUninterpretedSort("u"), d_tm.getIntegerSort());
    // functions as arguments are allowed
    assertDoesNotThrow(() -> d_tm.mkPredicateSort(new Sort[] {d_tm.getIntegerSort(), funSort}));

    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkPredicateSort(new Sort[] {d_tm.getIntegerSort()}));
  }

  @Test
  void mkRecordSort() throws CVC5ApiException
  {
    Pair<String, Sort>[] fields = new Pair[] {new Pair<>("b", d_tm.getBooleanSort()),
        new Pair<>("bv", d_tm.mkBitVectorSort(8)),
        new Pair<>("i", d_tm.getIntegerSort())};
    Pair<String, Sort>[] empty = new Pair[0];
    assertDoesNotThrow(() -> d_tm.mkRecordSort(fields));
    assertDoesNotThrow(() -> d_tm.mkRecordSort(empty));
    Sort recSort = d_tm.mkRecordSort(fields);
    assertDoesNotThrow(() -> recSort.getDatatype());

    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkRecordSort(fields));
  }

  @Test
  void mkSetSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkSetSort(d_tm.getBooleanSort()));
    assertDoesNotThrow(() -> d_tm.mkSetSort(d_tm.getIntegerSort()));
    assertDoesNotThrow(() -> d_tm.mkSetSort(d_tm.mkBitVectorSort(4)));
    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkSetSort(d_tm.mkBitVectorSort(4)));
  }

  @Test
  void mkBagSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkBagSort(d_tm.getBooleanSort()));
    assertDoesNotThrow(() -> d_tm.mkBagSort(d_tm.getIntegerSort()));
    assertDoesNotThrow(() -> d_tm.mkBagSort(d_tm.mkBitVectorSort(4)));
    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkBagSort(d_tm.mkBitVectorSort(4)));
  }

  @Test
  void mkSequenceSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkSequenceSort(d_tm.getBooleanSort()));
    assertDoesNotThrow(() -> d_tm.mkSequenceSort(d_tm.mkSequenceSort(d_tm.getIntegerSort())));
    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkSequenceSort(d_tm.getIntegerSort()));
  }

  @Test
  void mkAbstractSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkAbstractSort(ARRAY_SORT));
    assertDoesNotThrow(() -> d_tm.mkAbstractSort(BITVECTOR_SORT));
    assertDoesNotThrow(() -> d_tm.mkAbstractSort(TUPLE_SORT));
    assertDoesNotThrow(() -> d_tm.mkAbstractSort(SET_SORT));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkAbstractSort(BOOLEAN_SORT));
  }

  @Test
  void mkUninterpretedSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkUninterpretedSort("u"));
    assertDoesNotThrow(() -> d_tm.mkUninterpretedSort(""));
  }

  @Test
  void mkUnresolvedDatatypeSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkUnresolvedDatatypeSort("u"));
    assertDoesNotThrow(() -> d_tm.mkUnresolvedDatatypeSort("u", 1));
    assertDoesNotThrow(() -> d_tm.mkUnresolvedDatatypeSort(""));
    assertDoesNotThrow(() -> d_tm.mkUnresolvedDatatypeSort("", 1));
  }

  @Test
  void mkUninterpretedSortConstructorSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkUninterpretedSortConstructorSort(2, "s"));
    assertDoesNotThrow(() -> d_tm.mkUninterpretedSortConstructorSort(2));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkUninterpretedSortConstructorSort(0));
  }

  @Test
  void mkTupleSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkTupleSort(new Sort[] {d_tm.getIntegerSort()}));
    Sort funSort = d_tm.mkFunctionSort(d_tm.mkUninterpretedSort("u"), d_tm.getIntegerSort());
    assertDoesNotThrow(() -> d_tm.mkTupleSort(new Sort[] {d_tm.getIntegerSort(), funSort}));

    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkTupleSort(new Sort[] {d_tm.getIntegerSort()}));
  }

  @Test
  void mkNullableSort() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkNullableSort(d_tm.getIntegerSort()));

    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkNullableSort(d_tm.getIntegerSort()));
  }

  @Test
  void mkBitVector() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkBitVector(8, 2));
    assertDoesNotThrow(() -> d_tm.mkBitVector(32, 2));
    assertDoesNotThrow(() -> d_tm.mkBitVector(8, "-1111111", 2));
    assertDoesNotThrow(() -> d_tm.mkBitVector(8, "0101", 2));
    assertDoesNotThrow(() -> d_tm.mkBitVector(8, "00000101", 2));
    assertDoesNotThrow(() -> d_tm.mkBitVector(8, "-127", 10));
    assertDoesNotThrow(() -> d_tm.mkBitVector(8, "255", 10));
    assertDoesNotThrow(() -> d_tm.mkBitVector(8, "-7f", 16));
    assertDoesNotThrow(() -> d_tm.mkBitVector(8, "a0", 16));

    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(0, 2));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(0, "-127", 10));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(0, "a0", 16));

    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(8, "", 2));

    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(8, "101", 5));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(8, "128", 11));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(8, "a0", 21));

    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(8, "-11111111", 2));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(8, "101010101", 2));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(8, "-256", 10));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(8, "257", 10));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(8, "-a0", 16));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(8, "fffff", 16));

    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(8, "10201010", 2));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(8, "-25x", 10));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(8, "2x7", 10));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkBitVector(8, "fzff", 16));

    assertEquals(d_tm.mkBitVector(8, "0101", 2), d_tm.mkBitVector(8, "00000101", 2));
    assertEquals(d_tm.mkBitVector(4, "-1", 2), d_tm.mkBitVector(4, "1111", 2));
    assertEquals(d_tm.mkBitVector(4, "-1", 16), d_tm.mkBitVector(4, "1111", 2));
    assertEquals(d_tm.mkBitVector(4, "-1", 10), d_tm.mkBitVector(4, "1111", 2));
    assertEquals(d_tm.mkBitVector(8, "01010101", 2).toString(), "#b01010101");
    assertEquals(d_tm.mkBitVector(8, "F", 16).toString(), "#b00001111");
    assertEquals(d_tm.mkBitVector(8, "-1", 10), d_tm.mkBitVector(8, "FF", 16));
  }

  @Test
  void mkVar() throws CVC5ApiException
  {
    Sort boolSort = d_tm.getBooleanSort();
    Sort intSort = d_tm.getIntegerSort();
    Sort funSort = d_tm.mkFunctionSort(intSort, boolSort);
    assertDoesNotThrow(() -> d_tm.mkVar(boolSort));
    assertDoesNotThrow(() -> d_tm.mkVar(funSort));
    assertDoesNotThrow(() -> d_tm.mkVar(boolSort, ("b")));
    assertDoesNotThrow(() -> d_tm.mkVar(funSort, ""));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkVar(new Sort()));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkVar(new Sort(), "a"));
    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkVar(boolSort, "x"));
  }

  @Test
  void mkBoolean() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkBoolean(true));
    assertDoesNotThrow(() -> d_tm.mkBoolean(false));
  }

  @Test
  void mkRoundingMode() throws CVC5ApiException
  {
    assertEquals(d_tm.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_EVEN).toString(),
        "roundNearestTiesToEven");
    assertEquals(
        d_tm.mkRoundingMode(RoundingMode.ROUND_TOWARD_POSITIVE).toString(), "roundTowardPositive");
    assertEquals(
        d_tm.mkRoundingMode(RoundingMode.ROUND_TOWARD_NEGATIVE).toString(), "roundTowardNegative");
    assertEquals(d_tm.mkRoundingMode(RoundingMode.ROUND_TOWARD_ZERO).toString(), "roundTowardZero");
    assertEquals(d_tm.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_AWAY).toString(),
        "roundNearestTiesToAway");
  }

  @Test
  void mkFloatingPoint() throws CVC5ApiException
  {
    Term t1 = d_tm.mkBitVector(8);
    Term t2 = d_tm.mkBitVector(4);
    Term t3 = d_tm.mkInteger(2);
    assertDoesNotThrow(() -> d_tm.mkFloatingPoint(3, 5, t1));

    assertThrows(CVC5ApiException.class, () -> d_tm.mkFloatingPoint(0, 5, new Term()));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkFloatingPoint(0, 5, t1));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkFloatingPoint(3, 0, t1));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkFloatingPoint(3, 5, t2));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkFloatingPoint(3, 5, t2));

    assertEquals(
        d_tm.mkFloatingPoint(d_tm.mkBitVector(1), d_tm.mkBitVector(5), d_tm.mkBitVector(10)),
        d_tm.mkFloatingPoint(5, 11, d_tm.mkBitVector(16)));

    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkFloatingPoint(3, 5, t1));
  }

  @Test
  void mkCardinalityConstraint() throws CVC5ApiException
  {
    Sort su = d_tm.mkUninterpretedSort("u");
    Sort si = d_tm.getIntegerSort();
    assertDoesNotThrow(() -> d_tm.mkCardinalityConstraint(su, 3));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkCardinalityConstraint(si, 3));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkCardinalityConstraint(su, 0));
    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkCardinalityConstraint(su, 3));
  }

  @Test
  void mkEmptySet() throws CVC5ApiException
  {
    Solver slv = new Solver();
    Sort s = d_tm.mkSetSort(d_tm.getBooleanSort());
    assertThrows(CVC5ApiException.class, () -> d_tm.mkEmptySet(new Sort()));
    assertDoesNotThrow(() -> d_tm.mkEmptySet(s));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkEmptySet(d_tm.getBooleanSort()));
    assertDoesNotThrow(() -> slv.mkEmptySet(s));
  }

  @Test
  void mkEmptyBag() throws CVC5ApiException
  {
    Solver slv = new Solver();
    Sort s = d_tm.mkBagSort(d_tm.getBooleanSort());
    assertThrows(CVC5ApiException.class, () -> d_tm.mkEmptyBag(new Sort()));
    assertDoesNotThrow(() -> d_tm.mkEmptyBag(s));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkEmptyBag(d_tm.getBooleanSort()));

    assertDoesNotThrow(() -> slv.mkEmptyBag(s));
  }

  @Test
  void mkEmptySequence() throws CVC5ApiException
  {
    Solver slv = new Solver();
    Sort s = d_tm.mkSequenceSort(d_tm.getBooleanSort());
    assertDoesNotThrow(() -> d_tm.mkEmptySequence(s));
    assertDoesNotThrow(() -> d_tm.mkEmptySequence(d_tm.getBooleanSort()));
    assertDoesNotThrow(() -> slv.mkEmptySequence(s));
  }

  @Test
  void mkFalse() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkFalse());
    assertDoesNotThrow(() -> d_tm.mkFalse());
  }

  @Test
  void mkFloatingPointNaN() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkFloatingPointNaN(3, 5));
  }

  @Test
  void mkFloatingPointNegZero() throws CVC5ApiException
  {
    assertDoesNotThrow(() -> d_tm.mkFloatingPointNegZero(3, 5));
  }

  @Test
  void mkFloatingPointNegInf()
  {
    assertDoesNotThrow(() -> d_tm.mkFloatingPointNegInf(3, 5));
  }

  @Test
  void mkFloatingPointPosInf()
  {
    assertDoesNotThrow(() -> d_tm.mkFloatingPointPosInf(3, 5));
  }

  @Test
  void mkFloatingPointPosZero()
  {
    assertDoesNotThrow(() -> d_tm.mkFloatingPointPosZero(3, 5));
  }

  @Test
  void mkOp()
  {
    // Unlike c++,  mkOp(Kind kind, Kind k) is a type error in java
    // assertThrows(CVC5ApiException.class, () -> d_tm.mkOp(BITVECTOR_EXTRACT, EQUAL));

    // mkOp(Kind kind, const std::string& arg)
    assertDoesNotThrow(() -> d_tm.mkOp(DIVISIBLE, "2147483648"));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkOp(BITVECTOR_EXTRACT, "asdf"));

    // mkOp(Kind kind, int arg)
    assertDoesNotThrow(() -> d_tm.mkOp(DIVISIBLE, 1));
    assertDoesNotThrow(() -> d_tm.mkOp(BITVECTOR_ROTATE_LEFT, 1));
    assertDoesNotThrow(() -> d_tm.mkOp(BITVECTOR_ROTATE_RIGHT, 1));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkOp(BITVECTOR_EXTRACT, 1));

    // mkOp(Kind kind, int arg1, int arg2)
    assertDoesNotThrow(() -> d_tm.mkOp(BITVECTOR_EXTRACT, 1, 1));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkOp(DIVISIBLE, 1, 2));

    // mkOp(Kind kind, int[] args)
    int[] args = new int[] {1, 2, 2};
    assertDoesNotThrow(() -> d_tm.mkOp(TUPLE_PROJECT, args));
  }

  @Test
  void mkPi()
  {
    assertDoesNotThrow(() -> d_tm.mkPi());
  }

  @Test
  void mkInteger()
  {
    assertDoesNotThrow(() -> d_tm.mkInteger("123"));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger("1.23"));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger("1/23"));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger("12/3"));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger(".2"));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger("2."));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger(""));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger("asdf"));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger("1.2/3"));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger("."));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger("/"));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger("2/"));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger("/2"));

    assertDoesNotThrow(() -> d_tm.mkReal(("123")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger(("1.23")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger(("1/23")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger(("12/3")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger((".2")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger(("2.")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger(("")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger(("asdf")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger(("1.2/3")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger((".")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger(("/")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger(("2/")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkInteger(("/2")));

    int val1 = 1;
    long val2 = -1;
    int val3 = 1;
    long val4 = -1;
    assertDoesNotThrow(() -> d_tm.mkInteger(val1));
    assertDoesNotThrow(() -> d_tm.mkInteger(val2));
    assertDoesNotThrow(() -> d_tm.mkInteger(val3));
    assertDoesNotThrow(() -> d_tm.mkInteger(val4));
    assertDoesNotThrow(() -> d_tm.mkInteger(val4));
  }

  @Test
  void mkReal()
  {
    assertDoesNotThrow(() -> d_tm.mkReal("123"));
    assertDoesNotThrow(() -> d_tm.mkReal("1.23"));
    assertDoesNotThrow(() -> d_tm.mkReal("1/23"));
    assertDoesNotThrow(() -> d_tm.mkReal("12/3"));
    assertDoesNotThrow(() -> d_tm.mkReal(".2"));
    assertDoesNotThrow(() -> d_tm.mkReal("2."));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkReal(""));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkReal("asdf"));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkReal("1.2/3"));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkReal("."));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkReal("/"));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkReal("2/"));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkReal("/2"));

    assertDoesNotThrow(() -> d_tm.mkReal(("123")));
    assertDoesNotThrow(() -> d_tm.mkReal(("1.23")));
    assertDoesNotThrow(() -> d_tm.mkReal(("1/23")));
    assertDoesNotThrow(() -> d_tm.mkReal(("12/3")));
    assertDoesNotThrow(() -> d_tm.mkReal((".2")));
    assertDoesNotThrow(() -> d_tm.mkReal(("2.")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkReal(("")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkReal(("asdf")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkReal(("1.2/3")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkReal((".")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkReal(("/")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkReal(("2/")));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkReal(("/2")));

    int val1 = 1;
    long val2 = -1;
    int val3 = 1;
    long val4 = -1;
    assertDoesNotThrow(() -> d_tm.mkReal(val1));
    assertDoesNotThrow(() -> d_tm.mkReal(val2));
    assertDoesNotThrow(() -> d_tm.mkReal(val3));
    assertDoesNotThrow(() -> d_tm.mkReal(val4));
    assertDoesNotThrow(() -> d_tm.mkReal(val4));
    assertDoesNotThrow(() -> d_tm.mkReal(val1, val1));
    assertDoesNotThrow(() -> d_tm.mkReal(val2, val2));
    assertDoesNotThrow(() -> d_tm.mkReal(val3, val3));
    assertDoesNotThrow(() -> d_tm.mkReal(val4, val4));
  }

  @Test
  void mkRegexpNone()
  {
    Sort strSort = d_tm.getStringSort();
    Term s = d_tm.mkConst(strSort, "s");
    assertDoesNotThrow(() -> d_tm.mkTerm(STRING_IN_REGEXP, s, d_tm.mkRegexpNone()));
  }

  @Test
  void mkRegexpAll()
  {
    Sort strSort = d_tm.getStringSort();
    Term s = d_tm.mkConst(strSort, "s");
    assertDoesNotThrow(() -> d_tm.mkTerm(STRING_IN_REGEXP, s, d_tm.mkRegexpAll()));
  }

  @Test
  void mkRegexpAllchar()
  {
    Sort strSort = d_tm.getStringSort();
    Term s = d_tm.mkConst(strSort, "s");
    assertDoesNotThrow(() -> d_tm.mkTerm(STRING_IN_REGEXP, s, d_tm.mkRegexpAllchar()));
  }

  @Test
  void mkSepEmp()
  {
    assertDoesNotThrow(() -> d_tm.mkSepEmp());
  }

  @Test
  void mkSepNil()
  {
    assertDoesNotThrow(() -> d_tm.mkSepNil(d_tm.getBooleanSort()));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkSepNil(new Sort()));
    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkSepNil(d_tm.getIntegerSort()));
  }

  @Test
  void mkString()
  {
    assertDoesNotThrow(() -> d_tm.mkString(""));
    assertDoesNotThrow(() -> d_tm.mkString("asdfasdf"));
    assertEquals(d_tm.mkString("asdf\\nasdf").toString(), "\"asdf\\u{5c}nasdf\"");
    assertEquals(d_tm.mkString("asdf\\u{005c}nasdf", true).toString(), "\"asdf\\u{5c}nasdf\"");
  }

  @Test
  void mkTerm() throws CVC5ApiException
  {
    Sort bv32 = d_tm.mkBitVectorSort(32);
    Term a = d_tm.mkConst(bv32, "a");
    Term b = d_tm.mkConst(bv32, "b");
    Term[] v1 = new Term[] {a, b};
    Term[] v2 = new Term[] {a, new Term()};
    Term[] v3 = new Term[] {a, d_tm.mkTrue()};
    Term[] v4 = new Term[] {d_tm.mkInteger(1), d_tm.mkInteger(2)};
    Term[] v5 = new Term[] {d_tm.mkInteger(1), new Term()};
    Term[] v6 = new Term[] {};
    Solver slv = new Solver();

    // mkTerm(Kind kind) const
    assertDoesNotThrow(() -> d_tm.mkTerm(PI));
    assertDoesNotThrow(() -> d_tm.mkTerm(REGEXP_NONE));
    assertDoesNotThrow(() -> d_tm.mkTerm(REGEXP_ALLCHAR));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(CONST_BITVECTOR));

    // mkTerm(Kind kind, Term child) const
    assertDoesNotThrow(() -> d_tm.mkTerm(NOT, d_tm.mkTrue()));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(NOT, new Term()));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(NOT, a));
    assertDoesNotThrow(() -> slv.mkTerm(NOT, d_tm.mkTrue()));

    // mkTerm(Kind kind, Term child1, Term child2) const
    assertDoesNotThrow(() -> d_tm.mkTerm(EQUAL, a, b));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(EQUAL, new Term(), b));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(EQUAL, a, new Term()));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(EQUAL, a, d_tm.mkTrue()));
    assertDoesNotThrow(() -> slv.mkTerm(EQUAL, a, b));

    // mkTerm(Kind kind, Term child1, Term child2, Term child3) const
    assertDoesNotThrow(() -> d_tm.mkTerm(ITE, d_tm.mkTrue(), d_tm.mkTrue(), d_tm.mkTrue()));
    assertThrows(
        CVC5ApiException.class, () -> d_tm.mkTerm(ITE, new Term(), d_tm.mkTrue(), d_tm.mkTrue()));

    assertThrows(
        CVC5ApiException.class, () -> d_tm.mkTerm(ITE, d_tm.mkTrue(), new Term(), d_tm.mkTrue()));

    assertThrows(
        CVC5ApiException.class, () -> d_tm.mkTerm(ITE, d_tm.mkTrue(), d_tm.mkTrue(), new Term()));

    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(ITE, d_tm.mkTrue(), d_tm.mkTrue(), b));

    assertDoesNotThrow(() -> slv.mkTerm(ITE, d_tm.mkTrue(), d_tm.mkTrue(), d_tm.mkTrue()));

    // mkTerm(Kind kind, const Term[]& children) const
    assertDoesNotThrow(() -> d_tm.mkTerm(EQUAL, v1));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(EQUAL, v2));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(EQUAL, v3));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(DISTINCT, v6));
  }

  @Test
  void mkTermFromOp() throws CVC5ApiException
  {
    Sort bv32 = d_tm.mkBitVectorSort(32);
    Term a = d_tm.mkConst(bv32, "a");
    Term b = d_tm.mkConst(bv32, "b");
    Term[] v1 = new Term[] {d_tm.mkInteger(1), d_tm.mkInteger(2)};
    Term[] v2 = new Term[] {d_tm.mkInteger(1), new Term()};
    Term[] v3 = new Term[] {};
    Term[] v4 = new Term[] {d_tm.mkInteger(5)};
    Solver slv = new Solver();

    // simple operator terms
    Op opterm1 = d_tm.mkOp(BITVECTOR_EXTRACT, 2, 1);
    Op opterm2 = d_tm.mkOp(DIVISIBLE, 1);

    // list datatype
    Sort sort = d_tm.mkParamSort("T");
    DatatypeDecl listDecl = d_tm.mkDatatypeDecl("paramlist", new Sort[] {sort});
    DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
    DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
    cons.addSelector("head", sort);
    cons.addSelectorSelf("tail");
    listDecl.addConstructor(cons);
    listDecl.addConstructor(nil);
    Sort listSort = d_tm.mkDatatypeSort(listDecl);
    Sort intListSort = listSort.instantiate(new Sort[] {d_tm.getIntegerSort()});
    Term c = d_tm.mkConst(intListSort, "c");
    Datatype list = listSort.getDatatype();

    // list datatype constructor and selector operator terms
    Term consTerm = list.getConstructor("cons").getTerm();
    Term nilTerm = list.getConstructor("nil").getTerm();
    Term headTerm = list.getConstructor("cons").getSelector("head").getTerm();
    Term tailTerm = list.getConstructor("cons").getSelector("tail").getTerm();

    // mkTerm(Op op, Term term) const
    assertDoesNotThrow(() -> d_tm.mkTerm(APPLY_CONSTRUCTOR, nilTerm));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(APPLY_SELECTOR, nilTerm));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(APPLY_SELECTOR, consTerm));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(APPLY_CONSTRUCTOR, consTerm));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(opterm1));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(APPLY_SELECTOR, headTerm));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(opterm1));
    assertDoesNotThrow(() -> slv.mkTerm(APPLY_CONSTRUCTOR, nilTerm));

    // mkTerm(Op op, Term child) const
    assertDoesNotThrow(() -> d_tm.mkTerm(opterm1, a));
    assertDoesNotThrow(() -> d_tm.mkTerm(opterm2, d_tm.mkInteger(1)));
    assertDoesNotThrow(() -> d_tm.mkTerm(APPLY_SELECTOR, headTerm, c));
    assertDoesNotThrow(() -> d_tm.mkTerm(APPLY_SELECTOR, tailTerm, c));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(opterm2, a));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(opterm1, new Term()));
    assertThrows(
        CVC5ApiException.class, () -> d_tm.mkTerm(APPLY_CONSTRUCTOR, consTerm, d_tm.mkInteger(0)));

    assertDoesNotThrow(() -> slv.mkTerm(opterm1, a));

    // mkTerm(Op op, Term child1, Term child2) const
    assertDoesNotThrow(()
                           -> d_tm.mkTerm(APPLY_CONSTRUCTOR,
                               consTerm,
                               d_tm.mkInteger(0),
                               d_tm.mkTerm(APPLY_CONSTRUCTOR, nilTerm)));
    assertThrows(
        CVC5ApiException.class, () -> d_tm.mkTerm(opterm2, d_tm.mkInteger(1), d_tm.mkInteger(2)));

    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(opterm1, a, b));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(opterm2, d_tm.mkInteger(1), new Term()));

    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(opterm2, new Term(), d_tm.mkInteger(1)));

    assertDoesNotThrow(()
                           -> slv.mkTerm(APPLY_CONSTRUCTOR,
                               consTerm,
                               d_tm.mkInteger(0),
                               d_tm.mkTerm(APPLY_CONSTRUCTOR, nilTerm)));

    // mkTerm(Op op, Term child1, Term child2, Term child3) const
    Sort ssort = d_tm.getStringSort();
    Sort isort = d_tm.getIntegerSort();
    Sort xsort = d_tm.mkTupleSort(new Sort[] {ssort, ssort, isort});
    Sort ysort = d_tm.mkTupleSort(new Sort[] {ssort, isort});
    Term f = d_solver.defineFun("f",
        new Term[] {d_tm.mkVar(xsort, "x"), d_tm.mkVar(ysort, "y")},
        ysort,
        d_tm.mkTuple(new Term[] {
            d_tm.mkString("a"), d_tm.mkTerm(ADD, d_tm.mkInteger(1), d_tm.mkInteger(2))}));
    Term tup =
        d_tm.mkTuple(new Term[] {d_tm.mkString("foo"), d_tm.mkString("bar"), d_tm.mkInteger(1)});
    assertDoesNotThrow(()
                           -> d_tm.mkTerm(d_tm.mkOp(RELATION_AGGREGATE, 0),
                               f,
                               d_tm.mkTuple(new Term[] {d_tm.mkString(""), d_tm.mkInteger(0)}),
                               d_tm.mkTerm(SET_SINGLETON, tup)));

    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(opterm1, a, b, a));
    assertThrows(CVC5ApiException.class,
        () -> d_tm.mkTerm(opterm2, d_tm.mkInteger(1), d_tm.mkInteger(1), new Term()));

    // mkTerm(Op op, Term[] children)
    assertDoesNotThrow(() -> d_tm.mkTerm(opterm2, v4));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(opterm2, v1));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(opterm2, v2));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkTerm(opterm2, v3));
    assertDoesNotThrow(() -> slv.mkTerm(opterm2, v4));
  }

  @Test
  void mkTrue()
  {
    assertDoesNotThrow(() -> d_tm.mkTrue());
    assertDoesNotThrow(() -> d_tm.mkTrue());
  }

  @Test
  void mkTuple()
  {
    assertDoesNotThrow(() -> d_tm.mkTuple(new Term[] {d_tm.mkBitVector(3, "101", 2)}));
    assertDoesNotThrow(() -> d_tm.mkTuple(new Term[] {d_tm.mkInteger("5")}));

    assertDoesNotThrow(() -> d_tm.mkTuple(new Term[] {d_tm.mkReal("5.3")}));

    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkTuple(new Term[] {slv.mkBitVector(3, "101", 2)}));

    assertDoesNotThrow(() -> slv.mkTuple(new Term[] {d_tm.mkBitVector(3, "101", 2)}));
  }

  @Test
  void mkNullableSome()
  {
    assertDoesNotThrow(() -> d_tm.mkNullableSome(d_tm.mkBitVector(3, "101", 2)));
    assertDoesNotThrow(() -> d_tm.mkNullableSome(d_tm.mkInteger("5")));
    assertDoesNotThrow(() -> d_tm.mkNullableSome(d_tm.mkReal("5.3")));

    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkNullableSome(slv.mkBitVector(3, "101", 2)));

    assertDoesNotThrow(() -> slv.mkNullableSome(d_tm.mkBitVector(3, "101", 2)));
  }

  @Test
  void mkNullableVal()
  {
    Term some = d_tm.mkNullableSome(d_tm.mkInteger(5));
    Term value = d_tm.mkNullableVal(some);
    value = d_solver.simplify(value);
    assertEquals(5, value.getIntegerValue().intValue());
  }

  @Test
  void mkNullableIsNull()
  {
    Term some = d_tm.mkNullableSome(d_tm.mkInteger(5));
    Term value = d_tm.mkNullableIsNull(some);
    value = d_solver.simplify(value);
    assertEquals(false, value.getBooleanValue());
  }

  @Test
  void mkNullableIsSome()
  {
    Term some = d_tm.mkNullableSome(d_tm.mkInteger(5));
    Term value = d_tm.mkNullableIsSome(some);
    value = d_solver.simplify(value);
    assertEquals(true, value.getBooleanValue());
  }

  @Test
  void mkNullableNull()
  {
    Sort nullableSort = d_tm.mkNullableSort(d_tm.getBooleanSort());
    Term nullableNull = d_tm.mkNullableNull(nullableSort);
    Term value = d_tm.mkNullableIsNull(nullableNull);
    value = d_solver.simplify(value);
    assertEquals(true, value.getBooleanValue());
  }

  @Test
  void mkNullableLift()
  {
    Term some1 = d_tm.mkNullableSome(d_tm.mkInteger(1));
    Term some2 = d_tm.mkNullableSome(d_tm.mkInteger(2));
    Term some3 = d_tm.mkNullableLift(Kind.ADD, new Term[] {some1, some2});
    Term three = d_solver.simplify(d_tm.mkNullableVal(some3));
    assertEquals(3, three.getIntegerValue().intValue());
  }

  @Test
  void mkUniverseSet()
  {
    assertDoesNotThrow(() -> d_tm.mkUniverseSet(d_tm.getBooleanSort()));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkUniverseSet(new Sort()));
    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkUniverseSet(d_tm.getBooleanSort()));
  }

  @Test
  void mkConst()
  {
    Sort boolSort = d_tm.getBooleanSort();
    Sort intSort = d_tm.getIntegerSort();
    Sort funSort = d_tm.mkFunctionSort(intSort, boolSort);
    assertDoesNotThrow(() -> d_tm.mkConst(boolSort));
    assertDoesNotThrow(() -> d_tm.mkConst(funSort));
    assertDoesNotThrow(() -> d_tm.mkConst(boolSort, ("b")));
    assertDoesNotThrow(() -> d_tm.mkConst(intSort, ("i")));
    assertDoesNotThrow(() -> d_tm.mkConst(funSort, "f"));
    assertDoesNotThrow(() -> d_tm.mkConst(funSort, ""));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkConst(new Sort()));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkConst(new Sort(), "a"));

    Solver slv = new Solver();
    assertDoesNotThrow(() -> slv.mkConst(boolSort));
  }

  @Test
  void mkConstArray()
  {
    Sort intSort = d_tm.getIntegerSort();
    Sort arrSort = d_tm.mkArraySort(intSort, intSort);
    Term zero = d_tm.mkInteger(0);
    Term constArr = d_tm.mkConstArray(arrSort, zero);

    assertDoesNotThrow(() -> d_tm.mkConstArray(arrSort, zero));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkConstArray(new Sort(), zero));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkConstArray(arrSort, new Term()));
    assertThrows(CVC5ApiException.class, () -> d_tm.mkConstArray(arrSort, d_tm.mkBitVector(1, 1)));

    assertThrows(CVC5ApiException.class, () -> d_tm.mkConstArray(intSort, zero));
    Solver slv = new Solver();
    Term zero2 = slv.mkInteger(0);
    Sort arrSort2 = slv.mkArraySort(slv.getIntegerSort(), slv.getIntegerSort());
    assertDoesNotThrow(() -> slv.mkConstArray(arrSort2, zero));
    assertDoesNotThrow(() -> slv.mkConstArray(arrSort, zero2));
  }

  @Test
  void uFIteration()
  {
    Sort intSort = d_tm.getIntegerSort();
    Sort funSort = d_tm.mkFunctionSort(new Sort[] {intSort, intSort}, intSort);
    Term x = d_tm.mkConst(intSort, "x");
    Term y = d_tm.mkConst(intSort, "y");
    Term f = d_tm.mkConst(funSort, "f");
    Term fxy = d_tm.mkTerm(APPLY_UF, f, x, y);

    // Expecting the uninterpreted function to be one of the children
    Term expected_children[] = new Term[] {f, x, y};
    int idx = 0;
    for (Term c : fxy)
    {
      assertEquals(c, expected_children[idx]);
      idx++;
    }
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
    Statistics stats = d_tm.getStatistics();
    stats.toString();
    for (Map.Entry<String, Stat> s : stats)
    {
      assertFalse(s.getKey().isEmpty());
    }
    for (Statistics.ConstIterator it = stats.iterator(true, true); it.hasNext();)
    {
      Map.Entry<String, Stat> elem = it.next();
      if (elem.getKey().equals("cvc5::CONSTANT"))
      {
        assertFalse(elem.getValue().isInternal());
        assertFalse(elem.getValue().isDefault());
        assertTrue(elem.getValue().isHistogram());
        Map<String, Long> hist = elem.getValue().getHistogram();
        assertFalse(hist.isEmpty());
        assertEquals(elem.getValue().toString(), "{ integer type: 1 }");
      }
    }
  }
}
