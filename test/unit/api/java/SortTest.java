/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mathias Preiner, Mudathir Mohamed
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

package tests;
import static io.github.cvc5.api.Kind.*;
import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.api.*;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class SortTest
{
  private Solver d_solver;

  @BeforeEach void setUp()
  {
    d_solver = new Solver();
  }

  @AfterEach void tearDown()
  {
    d_solver.close();
  }

  Sort create_datatype_sort() throws CVC5ApiException
  {
    DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", d_solver.getIntegerSort());
    cons.addSelectorSelf("tail");
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    return d_solver.mkDatatypeSort(dtypeSpec);
  }

  Sort create_param_datatype_sort() throws CVC5ApiException
  {
    Sort sort = d_solver.mkParamSort("T");
    DatatypeDecl paramDtypeSpec = d_solver.mkDatatypeDecl("paramlist", sort);
    DatatypeConstructorDecl paramCons = d_solver.mkDatatypeConstructorDecl("cons");
    DatatypeConstructorDecl paramNil = d_solver.mkDatatypeConstructorDecl("nil");
    paramCons.addSelector("head", sort);
    paramDtypeSpec.addConstructor(paramCons);
    paramDtypeSpec.addConstructor(paramNil);
    return d_solver.mkDatatypeSort(paramDtypeSpec);
  }

  @Test void operators_comparison()
  {
    assertDoesNotThrow(() -> d_solver.getIntegerSort() == d_solver.getNullSort());
    assertDoesNotThrow(() -> d_solver.getIntegerSort() != d_solver.getNullSort());
    assertDoesNotThrow(() -> d_solver.getIntegerSort().compareTo(d_solver.getNullSort()));
  }

  @Test void isBoolean()
  {
    assertTrue(d_solver.getBooleanSort().isBoolean());
    assertDoesNotThrow(() -> d_solver.getNullSort().isBoolean());
  }

  @Test void isInteger()
  {
    assertTrue(d_solver.getIntegerSort().isInteger());
    assertTrue(!d_solver.getRealSort().isInteger());
    assertDoesNotThrow(() -> d_solver.getNullSort().isInteger());
  }

  @Test void isReal()
  {
    assertTrue(d_solver.getRealSort().isReal());
    assertTrue(!d_solver.getIntegerSort().isReal());
    assertDoesNotThrow(() -> d_solver.getNullSort().isReal());
  }

  @Test void isString()
  {
    assertTrue(d_solver.getStringSort().isString());
    assertDoesNotThrow(() -> d_solver.getNullSort().isString());
  }

  @Test void isRegExp()
  {
    assertTrue(d_solver.getRegExpSort().isRegExp());
    assertDoesNotThrow(() -> d_solver.getNullSort().isRegExp());
  }

  @Test void isRoundingMode() throws CVC5ApiException
  {
    assertTrue(d_solver.getRoundingModeSort().isRoundingMode());
    assertDoesNotThrow(() -> d_solver.getNullSort().isRoundingMode());
  }

  @Test void isBitVector() throws CVC5ApiException
  {
    assertTrue(d_solver.mkBitVectorSort(8).isBitVector());
    assertDoesNotThrow(() -> d_solver.getNullSort().isBitVector());
  }

  @Test void isFloatingPoint() throws CVC5ApiException
  {
    assertTrue(d_solver.mkFloatingPointSort(8, 24).isFloatingPoint());
    assertDoesNotThrow(() -> d_solver.getNullSort().isFloatingPoint());
  }

  @Test void isDatatype() throws CVC5ApiException
  {
    Sort dt_sort = create_datatype_sort();
    assertTrue(dt_sort.isDatatype());
    assertDoesNotThrow(() -> d_solver.getNullSort().isDatatype());
  }

  @Test void isParametricDatatype() throws CVC5ApiException
  {
    Sort param_dt_sort = create_param_datatype_sort();
    assertTrue(param_dt_sort.isParametricDatatype());
    assertDoesNotThrow(() -> d_solver.getNullSort().isParametricDatatype());
  }

  @Test void isConstructor() throws CVC5ApiException
  {
    Sort dt_sort = create_datatype_sort();
    Datatype dt = dt_sort.getDatatype();
    Sort cons_sort = dt.getConstructor(0).getConstructorTerm().getSort();
    assertTrue(cons_sort.isConstructor());
    assertDoesNotThrow(() -> d_solver.getNullSort().isConstructor());
  }

  @Test void isSelector() throws CVC5ApiException
  {
    Sort dt_sort = create_datatype_sort();
    Datatype dt = dt_sort.getDatatype();
    Sort cons_sort = dt.getConstructor(0).getSelector(1).getSelectorTerm().getSort();
    assertTrue(cons_sort.isSelector());
    assertDoesNotThrow(() -> d_solver.getNullSort().isSelector());
  }

  @Test void isTester() throws CVC5ApiException
  {
    Sort dt_sort = create_datatype_sort();
    Datatype dt = dt_sort.getDatatype();
    Sort cons_sort = dt.getConstructor(0).getTesterTerm().getSort();
    assertTrue(cons_sort.isTester());
    assertDoesNotThrow(() -> d_solver.getNullSort().isTester());
  }

  @Test void isFunction()
  {
    Sort fun_sort = d_solver.mkFunctionSort(d_solver.getRealSort(), d_solver.getIntegerSort());
    assertTrue(fun_sort.isFunction());
    assertDoesNotThrow(() -> d_solver.getNullSort().isFunction());
  }

  @Test void isPredicate()
  {
    Sort pred_sort = d_solver.mkPredicateSort(new Sort[] {d_solver.getRealSort()});
    assertTrue(pred_sort.isPredicate());
    assertDoesNotThrow(() -> d_solver.getNullSort().isPredicate());
  }

  @Test void isTuple()
  {
    Sort tup_sort = d_solver.mkTupleSort(new Sort[] {d_solver.getRealSort()});
    assertTrue(tup_sort.isTuple());
    assertDoesNotThrow(() -> d_solver.getNullSort().isTuple());
  }

  @Test void isRecord()
  {
    Sort rec_sort =
        d_solver.mkRecordSort(new Pair[] {new Pair<String, Sort>("asdf", d_solver.getRealSort())});
    assertTrue(rec_sort.isRecord());
    assertDoesNotThrow(() -> d_solver.getNullSort().isRecord());
  }

  @Test void isArray()
  {
    Sort arr_sort = d_solver.mkArraySort(d_solver.getRealSort(), d_solver.getIntegerSort());
    assertTrue(arr_sort.isArray());
    assertDoesNotThrow(() -> d_solver.getNullSort().isArray());
  }

  @Test void isSet()
  {
    Sort set_sort = d_solver.mkSetSort(d_solver.getRealSort());
    assertTrue(set_sort.isSet());
    assertDoesNotThrow(() -> d_solver.getNullSort().isSet());
  }

  @Test void isBag()
  {
    Sort bag_sort = d_solver.mkBagSort(d_solver.getRealSort());
    assertTrue(bag_sort.isBag());
    assertDoesNotThrow(() -> d_solver.getNullSort().isBag());
  }

  @Test void isSequence()
  {
    Sort seq_sort = d_solver.mkSequenceSort(d_solver.getRealSort());
    assertTrue(seq_sort.isSequence());
    assertDoesNotThrow(() -> d_solver.getNullSort().isSequence());
  }

  @Test void isUninterpreted()
  {
    Sort un_sort = d_solver.mkUninterpretedSort("asdf");
    assertTrue(un_sort.isUninterpretedSort());
    assertDoesNotThrow(() -> d_solver.getNullSort().isUninterpretedSort());
  }

  @Test void isSortConstructor() throws CVC5ApiException
  {
    Sort sc_sort = d_solver.mkSortConstructorSort("asdf", 1);
    assertTrue(sc_sort.isSortConstructor());
    assertDoesNotThrow(() -> d_solver.getNullSort().isSortConstructor());
  }

  @Test void isFirstClass()
  {
    Sort fun_sort = d_solver.mkFunctionSort(d_solver.getRealSort(), d_solver.getIntegerSort());
    assertTrue(d_solver.getIntegerSort().isFirstClass());
    assertTrue(fun_sort.isFirstClass());
    Sort reSort = d_solver.getRegExpSort();
    assertFalse(reSort.isFirstClass());
    assertDoesNotThrow(() -> d_solver.getNullSort().isFirstClass());
  }

  @Test void isFunctionLike() throws CVC5ApiException
  {
    Sort fun_sort = d_solver.mkFunctionSort(d_solver.getRealSort(), d_solver.getIntegerSort());
    assertFalse(d_solver.getIntegerSort().isFunctionLike());
    assertTrue(fun_sort.isFunctionLike());

    Sort dt_sort = create_datatype_sort();
    Datatype dt = dt_sort.getDatatype();
    Sort cons_sort = dt.getConstructor(0).getSelector(1).getSelectorTerm().getSort();
    assertTrue(cons_sort.isFunctionLike());

    assertDoesNotThrow(() -> d_solver.getNullSort().isFunctionLike());
  }

  @Test void isSubsortOf()
  {
    assertTrue(d_solver.getIntegerSort().isSubsortOf(d_solver.getIntegerSort()));
    assertTrue(d_solver.getIntegerSort().isSubsortOf(d_solver.getRealSort()));
    assertFalse(d_solver.getIntegerSort().isSubsortOf(d_solver.getBooleanSort()));
    assertDoesNotThrow(() -> d_solver.getNullSort().isSubsortOf(d_solver.getNullSort()));
  }

  @Test void isComparableTo()
  {
    assertTrue(d_solver.getIntegerSort().isComparableTo(d_solver.getIntegerSort()));
    assertTrue(d_solver.getIntegerSort().isComparableTo(d_solver.getRealSort()));
    assertFalse(d_solver.getIntegerSort().isComparableTo(d_solver.getBooleanSort()));
    assertDoesNotThrow(() -> d_solver.getNullSort().isComparableTo(d_solver.getNullSort()));
  }

  @Test void getDatatype() throws CVC5ApiException
  {
    Sort dtypeSort = create_datatype_sort();
    assertDoesNotThrow(() -> dtypeSort.getDatatype());
    // create bv sort, check should fail
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getDatatype());
  }

  @Test void datatypeSorts() throws CVC5ApiException
  {
    Sort intSort = d_solver.getIntegerSort();
    Sort dtypeSort = create_datatype_sort();
    Datatype dt = dtypeSort.getDatatype();
    assertFalse(dtypeSort.isConstructor());
    assertThrows(CVC5ApiException.class, () -> dtypeSort.getConstructorCodomainSort());
    assertThrows(CVC5ApiException.class, () -> dtypeSort.getConstructorDomainSorts());
    assertThrows(CVC5ApiException.class, () -> dtypeSort.getConstructorArity());

    // get constructor
    DatatypeConstructor dcons = dt.getConstructor(0);
    Term consTerm = dcons.getConstructorTerm();
    Sort consSort = consTerm.getSort();
    assertTrue(consSort.isConstructor());
    assertFalse(consSort.isTester());
    assertFalse(consSort.isSelector());
    assertEquals(consSort.getConstructorArity(), 2);
    Sort[] consDomSorts = consSort.getConstructorDomainSorts();
    assertEquals(consDomSorts[0], intSort);
    assertEquals(consDomSorts[1], dtypeSort);
    assertEquals(consSort.getConstructorCodomainSort(), dtypeSort);

    // get tester
    Term isConsTerm = dcons.getTesterTerm();
    assertTrue(isConsTerm.getSort().isTester());
    assertEquals(isConsTerm.getSort().getTesterDomainSort(), dtypeSort);
    Sort booleanSort = d_solver.getBooleanSort();
    assertEquals(isConsTerm.getSort().getTesterCodomainSort(), booleanSort);
    assertThrows(CVC5ApiException.class, () -> booleanSort.getTesterDomainSort());
    assertThrows(CVC5ApiException.class, () -> booleanSort.getTesterCodomainSort());

    // get selector
    DatatypeSelector dselTail = dcons.getSelector(1);
    Term tailTerm = dselTail.getSelectorTerm();
    assertTrue(tailTerm.getSort().isSelector());
    assertEquals(tailTerm.getSort().getSelectorDomainSort(), dtypeSort);
    assertEquals(tailTerm.getSort().getSelectorCodomainSort(), dtypeSort);
    assertThrows(CVC5ApiException.class, () -> booleanSort.getSelectorDomainSort());
    assertThrows(CVC5ApiException.class, () -> booleanSort.getSelectorCodomainSort());
  }

  @Test void instantiate() throws CVC5ApiException
  {
    // instantiate parametric datatype, check should not fail
    Sort paramDtypeSort = create_param_datatype_sort();
    assertDoesNotThrow(() -> paramDtypeSort.instantiate(new Sort[] {d_solver.getIntegerSort()}));
    // instantiate non-parametric datatype sort, check should fail
    DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", d_solver.getIntegerSort());
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
    assertThrows(CVC5ApiException.class,
        () -> dtypeSort.instantiate(new Sort[] {d_solver.getIntegerSort()}));
  }

  @Test void getFunctionArity() throws CVC5ApiException
  {
    Sort funSort =
        d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort());
    assertDoesNotThrow(() -> funSort.getFunctionArity());
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getFunctionArity());
  }

  @Test void getFunctionDomainSorts() throws CVC5ApiException
  {
    Sort funSort =
        d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort());
    assertDoesNotThrow(() -> funSort.getFunctionDomainSorts());
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getFunctionDomainSorts());
  }

  @Test void getFunctionCodomainSort() throws CVC5ApiException
  {
    Sort funSort =
        d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort());
    assertDoesNotThrow(() -> funSort.getFunctionCodomainSort());
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getFunctionCodomainSort());
  }

  @Test void getArrayIndexSort() throws CVC5ApiException
  {
    Sort elementSort = d_solver.mkBitVectorSort(32);
    Sort indexSort = d_solver.mkBitVectorSort(32);
    Sort arraySort = d_solver.mkArraySort(indexSort, elementSort);
    assertDoesNotThrow(() -> arraySort.getArrayIndexSort());
    assertThrows(CVC5ApiException.class, () -> indexSort.getArrayIndexSort());
  }

  @Test void getArrayElementSort() throws CVC5ApiException
  {
    Sort elementSort = d_solver.mkBitVectorSort(32);
    Sort indexSort = d_solver.mkBitVectorSort(32);
    Sort arraySort = d_solver.mkArraySort(indexSort, elementSort);
    assertDoesNotThrow(() -> arraySort.getArrayElementSort());
    assertThrows(CVC5ApiException.class, () -> indexSort.getArrayElementSort());
  }

  @Test void getSetElementSort() throws CVC5ApiException
  {
    Sort setSort = d_solver.mkSetSort(d_solver.getIntegerSort());
    assertDoesNotThrow(() -> setSort.getSetElementSort());
    Sort elementSort = setSort.getSetElementSort();
    assertEquals(elementSort, d_solver.getIntegerSort());
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getSetElementSort());
  }

  @Test void getBagElementSort() throws CVC5ApiException
  {
    Sort bagSort = d_solver.mkBagSort(d_solver.getIntegerSort());
    assertDoesNotThrow(() -> bagSort.getBagElementSort());
    Sort elementSort = bagSort.getBagElementSort();
    assertEquals(elementSort, d_solver.getIntegerSort());
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getBagElementSort());
  }

  @Test void getSequenceElementSort() throws CVC5ApiException
  {
    Sort seqSort = d_solver.mkSequenceSort(d_solver.getIntegerSort());
    assertTrue(seqSort.isSequence());
    assertDoesNotThrow(() -> seqSort.getSequenceElementSort());
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertFalse(bvSort.isSequence());
    assertThrows(CVC5ApiException.class, () -> bvSort.getSequenceElementSort());
  }

  @Test void getUninterpretedSortName() throws CVC5ApiException
  {
    Sort uSort = d_solver.mkUninterpretedSort("u");
    assertDoesNotThrow(() -> uSort.getUninterpretedSortName());
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getUninterpretedSortName());
  }

  @Test void isUninterpretedSortParameterized() throws CVC5ApiException
  {
    Sort uSort = d_solver.mkUninterpretedSort("u");
    assertFalse(uSort.isUninterpretedSortParameterized());
    Sort sSort = d_solver.mkSortConstructorSort("s", 1);
    Sort siSort = sSort.instantiate(new Sort[] {uSort});
    assertTrue(siSort.isUninterpretedSortParameterized());
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.isUninterpretedSortParameterized());
  }

  @Test void getUninterpretedSortParamSorts() throws CVC5ApiException
  {
    Sort uSort = d_solver.mkUninterpretedSort("u");
    assertDoesNotThrow(() -> uSort.getUninterpretedSortParamSorts());
    Sort sSort = d_solver.mkSortConstructorSort("s", 2);
    Sort siSort = sSort.instantiate(new Sort[] {uSort, uSort});
    assertEquals(siSort.getUninterpretedSortParamSorts().length, 2);
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getUninterpretedSortParamSorts());
  }

  @Test void getUninterpretedSortConstructorName() throws CVC5ApiException
  {
    Sort sSort = d_solver.mkSortConstructorSort("s", 2);
    assertDoesNotThrow(() -> sSort.getSortConstructorName());
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getSortConstructorName());
  }

  @Test void getUninterpretedSortConstructorArity() throws CVC5ApiException
  {
    Sort sSort = d_solver.mkSortConstructorSort("s", 2);
    assertDoesNotThrow(() -> sSort.getSortConstructorArity());
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getSortConstructorArity());
  }

  @Test void getBitVectorSize() throws CVC5ApiException
  {
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertDoesNotThrow(() -> bvSort.getBitVectorSize());
    Sort setSort = d_solver.mkSetSort(d_solver.getIntegerSort());
    assertThrows(CVC5ApiException.class, () -> setSort.getBitVectorSize());
  }

  @Test void getFloatingPointExponentSize() throws CVC5ApiException
  {
    Sort fpSort = d_solver.mkFloatingPointSort(4, 8);
    assertDoesNotThrow(() -> fpSort.getFloatingPointExponentSize());
    Sort setSort = d_solver.mkSetSort(d_solver.getIntegerSort());
    assertThrows(CVC5ApiException.class, () -> setSort.getFloatingPointExponentSize());
  }

  @Test void getFloatingPointSignificandSize() throws CVC5ApiException
  {
    Sort fpSort = d_solver.mkFloatingPointSort(4, 8);
    assertDoesNotThrow(() -> fpSort.getFloatingPointSignificandSize());
    Sort setSort = d_solver.mkSetSort(d_solver.getIntegerSort());
    assertThrows(CVC5ApiException.class, () -> setSort.getFloatingPointSignificandSize());
  }

  @Test void getDatatypeParamSorts() throws CVC5ApiException
  {
    // create parametric datatype, check should not fail
    Sort sort = d_solver.mkParamSort("T");
    DatatypeDecl paramDtypeSpec = d_solver.mkDatatypeDecl("paramlist", sort);
    DatatypeConstructorDecl paramCons = d_solver.mkDatatypeConstructorDecl("cons");
    DatatypeConstructorDecl paramNil = d_solver.mkDatatypeConstructorDecl("nil");
    paramCons.addSelector("head", sort);
    paramDtypeSpec.addConstructor(paramCons);
    paramDtypeSpec.addConstructor(paramNil);
    Sort paramDtypeSort = d_solver.mkDatatypeSort(paramDtypeSpec);
    assertDoesNotThrow(() -> paramDtypeSort.getDatatypeParamSorts());
    // create non-parametric datatype sort, check should fail
    DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", d_solver.getIntegerSort());
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
    assertThrows(CVC5ApiException.class, () -> dtypeSort.getDatatypeParamSorts());
  }

  @Test void getDatatypeArity() throws CVC5ApiException
  {
    // create datatype sort, check should not fail
    DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", d_solver.getIntegerSort());
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    Sort dtypeSort = d_solver.mkDatatypeSort(dtypeSpec);
    assertDoesNotThrow(() -> dtypeSort.getDatatypeArity());
    // create bv sort, check should fail
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getDatatypeArity());
  }

  @Test void getTupleLength() throws CVC5ApiException
  {
    Sort tupleSort =
        d_solver.mkTupleSort(new Sort[] {d_solver.getIntegerSort(), d_solver.getIntegerSort()});
    assertDoesNotThrow(() -> tupleSort.getTupleLength());
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getTupleLength());
  }

  @Test void getTupleSorts() throws CVC5ApiException
  {
    Sort tupleSort =
        d_solver.mkTupleSort(new Sort[] {d_solver.getIntegerSort(), d_solver.getIntegerSort()});
    assertDoesNotThrow(() -> tupleSort.getTupleSorts());
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertThrows(CVC5ApiException.class, () -> bvSort.getTupleSorts());
  }

  @Test void sortCompare() throws CVC5ApiException
  {
    Sort boolSort = d_solver.getBooleanSort();
    Sort intSort = d_solver.getIntegerSort();
    Sort bvSort = d_solver.mkBitVectorSort(32);
    Sort bvSort2 = d_solver.mkBitVectorSort(32);
    assertTrue(bvSort.compareTo(bvSort2) >= 0);
    assertTrue(bvSort.compareTo(bvSort2) <= 0);
    assertTrue(intSort.compareTo(boolSort) > 0 != intSort.compareTo(boolSort) < 0);
    assertTrue((intSort.compareTo(bvSort) > 0 || intSort.equals(bvSort))
        == (intSort.compareTo(bvSort) >= 0));
  }

  @Test void sortSubtyping()
  {
    Sort intSort = d_solver.getIntegerSort();
    Sort realSort = d_solver.getRealSort();
    assertTrue(intSort.isSubsortOf(realSort));
    assertFalse(realSort.isSubsortOf(intSort));
    assertTrue(intSort.isComparableTo(realSort));
    assertTrue(realSort.isComparableTo(intSort));

    Sort arraySortII = d_solver.mkArraySort(intSort, intSort);
    Sort arraySortIR = d_solver.mkArraySort(intSort, realSort);
    assertFalse(arraySortII.isComparableTo(intSort));
    // we do not support subtyping for arrays
    assertFalse(arraySortII.isComparableTo(arraySortIR));

    Sort setSortI = d_solver.mkSetSort(intSort);
    Sort setSortR = d_solver.mkSetSort(realSort);
    // we don't support subtyping for sets
    assertFalse(setSortI.isComparableTo(setSortR));
    assertFalse(setSortI.isSubsortOf(setSortR));
    assertFalse(setSortR.isComparableTo(setSortI));
    assertFalse(setSortR.isSubsortOf(setSortI));
  }

  @Test void sortScopedToString() throws CVC5ApiException
  {
    String name = "uninterp-sort";
    Sort bvsort8 = d_solver.mkBitVectorSort(8);
    Sort uninterp_sort = d_solver.mkUninterpretedSort(name);
    assertEquals(bvsort8.toString(), "(_ BitVec 8)");
    assertEquals(uninterp_sort.toString(), name);
    Solver solver2;
    assertEquals(bvsort8.toString(), "(_ BitVec 8)");
    assertEquals(uninterp_sort.toString(), name);
  }
}
