package cvc;

import static cvc.Kind.*;
import static cvc.RoundingMode.*;
import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class SolverTest
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

  @Test void recoverableException() throws CVCApiException
  {
    d_solver.setOption("produce-models", "true");
    Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
    d_solver.assertFormula(x.eqTerm(x).notTerm());
    assertThrows(CVCApiRecoverableException.class, () -> d_solver.getValue(x));
  }

  @Test void supportsFloatingPoint()
  {
    if (d_solver.supportsFloatingPoint())
    {
      assertDoesNotThrow(() -> d_solver.mkRoundingMode(ROUND_NEAREST_TIES_TO_EVEN));
    }
    else
    {
      assertThrows(
          CVCApiException.class, () -> d_solver.mkRoundingMode(ROUND_NEAREST_TIES_TO_EVEN));
    }
  }

  @Test void getBooleanSort()
  {
    assertDoesNotThrow(() -> d_solver.getBooleanSort());
  }

  @Test void getIntegerSort()
  {
    assertDoesNotThrow(() -> d_solver.getIntegerSort());
  }

  @Test void getNullSort()
  {
    assertDoesNotThrow(() -> d_solver.getNullSort());
  }

  @Test void getRealSort()
  {
    assertDoesNotThrow(() -> d_solver.getRealSort());
  }

  @Test void getRegExpSort()
  {
    assertDoesNotThrow(() -> d_solver.getRegExpSort());
  }

  @Test void getStringSort()
  {
    assertDoesNotThrow(() -> d_solver.getStringSort());
  }

  @Test void getRoundingModeSort()
  {
    if (d_solver.supportsFloatingPoint())
    {
      assertDoesNotThrow(() -> d_solver.getRoundingModeSort());
    }
    else
    {
      assertThrows(CVCApiException.class, () -> d_solver.getRoundingModeSort());
    }
  }

  @Test void mkArraySort() throws CVCApiException
  {
    Sort boolSort = d_solver.getBooleanSort();
    Sort intSort = d_solver.getIntegerSort();
    Sort realSort = d_solver.getRealSort();
    Sort bvSort = d_solver.mkBitVectorSort(32);
    assertDoesNotThrow(() -> d_solver.mkArraySort(boolSort, boolSort));
    assertDoesNotThrow(() -> d_solver.mkArraySort(intSort, intSort));
    assertDoesNotThrow(() -> d_solver.mkArraySort(realSort, realSort));
    assertDoesNotThrow(() -> d_solver.mkArraySort(bvSort, bvSort));
    assertDoesNotThrow(() -> d_solver.mkArraySort(boolSort, intSort));
    assertDoesNotThrow(() -> d_solver.mkArraySort(realSort, bvSort));

    if (d_solver.supportsFloatingPoint())
    {
      Sort fpSort = d_solver.mkFloatingPointSort(3, 5);
      assertDoesNotThrow(() -> d_solver.mkArraySort(fpSort, fpSort));
      assertDoesNotThrow(() -> d_solver.mkArraySort(bvSort, fpSort));
    }

    Solver slv = new Solver();
    assertThrows(CVCApiException.class, () -> slv.mkArraySort(boolSort, boolSort));
  }

  @Test void mkBitVectorSort()
  {
    assertDoesNotThrow(() -> d_solver.mkBitVectorSort(32));
    assertThrows(CVCApiException.class, () -> d_solver.mkBitVectorSort(0));
    assertThrows(CVCApiException.class, () -> d_solver.mkBitVectorSort(-5));
  }

  @Test void mkFloatingPointSort()
  {
    if (d_solver.supportsFloatingPoint())
    {
      assertDoesNotThrow(() -> d_solver.mkFloatingPointSort(4, 8));
      assertThrows(CVCApiException.class, () -> d_solver.mkFloatingPointSort(0, 8));
      assertThrows(CVCApiException.class, () -> d_solver.mkFloatingPointSort(4, 0));
    }
    else
    {
      assertThrows(CVCApiException.class, () -> d_solver.mkFloatingPointSort(4, 8));
    }
  }

  @Test void mkDatatypeSort()
  {
    DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", d_solver.getIntegerSort());
    dtypeSpec.addConstructor(cons);
    DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
    dtypeSpec.addConstructor(nil);
    assertDoesNotThrow(() -> d_solver.mkDatatypeSort(dtypeSpec));

    Solver slv = new Solver();
    assertThrows(CVCApiException.class, () -> slv.mkDatatypeSort(dtypeSpec));

    DatatypeDecl throwsDtypeSpec = d_solver.mkDatatypeDecl("list");
    assertThrows(CVCApiException.class, () -> d_solver.mkDatatypeSort(throwsDtypeSpec));
  }

  @Test void mkDatatypeSorts()
  {
    Solver slv = new Solver();

    DatatypeDecl dtypeSpec1 = d_solver.mkDatatypeDecl("list1");
    DatatypeConstructorDecl cons1 = d_solver.mkDatatypeConstructorDecl("cons1");
    cons1.addSelector("head1", d_solver.getIntegerSort());
    dtypeSpec1.addConstructor(cons1);
    DatatypeConstructorDecl nil1 = d_solver.mkDatatypeConstructorDecl("nil1");
    dtypeSpec1.addConstructor(nil1);
    DatatypeDecl dtypeSpec2 = d_solver.mkDatatypeDecl("list2");
    DatatypeConstructorDecl cons2 = d_solver.mkDatatypeConstructorDecl("cons2");
    cons2.addSelector("head2", d_solver.getIntegerSort());
    dtypeSpec2.addConstructor(cons2);
    DatatypeConstructorDecl nil2 = d_solver.mkDatatypeConstructorDecl("nil2");
    dtypeSpec2.addConstructor(nil2);
    DatatypeDecl[] decls = {dtypeSpec1, dtypeSpec2};
    assertDoesNotThrow(() -> d_solver.mkDatatypeSorts(decls));

    assertThrows(CVCApiException.class, () -> slv.mkDatatypeSorts(decls));

    DatatypeDecl throwsDtypeSpec = d_solver.mkDatatypeDecl("list");
    DatatypeDecl[] throwsDecls = {throwsDtypeSpec};
    assertThrows(CVCApiException.class, () -> d_solver.mkDatatypeSorts(throwsDecls));
    /* with unresolved sorts */
    Sort unresList = d_solver.mkUninterpretedSort("ulist");
    Sort[] unresSorts = {unresList};
    DatatypeDecl ulist = d_solver.mkDatatypeDecl("ulist");
    DatatypeConstructorDecl ucons = d_solver.mkDatatypeConstructorDecl("ucons");
    ucons.addSelector("car", unresList);
    ucons.addSelector("cdr", unresList);
    ulist.addConstructor(ucons);
    DatatypeConstructorDecl unil = d_solver.mkDatatypeConstructorDecl("unil");
    ulist.addConstructor(unil);
    DatatypeDecl[] udecls = {ulist};
    assertDoesNotThrow(() -> d_solver.mkDatatypeSorts(udecls, unresSorts));

    assertThrows(CVCApiException.class, () -> slv.mkDatatypeSorts(udecls, unresSorts));

    /* Note: More tests are in DatatypeTests. */
  }

  @Test void mkFunctionSort()
  {
    assertDoesNotThrow(()
                           -> d_solver.mkFunctionSort(
                               d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort()));
    Sort funSort =
        d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort());
    assertThrows(
        CVCApiException.class, () -> d_solver.mkFunctionSort(funSort, d_solver.getIntegerSort()));
    assertThrows(
        CVCApiException.class, () -> d_solver.mkFunctionSort(d_solver.getIntegerSort(), funSort));
    assertDoesNotThrow(()
                           -> d_solver.mkFunctionSort(new Sort[] {d_solver.mkUninterpretedSort("u"),
                                                          d_solver.getIntegerSort()},
                               d_solver.getIntegerSort()));
    Sort funSort2 =
        d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort());
    assertThrows(CVCApiException.class,
        ()
            -> d_solver.mkFunctionSort(new Sort[] {funSort2, d_solver.mkUninterpretedSort("u")},
                d_solver.getIntegerSort()));
    assertThrows(CVCApiException.class,
        ()
            -> d_solver.mkFunctionSort(
                new Sort[] {d_solver.getIntegerSort(), d_solver.mkUninterpretedSort("u")},
                funSort2));

    Solver slv = new Solver();
    assertThrows(CVCApiException.class,
        () -> slv.mkFunctionSort(d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort()));
    assertThrows(CVCApiException.class,
        () -> slv.mkFunctionSort(slv.mkUninterpretedSort("u"), d_solver.getIntegerSort()));
    Sort[] sorts1 = {d_solver.getBooleanSort(), slv.getIntegerSort(), d_solver.getIntegerSort()};
    Sort[] sorts2 = {slv.getBooleanSort(), slv.getIntegerSort()};
    assertDoesNotThrow(() -> slv.mkFunctionSort(sorts2, slv.getIntegerSort()));
    assertThrows(CVCApiException.class, () -> slv.mkFunctionSort(sorts1, slv.getIntegerSort()));
    assertThrows(
        CVCApiException.class, () -> slv.mkFunctionSort(sorts2, d_solver.getIntegerSort()));
  }

  @Test void mkParamSort()
  {
    assertDoesNotThrow(() -> d_solver.mkParamSort("T"));
    assertDoesNotThrow(() -> d_solver.mkParamSort(""));
  }

  @Test void mkPredicateSort()
  {
    assertDoesNotThrow(() -> d_solver.mkPredicateSort(new Sort[] {d_solver.getIntegerSort()}));
    assertThrows(CVCApiException.class, () -> d_solver.mkPredicateSort(new Sort[] {}));
    Sort funSort =
        d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort());
    assertThrows(CVCApiException.class,
        () -> d_solver.mkPredicateSort(new Sort[] {d_solver.getIntegerSort(), funSort}));

    Solver slv = new Solver();
    assertThrows(
        CVCApiException.class, () -> slv.mkPredicateSort(new Sort[] {d_solver.getIntegerSort()}));
  }

  @Test void mkRecordSort() throws CVCApiException
  {
    Pair<String, Sort>[] fields = new Pair[] {new Pair<>("b", d_solver.getBooleanSort()),
        new Pair<>("bv", d_solver.mkBitVectorSort(8)),
        new Pair<>("i", d_solver.getIntegerSort())};
    Pair<String, Sort>[] empty = new Pair[] {};
    assertDoesNotThrow(() -> d_solver.mkRecordSort(fields));
    assertDoesNotThrow(() -> d_solver.mkRecordSort(empty));
    Sort recSort = d_solver.mkRecordSort(fields);
    assertDoesNotThrow(() -> recSort.getDatatype());

    Solver slv = new Solver();
    assertThrows(CVCApiException.class, () -> slv.mkRecordSort(fields));
    Long x = Long.valueOf(10);
    x.longValue();
  }

  @Test void mkSetSort()
  {
    assertDoesNotThrow(() -> d_solver.mkSetSort(d_solver.getBooleanSort()));
    assertDoesNotThrow(() -> d_solver.mkSetSort(d_solver.getIntegerSort()));
    assertDoesNotThrow(() -> d_solver.mkSetSort(d_solver.mkBitVectorSort(4)));
    Solver slv = new Solver();
    assertThrows(CVCApiException.class, () -> slv.mkSetSort(d_solver.mkBitVectorSort(4)));
  }

  @Test void mkBagSort()
  {
    assertDoesNotThrow(() -> d_solver.mkBagSort(d_solver.getBooleanSort()));
    assertDoesNotThrow(() -> d_solver.mkBagSort(d_solver.getIntegerSort()));
    assertDoesNotThrow(() -> d_solver.mkBagSort(d_solver.mkBitVectorSort(4)));
    Solver slv = new Solver();
    assertThrows(CVCApiException.class, () -> slv.mkBagSort(d_solver.mkBitVectorSort(4)));
  }

  @Test void mkSequenceSort()
  {
    assertDoesNotThrow(() -> d_solver.mkSequenceSort(d_solver.getBooleanSort()));
    assertDoesNotThrow(
        () -> d_solver.mkSequenceSort(d_solver.mkSequenceSort(d_solver.getIntegerSort())));
    Solver slv = new Solver();
    assertThrows(CVCApiException.class, () -> slv.mkSequenceSort(d_solver.getIntegerSort()));
  }

  @Test void mkUninterpretedSort()
  {
    assertDoesNotThrow(() -> d_solver.mkUninterpretedSort("u"));
    assertDoesNotThrow(() -> d_solver.mkUninterpretedSort(""));
  }

  @Test void mkSortConstructorSort()
  {
    assertDoesNotThrow(() -> d_solver.mkSortConstructorSort("s", 2));
    assertDoesNotThrow(() -> d_solver.mkSortConstructorSort("", 2));
    assertThrows(CVCApiException.class, () -> d_solver.mkSortConstructorSort("", 0));
  }

  @Test void mkTupleSort()
  {
    assertDoesNotThrow(() -> d_solver.mkTupleSort(new Sort[] {d_solver.getIntegerSort()}));
    Sort funSort =
        d_solver.mkFunctionSort(d_solver.mkUninterpretedSort("u"), d_solver.getIntegerSort());
    assertThrows(CVCApiException.class,
        () -> d_solver.mkTupleSort(new Sort[] {d_solver.getIntegerSort(), funSort}));

    Solver slv = new Solver();
    assertThrows(
        CVCApiException.class, () -> slv.mkTupleSort(new Sort[] {d_solver.getIntegerSort()}));
  }

  @Test void mkBitVector() throws CVCApiException
  {
    int size0 = 0, size1 = 8, size2 = 32, val1 = 2;
    long val2 = 2;
    assertDoesNotThrow(() -> d_solver.mkBitVector(size1, val1));
    assertDoesNotThrow(() -> d_solver.mkBitVector(size2, val2));
    assertDoesNotThrow(() -> d_solver.mkBitVector("1010", 2));
    assertDoesNotThrow(() -> d_solver.mkBitVector("1010", 10));
    assertDoesNotThrow(() -> d_solver.mkBitVector("1234", 10));
    assertDoesNotThrow(() -> d_solver.mkBitVector("1010", 16));
    assertDoesNotThrow(() -> d_solver.mkBitVector("a09f", 16));
    assertDoesNotThrow(() -> d_solver.mkBitVector(8, "-127", 10));
    assertThrows(CVCApiException.class, () -> d_solver.mkBitVector(size0, val1));
    assertThrows(CVCApiException.class, () -> d_solver.mkBitVector(size0, val2));
    assertThrows(CVCApiException.class, () -> d_solver.mkBitVector("", 2));
    assertThrows(CVCApiException.class, () -> d_solver.mkBitVector("10", 3));
    assertThrows(CVCApiException.class, () -> d_solver.mkBitVector("20", 2));
    assertThrows(CVCApiException.class, () -> d_solver.mkBitVector(8, "101010101", 2));
    assertThrows(CVCApiException.class, () -> d_solver.mkBitVector(8, "-256", 10));
    assertEquals(d_solver.mkBitVector("1010", 2), d_solver.mkBitVector("10", 10));
    assertEquals(d_solver.mkBitVector("1010", 2), d_solver.mkBitVector("a", 16));
    assertEquals(d_solver.mkBitVector(8, "01010101", 2).toString(), "#b01010101");
    assertEquals(d_solver.mkBitVector(8, "F", 16).toString(), "#b00001111");
    assertEquals(d_solver.mkBitVector(8, "-1", 10), d_solver.mkBitVector(8, "FF", 16));
  }

  @Test void mkVar()
  {
    Sort boolSort = d_solver.getBooleanSort();
    Sort intSort = d_solver.getIntegerSort();
    Sort funSort = d_solver.mkFunctionSort(intSort, boolSort);
    assertDoesNotThrow(() -> d_solver.mkVar(boolSort));
    assertDoesNotThrow(() -> d_solver.mkVar(funSort));
    assertDoesNotThrow(() -> d_solver.mkVar(boolSort, "b"));
    assertDoesNotThrow(() -> d_solver.mkVar(funSort, ""));
    assertThrows(CVCApiException.class, () -> d_solver.mkVar(d_solver.getNullSort()));
    assertThrows(CVCApiException.class, () -> d_solver.mkVar(d_solver.getNullSort(), "a"));
    Solver slv = new Solver();
    assertThrows(CVCApiException.class, () -> slv.mkVar(boolSort, "x"));
  }

  @Test void mkBoolean()
  {
    assertDoesNotThrow(() -> d_solver.mkBoolean(true));
    assertDoesNotThrow(() -> d_solver.mkBoolean(false));
  }

//  @Test void mkRoundingMode()
//  {
//    if (Configuration.isBuiltWithSymFPU())
//    {
//      assertDoesNotThrow(() -> d_solver.mkRoundingMode(RoundingMode.ROUND_TOWARD_ZERO));
//    }
//    else
//    {
//      assertThrows(
//          CVCApiException.class, () -> d_solver.mkRoundingMode(RoundingMode.ROUND_TOWARD_ZERO));
//    }
//  }

  @Test void mkUninterpretedConst()
  {
    assertDoesNotThrow(() -> d_solver.mkUninterpretedConst(d_solver.getBooleanSort(), 1));
    assertThrows(
        CVCApiException.class, () -> d_solver.mkUninterpretedConst(d_solver.getNullSort(), 1));
    Solver slv = new Solver();
    assertThrows(
        CVCApiException.class, () -> slv.mkUninterpretedConst(d_solver.getBooleanSort(), 1));
  }

  @Test void mkAbstractValue()
  {
    assertDoesNotThrow(() -> d_solver.mkAbstractValue(("1")));
    assertThrows(CVCApiException.class, () -> d_solver.mkAbstractValue("0"));
    assertThrows(CVCApiException.class, () -> d_solver.mkAbstractValue("-1"));
    assertThrows(CVCApiException.class, () -> d_solver.mkAbstractValue("1.2"));
    assertThrows(CVCApiException.class, () -> d_solver.mkAbstractValue("1/2"));
    assertThrows(CVCApiException.class, () -> d_solver.mkAbstractValue("asdf"));

    assertDoesNotThrow(() -> d_solver.mkAbstractValue(1));
    assertDoesNotThrow(() -> d_solver.mkAbstractValue((long) 1));
    assertDoesNotThrow(() -> d_solver.mkAbstractValue(-1));
    assertDoesNotThrow(() -> d_solver.mkAbstractValue(-1));
    assertThrows(CVCApiException.class, () -> d_solver.mkAbstractValue(0));
  }

// Configuration no longer part of the API
//  @Test void mkFloatingPoint() throws CVCApiException
//  {
//    Term t1 = d_solver.mkBitVector(8);
//    Term t2 = d_solver.mkBitVector(4);
//    Term t3 = d_solver.mkInteger(2);
//    if (Configuration.isBuiltWithSymFPU())
//    {
//      assertDoesNotThrow(() -> d_solver.mkFloatingPoint(3, 5, t1));
//    }
//    else
//    {
//      assertThrows(CVCApiException.class, () -> d_solver.mkFloatingPoint(3, 5, t1));
//    }
//    // TODO: figure out what to do with Term()
//    // assertThrows(CVCApiException.class, () -> d_solver.mkFloatingPoint(0, 5, Term()));
//    assertThrows(CVCApiException.class, () -> d_solver.mkFloatingPoint(0, 5, t1));
//    assertThrows(CVCApiException.class, () -> d_solver.mkFloatingPoint(3, 0, t1));
//    assertThrows(CVCApiException.class, () -> d_solver.mkFloatingPoint(3, 5, t2));
//    assertThrows(CVCApiException.class, () -> d_solver.mkFloatingPoint(3, 5, t2));
//
//    if (Configuration.isBuiltWithSymFPU())
//    {
//      Solver slv = new Solver();
//      assertThrows(CVCApiException.class, () -> slv.mkFloatingPoint(3, 5, t1));
//    }
//  }

  @Test void mkEmptySet()
  {
    Solver slv = new Solver();
    Sort s = d_solver.mkSetSort(d_solver.getBooleanSort());
    assertDoesNotThrow(() -> d_solver.mkEmptySet(d_solver.getNullSort()));
    assertDoesNotThrow(() -> d_solver.mkEmptySet(s));
    assertThrows(CVCApiException.class, () -> d_solver.mkEmptySet(d_solver.getBooleanSort()));
    assertThrows(CVCApiException.class, () -> slv.mkEmptySet(s));
  }

  @Test void mkEmptyBag()
  {
    Solver slv = new Solver();
    Sort s = d_solver.mkBagSort(d_solver.getBooleanSort());
    assertDoesNotThrow(() -> d_solver.mkEmptyBag(d_solver.getNullSort()));
    assertDoesNotThrow(() -> d_solver.mkEmptyBag(s));
    assertThrows(CVCApiException.class, () -> d_solver.mkEmptyBag(d_solver.getBooleanSort()));
    assertThrows(CVCApiException.class, () -> slv.mkEmptyBag(s));
  }

  @Test void mkEmptySequence()
  {
    Solver slv = new Solver();
    Sort s = d_solver.mkSequenceSort(d_solver.getBooleanSort());
    assertDoesNotThrow(() -> d_solver.mkEmptySequence(s));
    assertDoesNotThrow(() -> d_solver.mkEmptySequence(d_solver.getBooleanSort()));
    assertThrows(CVCApiException.class, () -> slv.mkEmptySequence(s));
  }

  @Test void mkFalse()
  {
    assertDoesNotThrow(() -> d_solver.mkFalse());
    assertDoesNotThrow(() -> d_solver.mkFalse());
  }

// Configuration no longer part of the API
//  @Test void mkNaN()
//  {
//    if (Configuration.isBuiltWithSymFPU())
//    {
//      assertDoesNotThrow(() -> d_solver.mkNaN(3, 5));
//    }
//    else
//    {
//      assertThrows(CVCApiException.class, () -> d_solver.mkNaN(3, 5));
//    }
//  }

// Configuration no longer part of the API
//  @Test void mkNegZero()
//  {
//    if (Configuration.isBuiltWithSymFPU())
//    {
//      assertDoesNotThrow(() -> d_solver.mkNegZero(3, 5));
//    }
//    else
//    {
//      assertThrows(CVCApiException.class, () -> d_solver.mkNegZero(3, 5));
//    }
//  }

// Configuration no longer part of the API
//  @Test void mkNegInf()
//  {
//    if (Configuration.isBuiltWithSymFPU())
//    {
//      assertDoesNotThrow(() -> d_solver.mkNegInf(3, 5));
//    }
//    else
//    {
//      assertThrows(CVCApiException.class, () -> d_solver.mkNegInf(3, 5));
//    }
//  }

// Configuration no longer part of the API
//  @Test void mkPosInf()
//  {
//    if (Configuration.isBuiltWithSymFPU())
//    {
//      assertDoesNotThrow(() -> d_solver.mkPosInf(3, 5));
//    }
//    else
//    {
//      assertThrows(CVCApiException.class, () -> d_solver.mkPosInf(3, 5));
//    }
//  }

// Configuration no longer part of the API
//  @Test void mkPosZero()
//  {
//    if (Configuration.isBuiltWithSymFPU())
//    {
//      assertDoesNotThrow(() -> d_solver.mkPosZero(3, 5));
//    }
//    else
//    {
//      assertThrows(CVCApiException.class, () -> d_solver.mkPosZero(3, 5));
//    }
//  }

  @Test void mkOp()
  {
    // mkOp(Kind kind, Kind k)
    assertThrows(CVCApiException.class, () -> d_solver.mkOp(BITVECTOR_EXTRACT, EQUAL.getValue()));

    // mkOp(Kind kind, const std::string& arg)
    assertDoesNotThrow(() -> d_solver.mkOp(RECORD_UPDATE, "asdf"));
    assertDoesNotThrow(() -> d_solver.mkOp(DIVISIBLE, "2147483648"));
    assertThrows(CVCApiException.class, () -> d_solver.mkOp(BITVECTOR_EXTRACT, "asdf"));

    // mkOp(Kind kind, uint32_t arg)
    assertDoesNotThrow(() -> d_solver.mkOp(DIVISIBLE, 1));
    assertDoesNotThrow(() -> d_solver.mkOp(BITVECTOR_ROTATE_LEFT, 1));
    assertDoesNotThrow(() -> d_solver.mkOp(BITVECTOR_ROTATE_RIGHT, 1));
    assertThrows(CVCApiException.class, () -> d_solver.mkOp(BITVECTOR_EXTRACT, 1));

    // mkOp(Kind kind, uint32_t arg1, uint32_t arg2)
    assertDoesNotThrow(() -> d_solver.mkOp(BITVECTOR_EXTRACT, 1, 1));
    assertThrows(CVCApiException.class, () -> d_solver.mkOp(DIVISIBLE, 1, 2));
  }

  @Test void mkPi()
  {
    assertDoesNotThrow(() -> d_solver.mkPi());
  }

  @Test void mkInteger()
  {
    assertDoesNotThrow(() -> d_solver.mkInteger("123"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("1.23"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("1/23"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("12/3"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger(".2"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("2."));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger(""));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("asdf"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("1.2/3"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("."));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("/"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("2/"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("/2"));

    assertDoesNotThrow(() -> d_solver.mkReal("123"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("1.23"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("1/23"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("12/3"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger(".2"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("2."));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger(""));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("asdf"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("1.2/3"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("."));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("/"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("2/"));
    assertThrows(CVCApiException.class, () -> d_solver.mkInteger("/2"));

    int val1 = 1;
    long val2 = -1;
    int val3 = 1;
    long val4 = -1;
    assertDoesNotThrow(() -> d_solver.mkInteger(val1));
    assertDoesNotThrow(() -> d_solver.mkInteger(val2));
    assertDoesNotThrow(() -> d_solver.mkInteger(val3));
    assertDoesNotThrow(() -> d_solver.mkInteger(val4));
    assertDoesNotThrow(() -> d_solver.mkInteger(val4));
  }

  @Test void mkReal()
  {
    assertDoesNotThrow(() -> d_solver.mkReal("123"));
    assertDoesNotThrow(() -> d_solver.mkReal("1.23"));
    assertDoesNotThrow(() -> d_solver.mkReal("1/23"));
    assertDoesNotThrow(() -> d_solver.mkReal("12/3"));
    assertDoesNotThrow(() -> d_solver.mkReal(".2"));
    assertDoesNotThrow(() -> d_solver.mkReal("2."));
    assertThrows(CVCApiException.class, () -> d_solver.mkReal(""));
    assertThrows(CVCApiException.class, () -> d_solver.mkReal("asdf"));
    assertThrows(CVCApiException.class, () -> d_solver.mkReal("1.2/3"));
    assertThrows(CVCApiException.class, () -> d_solver.mkReal("."));
    assertThrows(CVCApiException.class, () -> d_solver.mkReal("/"));
    assertThrows(CVCApiException.class, () -> d_solver.mkReal("2/"));
    assertThrows(CVCApiException.class, () -> d_solver.mkReal("/2"));

    assertDoesNotThrow(() -> d_solver.mkReal("123"));
    assertDoesNotThrow(() -> d_solver.mkReal("1.23"));
    assertDoesNotThrow(() -> d_solver.mkReal("1/23"));
    assertDoesNotThrow(() -> d_solver.mkReal("12/3"));
    assertDoesNotThrow(() -> d_solver.mkReal(".2"));
    assertDoesNotThrow(() -> d_solver.mkReal("2."));
    assertThrows(CVCApiException.class, () -> d_solver.mkReal(""));
    assertThrows(CVCApiException.class, () -> d_solver.mkReal("asdf"));
    assertThrows(CVCApiException.class, () -> d_solver.mkReal("1.2/3"));
    assertThrows(CVCApiException.class, () -> d_solver.mkReal("."));
    assertThrows(CVCApiException.class, () -> d_solver.mkReal("/"));
    assertThrows(CVCApiException.class, () -> d_solver.mkReal("2/"));
    assertThrows(CVCApiException.class, () -> d_solver.mkReal("/2"));

    int val1 = 1;
    long val2 = -1;
    int val3 = 1;
    long val4 = -1;
    assertDoesNotThrow(() -> d_solver.mkReal(val1));
    assertDoesNotThrow(() -> d_solver.mkReal(val2));
    assertDoesNotThrow(() -> d_solver.mkReal(val3));
    assertDoesNotThrow(() -> d_solver.mkReal(val4));
    assertDoesNotThrow(() -> d_solver.mkReal(val4));
    assertDoesNotThrow(() -> d_solver.mkReal(val1, val1));
    assertDoesNotThrow(() -> d_solver.mkReal(val2, val2));
    assertDoesNotThrow(() -> d_solver.mkReal(val3, val3));
    assertDoesNotThrow(() -> d_solver.mkReal(val4, val4));
  }

  @Test void mkRegexpEmpty()
  {
    Sort strSort = d_solver.getStringSort();
    Term s = d_solver.mkConst(strSort, "s");
    assertDoesNotThrow(() -> d_solver.mkTerm(STRING_IN_REGEXP, s, d_solver.mkRegexpEmpty()));
  }

  @Test void mkRegexpSigma()
  {
    Sort strSort = d_solver.getStringSort();
    Term s = d_solver.mkConst(strSort, "s");
    assertDoesNotThrow(() -> d_solver.mkTerm(STRING_IN_REGEXP, s, d_solver.mkRegexpSigma()));
  }

  @Test void mkSepNil()
  {
    assertDoesNotThrow(() -> d_solver.mkSepNil(d_solver.getBooleanSort()));
    assertThrows(CVCApiException.class, () -> d_solver.mkSepNil(d_solver.mkSort()));
    Solver slv = new Solver();
    assertThrows(CVCApiException.class, () -> slv.mkSepNil(d_solver.getIntegerSort()));
  }

  @Test void mkString()
  {
    assertDoesNotThrow(() -> d_solver.mkString(""));
    assertDoesNotThrow(() -> d_solver.mkString("asdfasdf"));
    assertEquals(d_solver.mkString("asdf\\nasdf").toString(), "\"asdf\\u{5c}nasdf\"");
    assertEquals(d_solver.mkString("asdf\\u{005c}nasdf", true).toString(), "\"asdf\\u{5c}nasdf\"");
  }

  @Test void mkChar()
  {
    assertDoesNotThrow(() -> d_solver.mkChar("0123"));
    assertDoesNotThrow(() -> d_solver.mkChar("aA"));
    assertThrows(CVCApiException.class, () -> d_solver.mkChar(""));
    assertThrows(CVCApiException.class, () -> d_solver.mkChar("0g0"));
    assertThrows(CVCApiException.class, () -> d_solver.mkChar("100000"));
    assertEquals(d_solver.mkChar("abc"), d_solver.mkChar("ABC"));
  }

  @Test void mkTerm() throws CVCApiException
  {
    Sort bv32 = d_solver.mkBitVectorSort(32);
    Term a = d_solver.mkConst(bv32, "a");
    Term b = d_solver.mkConst(bv32, "b");
    Term[] v1 = {a, b};
    Term[] v2 = {a, d_solver.mkTerm()};
    Term[] v3 = {a, d_solver.mkTrue()};
    Term[] v4 = {d_solver.mkInteger(1), d_solver.mkInteger(2)};
    Term[] v5 = {d_solver.mkInteger(1), d_solver.mkTerm()};
    Term[] v6 = {};
    Solver slv = new Solver();

    // mkTerm(Kind kind) const
    assertDoesNotThrow(() -> d_solver.mkTerm(PI));
    assertDoesNotThrow(() -> d_solver.mkTerm(REGEXP_EMPTY));
    assertDoesNotThrow(() -> d_solver.mkTerm(REGEXP_SIGMA));
    assertThrows(CVCApiException.class, () -> d_solver.mkTerm(CONST_BITVECTOR));

    // mkTerm(Kind kind, Term child) const
    assertDoesNotThrow(() -> d_solver.mkTerm(NOT, d_solver.mkTrue()));
    assertThrows(CVCApiException.class, () -> d_solver.mkTerm(NOT, d_solver.mkTerm()));
    assertThrows(CVCApiException.class, () -> d_solver.mkTerm(NOT, a));
    assertThrows(CVCApiException.class, () -> slv.mkTerm(NOT, d_solver.mkTrue()));

    // mkTerm(Kind kind, Term child1, Term child2) const
    assertDoesNotThrow(() -> d_solver.mkTerm(EQUAL, a, b));
    assertThrows(CVCApiException.class, () -> d_solver.mkTerm(EQUAL, d_solver.mkTerm(), b));
    assertThrows(CVCApiException.class, () -> d_solver.mkTerm(EQUAL, a, d_solver.mkTerm()));
    assertThrows(CVCApiException.class, () -> d_solver.mkTerm(EQUAL, a, d_solver.mkTrue()));
    assertThrows(CVCApiException.class, () -> slv.mkTerm(EQUAL, a, b));

    // mkTerm(Kind kind, Term child1, Term child2, Term child3) const
    assertDoesNotThrow(
        () -> d_solver.mkTerm(ITE, d_solver.mkTrue(), d_solver.mkTrue(), d_solver.mkTrue()));
    assertThrows(CVCApiException.class,
        () -> d_solver.mkTerm(ITE, d_solver.mkTerm(), d_solver.mkTrue(), d_solver.mkTrue()));
    assertThrows(CVCApiException.class,
        () -> d_solver.mkTerm(ITE, d_solver.mkTrue(), d_solver.mkTerm(), d_solver.mkTrue()));
    assertThrows(CVCApiException.class,
        () -> d_solver.mkTerm(ITE, d_solver.mkTrue(), d_solver.mkTrue(), d_solver.mkTerm()));
    assertThrows(
        CVCApiException.class, () -> d_solver.mkTerm(ITE, d_solver.mkTrue(), d_solver.mkTrue(), b));
    assertThrows(CVCApiException.class,
        () -> slv.mkTerm(ITE, d_solver.mkTrue(), d_solver.mkTrue(), d_solver.mkTrue()));

    // mkTerm(Kind kind, const Term []& children) const
    assertDoesNotThrow(() -> d_solver.mkTerm(EQUAL, v1));
    assertThrows(CVCApiException.class, () -> d_solver.mkTerm(EQUAL, v2));
    assertThrows(CVCApiException.class, () -> d_solver.mkTerm(EQUAL, v3));
    assertThrows(CVCApiException.class, () -> d_solver.mkTerm(DISTINCT, v6));
  }

  @Test void mkTrue()
  {
    assertDoesNotThrow(() -> d_solver.mkTrue());
  }

  @Test void setLogic()
  {
    assertDoesNotThrow(() -> d_solver.setLogic("AUFLIRA"));
    assertThrows(CVCApiException.class, () -> d_solver.setLogic("AF_BV"));
    d_solver.assertFormula(d_solver.mkTrue());
    assertThrows(CVCApiException.class, () -> d_solver.setLogic("AUFLIRA"));
  }
}