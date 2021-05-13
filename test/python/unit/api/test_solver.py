###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Ying Sheng
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

import pytest
import pycvc5
import sys

from pycvc5 import kinds

@pytest.fixture
def solver():
    return pycvc5.Solver()

def test_recoverable_exception(solver):
    solver.setOption("produce-models", "true")
    x = solver.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x).notTerm())
    with pytest.raises(RuntimeError):
        c = solver.getValue(x)

def test_supports_floating_point(solver):
    if solver.supportsFloatingPoint():
        solver.mkRoundingMode(pycvc5.RoundNearestTiesToEven)
    else:
        with pytest.raises(RuntimeError):
            solver.mkRoundingMode(pycvc5.RoundNearestTiesToEven)

def test_getBooleanSort(solver):
    solver.getBooleanSort()

def test_getIntegerSort(solver):
    solver.getIntegerSort()

# TODO
#def test_getNullSort(solver):
#        solver.getNullSort()

def test_getRealSort(solver):
    solver.getRealSort()

def test_getRegExpSort(solver):
    solver.getRegExpSort()

def test_getStringSort(solver):
    solver.getStringSort()

def test_get_rounding_mode_sort(solver):
    if solver.supportsFloatingPoint():
        solver.getRoundingModeSort()
    else:
        with pytest.raises(RuntimeError):
            solver.getRoundingModeSort()

def test_mkArraySort(solver):
    boolSort = solver.getBooleanSort()
    intSort = solver.getIntegerSort()
    realSort = solver.getRealSort()
    bvSort = solver.mkBitVectorSort(32)
    solver.mkArraySort(boolSort, boolSort)
    solver.mkArraySort(intSort, intSort)
    solver.mkArraySort(realSort, realSort)
    solver.mkArraySort(bvSort, bvSort)
    solver.mkArraySort(boolSort, intSort)
    solver.mkArraySort(realSort, bvSort)

    if (solver.supportsFloatingPoint()):
        fpSort = solver.mkFloatingPointSort(3, 5)
        solver.mkArraySort(fpSort, fpSort)
        solver.mkArraySort(bvSort, fpSort)

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkArraySort(boolSort, boolSort)

def test_mkBitVectorSort(solver):
    solver.mkBitVectorSort(32);
    with pytest.raises(RuntimeError):
        solver.mkBitVectorSort(0)

def test_mkFloatingPointSort(solver):
    if solver.supportsFloatingPoint():
        solver.mkFloatingPointSort(4, 8)
        with pytest.raises(RuntimeError):
            solver.mkFloatingPointSort(0, 8)
        with pytest.raises(RuntimeError):
            solver.mkFloatingPointSort(4, 0)
    else:
        with pytest.raises(RuntimeError):
            solver.mkFloatingPointSort(4, 8)

def test_mkDatatypeSort(solver):
    dtypeSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    solver.mkDatatypeSort(dtypeSpec)

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkDatatypeSort(dtypeSpec)

    throwsDtypeSpec = solver.mkDatatypeDecl("list")
    with pytest.raises(RuntimeError):
        solver.mkDatatypeSort(throwsDtypeSpec)

def test_mkDatatypeSorts(solver):
    slv = pycvc5.Solver()
    
    dtypeSpec1 = solver.mkDatatypeDecl("list1")
    cons1 = solver.mkDatatypeConstructorDecl("cons1")
    cons1.addSelector("head1", solver.getIntegerSort())
    dtypeSpec1.addConstructor(cons1)
    nil1 = solver.mkDatatypeConstructorDecl("nil1")
    dtypeSpec1.addConstructor(nil1)

    dtypeSpec2 = solver.mkDatatypeDecl("list2")
    cons2 = solver.mkDatatypeConstructorDecl("cons2")
    cons2.addSelector("head2", solver.getIntegerSort())
    dtypeSpec2.addConstructor(cons2)
    nil2 = solver.mkDatatypeConstructorDecl("nil2")
    dtypeSpec2.addConstructor(nil2)
    
    decls = [dtypeSpec1, dtypeSpec2]
    solver.mkDatatypeSorts(decls, [])

    with pytest.raises(RuntimeError):
        slv.mkDatatypeSorts(decls, [])

    throwsDtypeSpec = solver.mkDatatypeDecl("list")
    throwsDecls = [throwsDtypeSpec]
    with pytest.raises(RuntimeError):
        solver.mkDatatypeSorts(throwsDecls, [])

    # with unresolved sorts
    unresList = solver.mkUninterpretedSort("ulist")
    unresSorts = [unresList]
    ulist = solver.mkDatatypeDecl("ulist")
    ucons = solver.mkDatatypeConstructorDecl("ucons")
    ucons.addSelector("car", unresList)
    ucons.addSelector("cdr", unresList)
    ulist.addConstructor(ucons)
    unil = solver.mkDatatypeConstructorDecl("unil")
    ulist.addConstructor(unil)
    udecls = [ulist]

    solver.mkDatatypeSorts(udecls, unresSorts)
    with pytest.raises(RuntimeError):
        slv.mkDatatypeSorts(udecls, unresSorts)

def test_mkFunctionSort(solver):
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
            solver.getIntegerSort())

    # function arguments are allowed
    solver.mkFunctionSort(funSort, solver.getIntegerSort())

    # non-first-class arguments are not allowed
    reSort = solver.getRegExpSort()
    with pytest.raises(RuntimeError):
        solver.mkFunctionSort(reSort, solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        solver.mkFunctionSort(solver.getIntegerSort(), funSort)

    solver.mkFunctionSort([solver.mkUninterpretedSort("u"),\
            solver.getIntegerSort()],\
            solver.getIntegerSort())
    funSort2 = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
            solver.getIntegerSort())

    # function arguments are allowed
    solver.mkFunctionSort([funSort2, solver.mkUninterpretedSort("u")],\
            solver.getIntegerSort())

    with pytest.raises(RuntimeError):
        solver.mkFunctionSort([solver.getIntegerSort(),\
                solver.mkUninterpretedSort("u")],\
                funSort2)
    
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkFunctionSort(solver.mkUninterpretedSort("u"),\
                solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        slv.mkFunctionSort(slv.mkUninterpretedSort("u"),\
                solver.getIntegerSort())
    sorts1 = [solver.getBooleanSort(),\
            slv.getIntegerSort(),\
            solver.getIntegerSort()]
    sorts2 = [slv.getBooleanSort(), slv.getIntegerSort()]
    slv.mkFunctionSort(sorts2, slv.getIntegerSort())
    with pytest.raises(RuntimeError):
        slv.mkFunctionSort(sorts1, slv.getIntegerSort())
    with pytest.raises(RuntimeError):
        slv.mkFunctionSort(sorts2, solver.getIntegerSort())

def test_mkParamSort(solver):
    solver.mkParamSort("T")
    solver.mkParamSort("")

def test_mkPredicateSort(solver):
    solver.mkPredicateSort([solver.getIntegerSort()])
    with pytest.raises(RuntimeError):
        solver.mkPredicateSort([])

    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
            solver.getIntegerSort())
    # functions as arguments are allowed
    solver.mkPredicateSort([solver.getIntegerSort(), funSort])

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkPredicateSort([solver.getIntegerSort()])

def test_mkRecordSort(solver):
    fields = [("b", solver.getBooleanSort()),\
              ("bv", solver.mkBitVectorSort(8)),\
              ("i", solver.getIntegerSort())]
    empty = []
    solver.mkRecordSort(fields)
    solver.mkRecordSort(empty)
    recSort = solver.mkRecordSort(fields)
    recSort.getDatatype()

def test_mkSetSort(solver):
    solver.mkSetSort(solver.getBooleanSort())
    solver.mkSetSort(solver.getIntegerSort())
    solver.mkSetSort(solver.mkBitVectorSort(4))
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkSetSort(solver.mkBitVectorSort(4))

# TODO
#def test_mkBagSort(solver):
#    solver.mkBagSort(solver.getBooleanSort())
#    solver.mkBadSort(solver.getIntegerSort())
#    solver.mkBagSort(solver.mkBitVectorSort(4))
#    slv = pycvc5.Solver()
#    with pytest.raises(RuntimeError):
#        slv.mkBagSort(solver.mkBitVectorSort(4))

def test_mkSequenceSort(solver):
    solver.mkSequenceSort(solver.getBooleanSort())
    solver.mkSequenceSort(\
            solver.mkSequenceSort(solver.getIntegerSort()))
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkSequenceSort(solver.getIntegerSort())

def test_mkUninterpretedSort(solver):
    solver.mkUninterpretedSort("u")
    solver.mkUninterpretedSort("")

def test_mkSortConstructorSort(solver):
    solver.mkSortConstructorSort("s", 2)
    solver.mkSortConstructorSort("", 2)
    with pytest.raises(RuntimeError):
        solver.mkSortConstructorSort("", 0)

def test_mkTupleSort(solver):
    solver.mkTupleSort([solver.getIntegerSort()])
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
                                    solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        solver.mkTupleSort([solver.getIntegerSort(), funSort])

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkTupleSort([solver.getIntegerSort()])

def test_mkBitVector(solver):
    size0, size1, size2 = 0, 8, 32
    val1, val2 = 2, 2
    solver.mkBitVector(size1, val1)
    solver.mkBitVector(size2, val2)
    solver.mkBitVector("1010", 2)
    solver.mkBitVector("1010", 10)
    solver.mkBitVector("1234", 10)
    solver.mkBitVector("1010", 16)
    solver.mkBitVector("a09f", 16)
    #solver.mkBitVector(8, "-127", 10)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(size0, val1)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(size0, val2)
    with pytest.raises(RuntimeError):
        solver.mkBitVector("", 2)
    with pytest.raises(RuntimeError):
        solver.mkBitVector("10", 3)
    with pytest.raises(RuntimeError):
        solver.mkBitVector("20", 2)
#    with pytest.raises(RuntimeError):
#        solver.mkBitVector(8, "101010101", 2)
#    with pytest.raises(RuntimeError):
#        solver.mkBitVector(8, "-256", 10)
    assert solver.mkBitVector("1010", 2) == solver.mkBitVector("10", 10)
    assert solver.mkBitVector("1010", 2) == solver.mkBitVector("a", 16)
#    assert solver.mkBitVector(8, "01010101", 2).toString() == "#b01010101"
#    assert solver.mkBitVector(8, "F", 16).toString() == "#b00001111"
#    assert solver.mkBitVector(8, "-1", 10) ==\
#           solver.mkBitVector(8, "FF", 16)

def test_mkVar(solver):
    boolSort = solver.getBooleanSort()
    intSort = solver.getIntegerSort()
    funSort = solver.mkFunctionSort(intSort, boolSort)
    solver.mkVar(boolSort)
    solver.mkVar(funSort)
    solver.mkVar(boolSort, "b")
    solver.mkVar(funSort, "")
    with pytest.raises(RuntimeError):
        solver.mkVar(pycvc5.Sort(solver))
#    with pytest.raises(RuntimeError):
#        solver.mkVar(Sort(solver), "a")
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkVar(boolSort, "x")

def test_mkBoolean(solver):
    solver.mkBoolean(True)
    solver.mkBoolean(False)

def test_mkRoundingMode(solver):
    if solver.supportsFloatingPoint():
        solver.mkRoundingMode(pycvc5.RoundTowardZero)
#    else:
#        with pytest.raises(RuntimeError):
#            solver.mkRoundingMode(__rounding_modes.ROUND_TOWARD_ZERO)

def test_mkUninterpretedConst(solver):
    solver.mkUninterpretedConst(solver.getBooleanSort(), 1)
    with pytest.raises(RuntimeError):
        solver.mkUninterpretedConst(pycvc5.Sort(solver), 1)
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkUninterpretedConst(solver.getBooleanSort(), 1)

def test_mkAbstractValue(solver):
    solver.mkAbstractValue("1")
    with pytest.raises(ValueError):
        solver.mkAbstractValue("0")
#    with pytest.raises(RuntimeError):
#        solver.mkAbstractValue("-1")
#    with pytest.raises(RuntimeError):
#        solver.mkAbstractValue("1.2")
#    with pytest.raises(RuntimeError):
#        solver.mkAbstractValue("1/2")
#    with pytest.raises(RuntimeError):
#        solver.mkAbstractValue("asdf")

    solver.mkAbstractValue(1)
    solver.mkAbstractValue(1)
    solver.mkAbstractValue(1)
    solver.mkAbstractValue(1)
#    solver.mkAbstractValue(-1)
#    solver.mkAbstractValue(-1)
#    with pytest.raises(RuntimeError):
#        solver.mkAbstractValue(0)

def test_mkFloatingPoint(solver):
    t1 = solver.mkBitVector(8)
    t2 = solver.mkBitVector(4)
    t3 = solver.mkInteger(2)
    if (solver.supportsFloatingPoint()):
        solver.mkFloatingPoint(3, 5, t1)
    else:
        with pytest.raises(RuntimeError):  
            solver.mkFloatingPoint(3, 5, t1)

    with pytest.raises(RuntimeError): 
        solver.mkFloatingPoint(0, 5, pycvc5.Term(solver))
    with pytest.raises(RuntimeError): 
        solver.mkFloatingPoint(0, 5, t1)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(3, 0, t1)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(3, 5, t2)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(3, 5, t2)

    if (solver.supportsFloatingPoint()):
        slv = pycvc5.Solver()
        with pytest.raises(RuntimeError):
            slv.mkFloatingPoint(3, 5, t1)

def test_mkEmptySet(solver):
    slv = pycvc5.Solver()
    s = solver.mkSetSort(solver.getBooleanSort())
#    solver.mkEmptySet(Sort())
    solver.mkEmptySet(s)
    with pytest.raises(RuntimeError):
        solver.mkEmptySet(solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        slv.mkEmptySet(s)

# TODO
def test_mkEmptyBag(solver):
    slv = pycvc5.Solver()
    s = solver.mkBagSort(solver.getBooleanSort())
#    solver.mkEmptyBag(Sort())
#    solver.mkEmptyBag(s)
#    with pytest.raises(RuntimeError):
#        solver.mkEmptyBag(solver.getBooleanSort())
#    with pytest.raises(RuntimeError):
#        slv.mkEmptyBag(s)

def test_mkEmptySequence(solver):
    slv = pycvc5.Solver()
    s = solver.mkSequenceSort(solver.getBooleanSort())
    solver.mkEmptySequence(s)
    solver.mkEmptySequence(solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        slv.mkEmptySequence(s)

def test_mkFalse(solver):
    solver.mkFalse()
    solver.mkFalse()

def test_mkNaN(solver):
    if (solver.supportsFloatingPoint()):
        solver.mkNaN(3, 5)
    else:
        with pytest.raises(RuntimeError):
            solver.mkNaN(3, 5)

def test_mkNegZero(solver):
    if (solver.supportsFloatingPoint()):
        solver.mkNegZero(3, 5)
    else:
        with pytest.raises(RuntimeError):
            solver.mkNegZero(3, 5)

def test_mkNegInf(solver):
    if (solver.supportsFloatingPoint()):
        solver.mkNegInf(3, 5)
    else:
        with pytest.raises(RuntimeError):
            solver.mkNegInf(3, 5)

def test_mkPosInf(solver):
    if (solver.supportsFloatingPoint()):
        solver.mkPosInf(3, 5)
    else:
        with pytest.raises(RuntimeError):
            solver.mkPosInf(3, 5)

def test_mkPosZero(solver):
    if (solver.supportsFloatingPoint()):
        solver.mkPosZero(3, 5)
    else:
        with pytest.raises(RuntimeError):
            solver.mkPosZero(3, 5)

def test_mkOp(solver):
    # mkOp(Kind kind, Kind k)
    with pytest.raises(RuntimeError):
        solver.mkOp(kinds.BVExtract, kinds.Equal)
#
#    # mkOp(Kind kind, const std::string& arg)
#    solver.mkOp(DIVISIBLE, "2147483648")
#    with pytest.raises(RuntimeError):
#        solver.mkOp(BITVECTOR_EXTRACT, "asdf")
#
#    # mkOp(Kind kind, uint32_t arg)
#    solver.mkOp(DIVISIBLE, 1)
#    solver.mkOp(BITVECTOR_ROTATE_LEFT, 1)
#    solver.mkOp(BITVECTOR_ROTATE_RIGHT, 1)
#    with pytest.raises(RuntimeError):
#        solver.mkOp(BITVECTOR_EXTRACT, 1)
#
#    # mkOp(Kind kind, uint32_t arg1, uint32_t arg2)
#    solver.mkOp(BITVECTOR_EXTRACT, 1, 1)
#    with pytest.raises(RuntimeError):
#        solver.mkOp(DIVISIBLE, 1, 2)
#
#    # mkOp(Kind kind, std::vector<uint32_t> args)
#    args = [1, 2, 2]
#    solver.mkOp(TUPLE_PROJECT, args)

def test_mkPi(solver):
    solver.mkPi()

def test_mkInteger(solver):
    solver.mkInteger("123")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1.23")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1/23")
    with pytest.raises(RuntimeError):
        solver.mkInteger("12/3")
    with pytest.raises(RuntimeError):
        solver.mkInteger(".2")
    with pytest.raises(RuntimeError):
        solver.mkInteger("2.")
    with pytest.raises(RuntimeError):
        solver.mkInteger("")
    with pytest.raises(RuntimeError):
        solver.mkInteger("asdf")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1.2/3")
    with pytest.raises(RuntimeError):
        solver.mkInteger(".")
    with pytest.raises(RuntimeError):
        solver.mkInteger("/")
    with pytest.raises(RuntimeError):
        solver.mkInteger("2/")
    with pytest.raises(RuntimeError):
        solver.mkInteger("/2")

    solver.mkReal("123")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1.23")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1/23")
    with pytest.raises(RuntimeError):
        solver.mkInteger("12/3")
    with pytest.raises(RuntimeError):
        solver.mkInteger(".2")
    with pytest.raises(RuntimeError):
        solver.mkInteger("2.")
    with pytest.raises(RuntimeError):
        solver.mkInteger("")
    with pytest.raises(RuntimeError):
        solver.mkInteger("asdf")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1.2/3")
    with pytest.raises(RuntimeError):
        solver.mkInteger(".")
    with pytest.raises(RuntimeError):
        solver.mkInteger("/")
    with pytest.raises(RuntimeError):
        solver.mkInteger("2/")
    with pytest.raises(RuntimeError):
        solver.mkInteger("/2")

    val1 = 1
    val2 = -1
    val3 = 1
    val4 = -1
    solver.mkInteger(val1)
    solver.mkInteger(val2)
    solver.mkInteger(val3)
    solver.mkInteger(val4)
    solver.mkInteger(val4)

def test_mkReal(solver):
    solver.mkReal("123")
    solver.mkReal("1.23")
    solver.mkReal("1/23")
    solver.mkReal("12/3")
    solver.mkReal(".2")
    solver.mkReal("2.")
    with pytest.raises(RuntimeError):
        solver.mkReal("")
    with pytest.raises(RuntimeError):
        solver.mkReal("asdf")
    with pytest.raises(RuntimeError):
        solver.mkReal("1.2/3")
    with pytest.raises(RuntimeError):
        solver.mkReal(".")
    with pytest.raises(RuntimeError):
        solver.mkReal("/")
    with pytest.raises(RuntimeError):
        solver.mkReal("2/")
    with pytest.raises(RuntimeError):
        solver.mkReal("/2")

    solver.mkReal("123")
    solver.mkReal("1.23")
    solver.mkReal("1/23")
    solver.mkReal("12/3")
    solver.mkReal(".2")
    solver.mkReal("2.")
    with pytest.raises(RuntimeError):
        solver.mkReal("")
    with pytest.raises(RuntimeError):
        solver.mkReal("asdf")
    with pytest.raises(RuntimeError):
        solver.mkReal("1.2/3")
    with pytest.raises(RuntimeError):
        solver.mkReal(".")
    with pytest.raises(RuntimeError):
        solver.mkReal("/")
    with pytest.raises(RuntimeError):
        solver.mkReal("2/")
    with pytest.raises(RuntimeError):
        solver.mkReal("/2")

    val1 = 1;
    val2 = -1;
    val3 = 1;
    val4 = -1;
    solver.mkReal(val1)
    solver.mkReal(val2)
    solver.mkReal(val3)
    solver.mkReal(val4)
    solver.mkReal(val4)
    solver.mkReal(val1, val1)
    solver.mkReal(val2, val2)
    solver.mkReal(val3, val3)
    solver.mkReal(val4, val4)

def test_mkRegexpEmpty(solver):
    strSort = solver.getStringSort()
    s = solver.mkConst(strSort, "s")
#    solver.mkTerm(STRING_IN_REGEXP, s, solver.mkRegexpEmpty())

def test_mkRegexpSigma(solver):
    strSort = solver.getStringSort()
    s = solver.mkConst(strSort, "s")
#    solver.mkTerm(STRING_IN_REGEXP, s, solver.mkRegexpSigma())

def test_mkSepNil(solver):
    solver.mkSepNil(solver.getBooleanSort())
 #   solver.mkSepNil(Sort())
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkSepNil(solver.getIntegerSort())

def test_mkString(solver):
    solver.mkString("")
    solver.mkString("asdfasdf")
    print(solver.mkString("asdf\\nasdf"))
    print("\"asdf\\u{5c}nasdf\"")
    assert str(solver.mkString("asdf\\nasdf")) == \
            "\"asdf\\u{5c}nasdf\""
#    assert str(solver.mkString("asdf\\u{005c}nasdf", True)) == \
#            "\"asdf\\u{5c}nasdf\""

#def test_mk_char(solver):
#    solver.mkChar("0123")
#    solver.mkChar("aA")
#    with pytest.raises(RuntimeError):
#        solver.mkChar("")
#    with pytest.raises(RuntimeError):
#        solver.mkChar("0g0")
#    with pytest.raises(RuntimeError):
#        solver.mkChar("100000")
#    assert solver.mkChar("abc") == solver.mkChar("ABC")

def test_mkTerm(solver):
    bv32 = solver.mkBitVectorSort(32)
    a = solver.mkConst(bv32, "a")
    b = solver.mkConst(bv32, "b")
    v1 = [a, b]
#    v2 = [a, Term(solver)]
    v3 = [a, solver.mkTrue()]
    v4 = [solver.mkInteger(1), solver.mkInteger(2)]
#    v5 = [solver.mkInteger(1), Term()]
    v6 = []
    slv = pycvc5.Solver()

    # mkTerm(Kind kind) const
#    solver.mkTerm(kinds.PI)
#    solver.mkTerm(REGEXP_EMPTY)
#    solver.mkTerm(REGEXP_SIGMA)
#    with pytest.raises(RuntimeError):
#        solver.mkTerm(CONST_BITVECTOR)

    # mkTerm(Kind kind, Term child) const
#    solver.mkTerm(NOT, solver.mkTrue())
#    with pytest.raises(RuntimeError):
#        solver.mkTerm(NOT, Term())
#    with pytest.raises(RuntimeError):
#        solver.mkTerm(NOT, a)
#    with pytest.raises(RuntimeError):
#        slv.mkTerm(NOT, solver.mkTrue())

    # mkTerm(Kind kind, Term child1, Term child2) const
#    solver.mkTerm(EQUAL, a, b)
#    with pytest.raises(RuntimeError):
#        solver.mkTerm(EQUAL, Term(), b)
#    with pytest.raises(RuntimeError):
#        solver.mkTerm(EQUAL, a, Term())
#    with pytest.raises(RuntimeError):
#        solver.mkTerm(EQUAL, a, solver.mkTrue())
#    with pytest.raises(RuntimeError):
#        slv.mkTerm(EQUAL, a, b)

    # mkTerm(Kind kind, Term child1, Term child2, Term child3) const
#    solver.mkTerm(\
#        ITE, solver.mkTrue(), solver.mkTrue(), solver.mkTrue())
#    with pytest.raises(RuntimeError):
#        solver.mkTerm(ITE, Term(), solver.mkTrue(), solver.mkTrue())
#    with pytest.raises(RuntimeError):
#        solver.mkTerm(ITE, solver.mkTrue(), Term(), solver.mkTrue())
#    with pytest.raises(RuntimeError):
#        solver.mkTerm(ITE, solver.mkTrue(), solver.mkTrue(), Term())
#    with pytest.raises(RuntimeError):
#        solver.mkTerm(ITE, solver.mkTrue(), solver.mkTrue(), b)
#    with pytest.raises(RuntimeError):
#        slv.mkTerm(ITE, solver.mkTrue(), solver.mkTrue(), solver.mkTrue())

   # mkTerm(Kind kind, const std::vector<Term>& children) const
#    solver.mkTerm(EQUAL, v1)
#    with pytest.raises(RuntimeError):
#        solver.mkTerm(EQUAL, v2)
#    with pytest.raises(RuntimeError):
#        solver.mkTerm(EQUAL, v3)
#    with pytest.raises(RuntimeError):
#        solver.mkTerm(DISTINCT, v6)

#TEST_F(TestApiBlackSolver, mkTermFromOp)
#{
#  Sort bv32 = d_solver.mkBitVectorSort(32);
#  Term a = d_solver.mkConst(bv32, "a");
#  Term b = d_solver.mkConst(bv32, "b");
#  std::vector<Term> v1 = {d_solver.mkInteger(1), d_solver.mkInteger(2)};
#  std::vector<Term> v2 = {d_solver.mkInteger(1), Term()};
#  std::vector<Term> v3 = {};
#  std::vector<Term> v4 = {d_solver.mkInteger(5)};
#  Solver slv;
#
#  // simple operator terms
#  Op opterm1 = d_solver.mkOp(BITVECTOR_EXTRACT, 2, 1);
#  Op opterm2 = d_solver.mkOp(DIVISIBLE, 1);
#
#  // list datatype
#  Sort sort = d_solver.mkParamSort("T");
#  DatatypeDecl listDecl = d_solver.mkDatatypeDecl("paramlist", sort);
#  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
#  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
#  cons.addSelector("head", sort);
#  cons.addSelectorSelf("tail");
#  listDecl.addConstructor(cons);
#  listDecl.addConstructor(nil);
#  Sort listSort = d_solver.mkDatatypeSort(listDecl);
#  Sort intListSort =
#      listSort.instantiate(std::vector<Sort>{d_solver.getIntegerSort()});
#  Term c = d_solver.mkConst(intListSort, "c");
#  Datatype list = listSort.getDatatype();
#
#  // list datatype constructor and selector operator terms
#  Term consTerm1 = list.getConstructorTerm("cons");
#  Term consTerm2 = list.getConstructor("cons").getConstructorTerm();
#  Term nilTerm1 = list.getConstructorTerm("nil");
#  Term nilTerm2 = list.getConstructor("nil").getConstructorTerm();
#  Term headTerm1 = list["cons"].getSelectorTerm("head");
#  Term headTerm2 = list["cons"].getSelector("head").getSelectorTerm();
#  Term tailTerm1 = list["cons"].getSelectorTerm("tail");
#  Term tailTerm2 = list["cons"]["tail"].getSelectorTerm();
#
#  // mkTerm(Op op, Term term) const
#  ASSERT_NO_THROW(d_solver.mkTerm(APPLY_CONSTRUCTOR, nilTerm1));
#  ASSERT_NO_THROW(d_solver.mkTerm(APPLY_CONSTRUCTOR, nilTerm2));
#  ASSERT_THROW(d_solver.mkTerm(APPLY_SELECTOR, nilTerm1), CVC5ApiException);
#  ASSERT_THROW(d_solver.mkTerm(APPLY_SELECTOR, consTerm1), CVC5ApiException);
#  ASSERT_THROW(d_solver.mkTerm(APPLY_CONSTRUCTOR, consTerm2), CVC5ApiException);
#  ASSERT_THROW(d_solver.mkTerm(opterm1), CVC5ApiException);
#  ASSERT_THROW(d_solver.mkTerm(APPLY_SELECTOR, headTerm1), CVC5ApiException);
#  ASSERT_THROW(d_solver.mkTerm(opterm1), CVC5ApiException);
#  ASSERT_THROW(slv.mkTerm(APPLY_CONSTRUCTOR, nilTerm1), CVC5ApiException);
#
#  // mkTerm(Op op, Term child) const
#  ASSERT_NO_THROW(d_solver.mkTerm(opterm1, a));
#  ASSERT_NO_THROW(d_solver.mkTerm(opterm2, d_solver.mkInteger(1)));
#  ASSERT_NO_THROW(d_solver.mkTerm(APPLY_SELECTOR, headTerm1, c));
#  ASSERT_NO_THROW(d_solver.mkTerm(APPLY_SELECTOR, tailTerm2, c));
#  ASSERT_THROW(d_solver.mkTerm(opterm2, a), CVC5ApiException);
#  ASSERT_THROW(d_solver.mkTerm(opterm1, Term()), CVC5ApiException);
#  ASSERT_THROW(
#      d_solver.mkTerm(APPLY_CONSTRUCTOR, consTerm1, d_solver.mkInteger(0)),
#      CVC5ApiException);
#  ASSERT_THROW(slv.mkTerm(opterm1, a), CVC5ApiException);
#
#  // mkTerm(Op op, Term child1, Term child2) const
#  ASSERT_NO_THROW(
#      d_solver.mkTerm(APPLY_CONSTRUCTOR,
#                      consTerm1,
#                      d_solver.mkInteger(0),
#                      d_solver.mkTerm(APPLY_CONSTRUCTOR, nilTerm1)));
#  ASSERT_THROW(
#      d_solver.mkTerm(opterm2, d_solver.mkInteger(1), d_solver.mkInteger(2)),
#      CVC5ApiException);
#  ASSERT_THROW(d_solver.mkTerm(opterm1, a, b), CVC5ApiException);
#  ASSERT_THROW(d_solver.mkTerm(opterm2, d_solver.mkInteger(1), Term()),
#               CVC5ApiException);
#  ASSERT_THROW(d_solver.mkTerm(opterm2, Term(), d_solver.mkInteger(1)),
#               CVC5ApiException);
#  ASSERT_THROW(slv.mkTerm(APPLY_CONSTRUCTOR,
#                          consTerm1,
#                          d_solver.mkInteger(0),
#                          d_solver.mkTerm(APPLY_CONSTRUCTOR, nilTerm1)),
#               CVC5ApiException);
#
#  // mkTerm(Op op, Term child1, Term child2, Term child3) const
#  ASSERT_THROW(d_solver.mkTerm(opterm1, a, b, a), CVC5ApiException);
#  ASSERT_THROW(
#      d_solver.mkTerm(
#          opterm2, d_solver.mkInteger(1), d_solver.mkInteger(1), Term()),
#      CVC5ApiException);
#
#  // mkTerm(Op op, const std::vector<Term>& children) const
#  ASSERT_NO_THROW(d_solver.mkTerm(opterm2, v4));
#  ASSERT_THROW(d_solver.mkTerm(opterm2, v1), CVC5ApiException);
#  ASSERT_THROW(d_solver.mkTerm(opterm2, v2), CVC5ApiException);
#  ASSERT_THROW(d_solver.mkTerm(opterm2, v3), CVC5ApiException);
#  ASSERT_THROW(slv.mkTerm(opterm2, v4), CVC5ApiException);
#}

def test_mkTrue(solver):
    solver.mkTrue()
    solver.mkTrue()

#def test_mkTuple(solver):
#    solver.mkTuple([solver.mkBitVectorSort(3)],\
#                   [solver.mkBitVector("101", 2)])
#  ASSERT_NO_THROW(
#      d_solver.mkTuple({d_solver.getRealSort()}, {d_solver.mkInteger("5")}));
#
#  ASSERT_THROW(d_solver.mkTuple({}, {d_solver.mkBitVector("101", 2)}),
#               CVC5ApiException);
#  ASSERT_THROW(d_solver.mkTuple({d_solver.mkBitVectorSort(4)},
#                                {d_solver.mkBitVector("101", 2)}),
#               CVC5ApiException);
#  ASSERT_THROW(
#      d_solver.mkTuple({d_solver.getIntegerSort()}, {d_solver.mkReal("5.3")}),
#      CVC5ApiException);
#  Solver slv;
#  ASSERT_THROW(
#      slv.mkTuple({d_solver.mkBitVectorSort(3)}, {slv.mkBitVector("101", 2)}),
#      CVC5ApiException);
#  ASSERT_THROW(
#      slv.mkTuple({slv.mkBitVectorSort(3)}, {d_solver.mkBitVector("101", 2)}),
#      CVC5ApiException);

def test_mkUniverseSet(solver):
    solver.mkUniverseSet(solver.getBooleanSort())
#    with pytest.raises(RuntimeError):
#        solver.mkUniverseSet(Sort())
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkUniverseSet(solver.getBooleanSort())

def test_mkConst(solver):
    boolSort = solver.getBooleanSort()
    intSort = solver.getIntegerSort()
    funSort = solver.mkFunctionSort(intSort, boolSort)
    solver.mkConst(boolSort)
    solver.mkConst(funSort)
    solver.mkConst(boolSort, "b")
    solver.mkConst(intSort, "i")
    solver.mkConst(funSort, "f")
    solver.mkConst(funSort, "")
#    with pytest.raises(RuntimeError):
#        solver.mkConst(Sort(solver))
#    with pytest.raises(RuntimeError):
#        solver.mkConst(Sort(), "a")

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkConst(boolSort)

def test_mkConstArray(solver):
    intSort = solver.getIntegerSort()
    arrSort = solver.mkArraySort(intSort, intSort)
    zero = solver.mkInteger(0)
    constArr = solver.mkConstArray(arrSort, zero)

    solver.mkConstArray(arrSort, zero)
#    with pytest.raises(RuntimeError):
#        solver.mkConstArray(Sort(solver), zero)
#    with pytest.raises(RuntimeError):
#        solver.mkConstArray(arrSort, Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkConstArray(arrSort, solver.mkBitVector(1, 1))
    with pytest.raises(RuntimeError):
        solver.mkConstArray(intSort, zero)
    slv = pycvc5.Solver()
    zero2 = slv.mkInteger(0)
    arrSort2 = slv.mkArraySort(slv.getIntegerSort(), slv.getIntegerSort())
    with pytest.raises(RuntimeError):
        slv.mkConstArray(arrSort2, zero)
    with pytest.raises(RuntimeError):
        slv.mkConstArray(arrSort, zero2)

def test_declareDatatype(solver):
    nil = solver.mkDatatypeConstructorDecl("nil")
    ctors1 = [nil]
    solver.declareDatatype("a", ctors1)
    cons = solver.mkDatatypeConstructorDecl("cons")
    nil2 = solver.mkDatatypeConstructorDecl("nil")
    ctors2 = [cons, nil2]
    solver.declareDatatype("b", ctors2)
    cons2 = solver.mkDatatypeConstructorDecl("cons")
    nil3 = solver.mkDatatypeConstructorDecl("nil")
    ctors3 = [cons2, nil3]
    solver.declareDatatype("", ctors3)
    ctors4 = []
#    with pytest.raises(RuntimeError):
#        solver.declareDatatype("c", ctors4)
#    with pytest.raises(RuntimeError):
#        solver.declareDatatype("", ctors4)
    slv = pycvc5.Solver()
#    with pytest.raises(RuntimeError):
#        slv.declareDatatype("a", ctors1)

def test_declareFun(solver):
    bvSort = solver.mkBitVectorSort(32)
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
                                    solver.getIntegerSort())
    solver.declareFun("f1", [], bvSort)
    solver.declareFun("f3", [bvSort, solver.getIntegerSort()], bvSort)
    with pytest.raises(RuntimeError):
        solver.declareFun("f2", [], funSort)
    # functions as arguments is allowed
    solver.declareFun("f4", [bvSort, funSort], bvSort)
    with pytest.raises(RuntimeError):
        solver.declareFun("f5", [bvSort, bvSort], funSort)
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.declareFun("f1", [], bvSort)

def test_declareSort(solver):
    solver.declareSort("s", 0)
    solver.declareSort("s", 2)
    solver.declareSort("", 2)

def test_defineSort(solver):
    sortVar0 = solver.mkParamSort("T0")
    sortVar1 = solver.mkParamSort("T1")
    intSort = solver.getIntegerSort()
    realSort = solver.getRealSort()
    arraySort0 = solver.mkArraySort(sortVar0, sortVar0)
    arraySort1 = solver.mkArraySort(sortVar0, sortVar1)
    # Now create instantiations of the defined sorts
#    arraySort0.substitute(sortVar0, intSort)
#    arraySort1.substitute([sortVar0, sortVar1], [intSort, realSort])

def test_defineFun(solver):
    bvSort = solver.mkBitVectorSort(32)
    funSort1 = solver.mkFunctionSort([bvSort, bvSort], bvSort)
    funSort2 = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
                                     solver.getIntegerSort())
    b1 = solver.mkVar(bvSort, "b1")
    b11 = solver.mkVar(bvSort, "b1")
    b2 = solver.mkVar(solver.getIntegerSort(), "b2")
    b3 = solver.mkVar(funSort2, "b3")
    v1 = solver.mkConst(bvSort, "v1")
    v2 = solver.mkConst(solver.getIntegerSort(), "v2")
    v3 = solver.mkConst(funSort2, "v3")
    f1 = solver.mkConst(funSort1, "f1")
    f2 = solver.mkConst(funSort2, "f2")
    f3 = solver.mkConst(bvSort, "f3")
    solver.defineFun("f", [], bvSort, v1)
    solver.defineFun("ff", [b1, b2], bvSort, v1)
    solver.defineFun(f1, [b1, b11], v1)
    with pytest.raises(RuntimeError):
        solver.defineFun("ff", [v1, b2], bvSort, v1)
    with pytest.raises(RuntimeError):
        solver.defineFun("fff", [b1], bvSort, v3)
    with pytest.raises(RuntimeError):
        solver.defineFun("ffff", [b1], funSort2, v3)
    # b3 has function sort, which is allowed as an argument
    solver.defineFun("fffff", [b1, b3], bvSort, v1)
    with pytest.raises(RuntimeError):
        solver.defineFun(f1, [v1, b11], v1)
    with pytest.raises(RuntimeError):
        solver.defineFun(f1, [b1], v1)
    with pytest.raises(RuntimeError):
        solver.defineFun(f1, [b1, b11], v2)
    with pytest.raises(RuntimeError):
        solver.defineFun(f1, [b1, b11], v3)
    with pytest.raises(RuntimeError):
        solver.defineFun(f2, [b1], v2)
    with pytest.raises(RuntimeError):
        solver.defineFun(f3, [b1], v1)

    slv = pycvc5.Solver()
    bvSort2 = slv.mkBitVectorSort(32)
    v12 = slv.mkConst(bvSort2, "v1")
    b12 = slv.mkVar(bvSort2, "b1")
    b22 = slv.mkVar(slv.getIntegerSort(), "b2")
    with pytest.raises(RuntimeError):
        slv.defineFun("f", [], bvSort, v12)
    with pytest.raises(RuntimeError):
        slv.defineFun("f", [], bvSort2, v1)
    with pytest.raises(RuntimeError):
        slv.defineFun("ff", [b1, b22], bvSort2, v12)
    with pytest.raises(RuntimeError):
        slv.defineFun("ff", [b12, b2], bvSort2, v12)
    with pytest.raises(RuntimeError):
        slv.defineFun("ff", [b12, b22], bvSort, v12)
    with pytest.raises(RuntimeError):
        slv.defineFun("ff", [b12, b22], bvSort2, v1)

def test_defineFunGlobal(solver):
    bSort = solver.getBooleanSort()
    fSort = solver.mkFunctionSort(bSort, bSort)

    bTrue = solver.mkBoolean(True)
    # (define-fun f () Bool true)
    f = solver.defineFun("f", [], bSort, bTrue, True)
    b = solver.mkVar(bSort, "b")
    gSym = solver.mkConst(fSort, "g")
    # (define-fun g (b Bool) Bool b)
#    g = solver.defineFun(gSym, [b], b, True)

    # (assert (or (not f) (not (g true))))
#    solver.assertFormula(solver.mkTerm(\
#      OR, f.notTerm(), solver.mkTerm(APPLY_UF, g, bTrue).notTerm()))
#    assert solver.checkSat().isUnsat()
#  d_solver.resetAssertions();
#  // (assert (or (not f) (not (g true))))
#  d_solver.assertFormula(d_solver.mkTerm(
#      OR, f.notTerm(), d_solver.mkTerm(APPLY_UF, g, bTrue).notTerm()));
#  ASSERT_TRUE(d_solver.checkSat().isUnsat());
