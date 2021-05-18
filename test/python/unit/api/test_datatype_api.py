###############################################################################
# Top contributors (to current version):
#   Yoni Zohar
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
from pycvc5 import kinds
from pycvc5 import Sort, Term, DatatypeDecl


@pytest.fixture
def solver():
    return pycvc5.Solver()


def test_mk_datatype_sort(solver):
    dtypeSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    listSort = solver.mkDatatypeSort(dtypeSpec)
    d = listSort.getDatatype()
    consConstr = d[0]
    nilConstr = d[1]
    with pytest.raises(RuntimeError):
        d[2]
    consConstr.getConstructorTerm()
    nilConstr.getConstructorTerm()


def test_mk_datatype_sorts(solver):
    # Create two mutual datatypes corresponding to this definition
    # block:
    #
    #   DATATYPE
    #     tree = node(left: tree, right: tree) | leaf(data: list),
    #     list = cons(car: tree, cdr: list) | nil
    #   END
    #

    #Make unresolved types as placeholders
    unresTypes = set([])
    unresTree = solver.mkUninterpretedSort("tree")
    unresList = solver.mkUninterpretedSort("list")
    unresTypes.add(unresTree)
    unresTypes.add(unresList)

    tree = solver.mkDatatypeDecl("tree")
    node = solver.mkDatatypeConstructorDecl("node")
    node.addSelector("left", unresTree)
    node.addSelector("right", unresTree)
    tree.addConstructor(node)

    leaf = solver.mkDatatypeConstructorDecl("leaf")
    leaf.addSelector("data", unresList)
    tree.addConstructor(leaf)

    llist = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("car", unresTree)
    cons.addSelector("cdr", unresTree)
    llist.addConstructor(cons)

    nil = solver.mkDatatypeConstructorDecl("nil")
    llist.addConstructor(nil)

    dtdecls = []
    dtdecls.append(tree)
    dtdecls.append(llist)
    dtsorts = []
    dtsorts = solver.mkDatatypeSorts(dtdecls, unresTypes)
    assert len(dtsorts) == len(dtdecls)
    for i in range(0, len(dtdecls)):
        assert dtsorts[i].isDatatype()
        assert not dtsorts[i].getDatatype().isFinite()
    # verify the resolution was correct
    dtTree = dtsorts[0].getDatatype()
    dtcTreeNode = dtTree[0]
    assert dtcTreeNode.getName() == "node"
    dtsTreeNodeLeft = dtcTreeNode[0]
    assert dtsTreeNodeLeft.getName() == "left"
    # argument type should have resolved to be recursive
    assert dtsTreeNodeLeft.getRangeSort().isDatatype()
    assert dtsTreeNodeLeft.getRangeSort() == dtsorts[0]

    # fails due to empty datatype
    dtdeclsBad = []
    emptyD = solver.mkDatatypeDecl("emptyD")
    dtdeclsBad.append(emptyD)


def test_datatype_structs(solver):
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()

    # create datatype sort to test
    dtypeSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", intSort)
    cons.addSelectorSelf("tail")
    nullSort = Sort(solver)
    with pytest.raises(RuntimeError):
        cons.addSelector("null", nullSort)
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    dtypeSort = solver.mkDatatypeSort(dtypeSpec)
    dt = dtypeSort.getDatatype()
    assert not dt.isCodatatype()
    assert not dt.isTuple()
    assert not dt.isRecord()
    assert not dt.isFinite()
    assert dt.isWellFounded()
    # get constructor
    dcons = dt[0]
    consTerm = dcons.getConstructorTerm()
    assert dcons.getNumSelectors() == 2

    # create datatype sort to test
    dtypeSpecEnum = solver.mkDatatypeDecl("enum")
    ca = solver.mkDatatypeConstructorDecl("A")
    dtypeSpecEnum.addConstructor(ca)
    cb = solver.mkDatatypeConstructorDecl("B")
    dtypeSpecEnum.addConstructor(cb)
    cc = solver.mkDatatypeConstructorDecl("C")
    dtypeSpecEnum.addConstructor(cc)
    dtypeSortEnum = solver.mkDatatypeSort(dtypeSpecEnum)
    dtEnum = dtypeSortEnum.getDatatype()
    assert not dtEnum.isTuple()
    assert dtEnum.isFinite()

    # create codatatype
    dtypeSpecStream = solver.mkDatatypeDecl("stream", True)
    consStream = solver.mkDatatypeConstructorDecl("cons")
    consStream.addSelector("head", intSort)
    consStream.addSelectorSelf("tail")
    dtypeSpecStream.addConstructor(consStream)
    dtypeSortStream = solver.mkDatatypeSort(dtypeSpecStream)
    dtStream = dtypeSortStream.getDatatype()
    assert dtStream.isCodatatype()
    assert not dtStream.isFinite()
    # codatatypes may be well-founded
    assert dtStream.isWellFounded()

    # create tuple
    tupSort = solver.mkTupleSort([boolSort])
    dtTuple = tupSort.getDatatype()
    assert dtTuple.isTuple()
    assert not dtTuple.isRecord()
    assert dtTuple.isFinite()
    assert dtTuple.isWellFounded()

    # create record
    fields = [("b", boolSort), ("i", intSort)]
    recSort = solver.mkRecordSort(fields)
    assert recSort.isDatatype()
    dtRecord = recSort.getDatatype()
    assert not dtRecord.isTuple()
    assert dtRecord.isRecord()
    assert not dtRecord.isFinite()
    assert dtRecord.isWellFounded()


def test_datatype_names(solver):
    intSort = solver.getIntegerSort()

    # create datatype sort to test
    dtypeSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", intSort)
    cons.addSelectorSelf("tail")
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    dtypeSort = solver.mkDatatypeSort(dtypeSpec)
    dt = dtypeSort.getDatatype()
    dt.getConstructor("nil")
    dt["cons"]
    with pytest.raises(RuntimeError):
        dt.getConstructor("head")
    with pytest.raises(RuntimeError):
        dt.getConstructor("")

    dcons = dt[0]
    assert dcons.getName() == "cons"
    dcons.getSelector("head")
    dcons["tail"]
    with pytest.raises(RuntimeError):
        dcons.getSelector("cons")

    # get selector
    dselTail = dcons[1]
    assert dselTail.getName() == "tail"
    assert dselTail.getRangeSort() == dtypeSort

    # get selector from datatype
    dt.getSelector("head")
    with pytest.raises(RuntimeError):
        dt.getSelector("cons")


def test_parametric_datatype(solver):
    v = []
    t1 = solver.mkParamSort("T1")
    t2 = solver.mkParamSort("T2")
    v.append(t1)
    v.append(t2)
    pairSpec = solver.mkDatatypeDecl("pair", v)

    mkpair = solver.mkDatatypeConstructorDecl("mk-pair")
    mkpair.addSelector("first", t1)
    mkpair.addSelector("second", t2)
    pairSpec.addConstructor(mkpair)

    pairType = solver.mkDatatypeSort(pairSpec)

    assert pairType.getDatatype().isParametric()

    v.clear()
    v.append(solver.getIntegerSort())
    v.append(solver.getIntegerSort())
    pairIntInt = pairType.instantiate(v)
    v.clear()
    v.append(solver.getRealSort())
    v.append(solver.getRealSort())
    pairRealReal = pairType.instantiate(v)
    v.clear()
    v.append(solver.getRealSort())
    v.append(solver.getIntegerSort())
    pairRealInt = pairType.instantiate(v)
    v.clear()
    v.append(solver.getIntegerSort())
    v.append(solver.getRealSort())
    pairIntReal = pairType.instantiate(v)

    assert pairIntInt != pairRealReal
    assert pairIntReal != pairRealReal
    assert pairRealInt != pairRealReal
    assert pairIntInt != pairIntReal
    assert pairIntInt != pairRealInt
    assert pairIntReal != pairRealInt

    assert pairRealReal.isComparableTo(pairRealReal)
    assert not pairIntReal.isComparableTo(pairRealReal)
    assert not pairRealInt.isComparableTo(pairRealReal)
    assert not pairIntInt.isComparableTo(pairRealReal)
    assert not pairRealReal.isComparableTo(pairRealInt)
    assert not pairIntReal.isComparableTo(pairRealInt)
    assert pairRealInt.isComparableTo(pairRealInt)
    assert not pairIntInt.isComparableTo(pairRealInt)
    assert not pairRealReal.isComparableTo(pairIntReal)
    assert pairIntReal.isComparableTo(pairIntReal)
    assert not pairRealInt.isComparableTo(pairIntReal)
    assert not pairIntInt.isComparableTo(pairIntReal)
    assert not pairRealReal.isComparableTo(pairIntInt)
    assert not pairIntReal.isComparableTo(pairIntInt)
    assert not pairRealInt.isComparableTo(pairIntInt)
    assert pairIntInt.isComparableTo(pairIntInt)

    assert pairRealReal.isSubsortOf(pairRealReal)
    assert not pairIntReal.isSubsortOf(pairRealReal)
    assert not pairRealInt.isSubsortOf(pairRealReal)
    assert not pairIntInt.isSubsortOf(pairRealReal)
    assert not pairRealReal.isSubsortOf(pairRealInt)
    assert not pairIntReal.isSubsortOf(pairRealInt)
    assert pairRealInt.isSubsortOf(pairRealInt)
    assert not pairIntInt.isSubsortOf(pairRealInt)
    assert not pairRealReal.isSubsortOf(pairIntReal)
    assert pairIntReal.isSubsortOf(pairIntReal)
    assert not pairRealInt.isSubsortOf(pairIntReal)
    assert not pairIntInt.isSubsortOf(pairIntReal)
    assert not pairRealReal.isSubsortOf(pairIntInt)
    assert not pairIntReal.isSubsortOf(pairIntInt)
    assert not pairRealInt.isSubsortOf(pairIntInt)
    assert pairIntInt.isSubsortOf(pairIntInt)
