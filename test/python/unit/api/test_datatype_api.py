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
from pycvc5 import Sort, Term 
from pycvc5 import DatatypeDecl
from pycvc5 import Datatype
from pycvc5 import DatatypeConstructorDecl
from pycvc5 import DatatypeConstructor
from pycvc5 import DatatypeSelector


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

def test_is_null(solver):
  # creating empty (null) objects.
  dtypeSpec = DatatypeDecl(solver)
  cons = DatatypeConstructorDecl(solver)
  d = Datatype(solver)
  consConstr = DatatypeConstructor(solver)
  sel = DatatypeSelector(solver)

  # verifying that the objects are considered null.
  assert dtypeSpec.isNull()
  assert cons.isNull()
  assert d.isNull()
  assert consConstr.isNull()
  assert sel.isNull()

  # changing the objects to be non-null
  dtypeSpec = solver.mkDatatypeDecl("list");
  cons = solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", solver.getIntegerSort());
  dtypeSpec.addConstructor(cons);
  listSort = solver.mkDatatypeSort(dtypeSpec)
  d = listSort.getDatatype();
  consConstr = d[0];
  sel = consConstr[0];

  # verifying that the new objects are non-null
  assert not dtypeSpec.isNull()
  assert not cons.isNull()
  assert not d.isNull()
  assert not consConstr.isNull()
  assert not sel.isNull()

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
        assert dtsorts[i].getDatatype().getName() == dtdecls[i].getName()
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
    with pytest.raises(RuntimeError):
        solver.mkDatatypeSorts(dtdeclsBad)


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
    dtypeSpec.getName()
    assert dtypeSpec.getName() == "list"
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", intSort)
    cons.addSelectorSelf("tail")
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    dtypeSort = solver.mkDatatypeSort(dtypeSpec)
    dt = dtypeSort.getDatatype()
    assert dt.getName() == "list"
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

    # possible to construct null datatype declarations if not using mkDatatypeDecl
    with pytest.raises(RuntimeError):
        DatatypeDecl(solver).getName()


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


def test_datatype_simply_rec(solver):
    # Create mutual datatypes corresponding to this definition block:
    #
    #   DATATYPE
    #     wlist = leaf(data: list),
    #     list = cons(car: wlist, cdr: list) | nil,
    #     ns = elem(ndata: set(wlist)) | elemArray(ndata2: array(list, list))
    #   END

    # Make unresolved types as placeholders
    unresTypes = set([])
    unresWList = solver.mkUninterpretedSort("wlist")
    unresList = solver.mkUninterpretedSort("list")
    unresNs = solver.mkUninterpretedSort("ns")
    unresTypes.add(unresWList)
    unresTypes.add(unresList)
    unresTypes.add(unresNs)

    wlist = solver.mkDatatypeDecl("wlist")
    leaf = solver.mkDatatypeConstructorDecl("leaf")
    leaf.addSelector("data", unresList)
    wlist.addConstructor(leaf)

    llist = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("car", unresWList)
    cons.addSelector("cdr", unresList)
    llist.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    llist.addConstructor(nil)

    ns = solver.mkDatatypeDecl("ns")
    elem = solver.mkDatatypeConstructorDecl("elem")
    elem.addSelector("ndata", solver.mkSetSort(unresWList))
    ns.addConstructor(elem)
    elemArray = solver.mkDatatypeConstructorDecl("elemArray")
    elemArray.addSelector("ndata", solver.mkArraySort(unresList, unresList))
    ns.addConstructor(elemArray)

    dtdecls = [wlist, llist, ns]
    # this is well-founded and has no nested recursion
    dtsorts = solver.mkDatatypeSorts(dtdecls, unresTypes)
    assert len(dtsorts) == 3
    assert dtsorts[0].getDatatype().isWellFounded()
    assert dtsorts[1].getDatatype().isWellFounded()
    assert dtsorts[2].getDatatype().isWellFounded()
    assert not dtsorts[0].getDatatype().hasNestedRecursion()
    assert not dtsorts[1].getDatatype().hasNestedRecursion()
    assert not dtsorts[2].getDatatype().hasNestedRecursion()

    # Create mutual datatypes corresponding to this definition block:
    #   DATATYPE
    #     ns2 = elem2(ndata: array(int,ns2)) | nil2
    #   END

    unresTypes.clear()
    unresNs2 = solver.mkUninterpretedSort("ns2")
    unresTypes.add(unresNs2)

    ns2 = solver.mkDatatypeDecl("ns2")
    elem2 = solver.mkDatatypeConstructorDecl("elem2")
    elem2.addSelector("ndata",
                      solver.mkArraySort(solver.getIntegerSort(), unresNs2))
    ns2.addConstructor(elem2)
    nil2 = solver.mkDatatypeConstructorDecl("nil2")
    ns2.addConstructor(nil2)

    dtdecls.clear()
    dtdecls.append(ns2)

    # this is not well-founded due to non-simple recursion
    dtsorts = solver.mkDatatypeSorts(dtdecls, unresTypes)
    assert len(dtsorts) == 1
    assert dtsorts[0].getDatatype()[0][0].getRangeSort().isArray()
    assert dtsorts[0].getDatatype()[0][0].getRangeSort().getArrayElementSort() \
        == dtsorts[0]
    assert dtsorts[0].getDatatype().isWellFounded()
    assert dtsorts[0].getDatatype().hasNestedRecursion()

    # Create mutual datatypes corresponding to this definition block:
    #   DATATYPE
    #     list3 = cons3(car: ns3, cdr: list3) | nil3,
    #     ns3 = elem3(ndata: set(list3))
    #   END

    unresTypes.clear()
    unresNs3 = solver.mkUninterpretedSort("ns3")
    unresTypes.add(unresNs3)
    unresList3 = solver.mkUninterpretedSort("list3")
    unresTypes.add(unresList3)

    list3 = solver.mkDatatypeDecl("list3")
    cons3 = solver.mkDatatypeConstructorDecl("cons3")
    cons3.addSelector("car", unresNs3)
    cons3.addSelector("cdr", unresList3)
    list3.addConstructor(cons3)
    nil3 = solver.mkDatatypeConstructorDecl("nil3")
    list3.addConstructor(nil3)

    ns3 = solver.mkDatatypeDecl("ns3")
    elem3 = solver.mkDatatypeConstructorDecl("elem3")
    elem3.addSelector("ndata", solver.mkSetSort(unresList3))
    ns3.addConstructor(elem3)

    dtdecls.clear()
    dtdecls.append(list3)
    dtdecls.append(ns3)

    # both are well-founded and have nested recursion
    dtsorts = solver.mkDatatypeSorts(dtdecls, unresTypes)
    assert len(dtsorts) == 2
    assert dtsorts[0].getDatatype().isWellFounded()
    assert dtsorts[1].getDatatype().isWellFounded()
    assert dtsorts[0].getDatatype().hasNestedRecursion()
    assert dtsorts[1].getDatatype().hasNestedRecursion()

    # Create mutual datatypes corresponding to this definition block:
    #   DATATYPE
    #     list4 = cons(car: set(ns4), cdr: list4) | nil,
    #     ns4 = elem(ndata: list4)
    #   END
    unresTypes.clear()
    unresNs4 = solver.mkUninterpretedSort("ns4")
    unresTypes.add(unresNs4)
    unresList4 = solver.mkUninterpretedSort("list4")
    unresTypes.add(unresList4)

    list4 = solver.mkDatatypeDecl("list4")
    cons4 = solver.mkDatatypeConstructorDecl("cons4")
    cons4.addSelector("car", solver.mkSetSort(unresNs4))
    cons4.addSelector("cdr", unresList4)
    list4.addConstructor(cons4)
    nil4 = solver.mkDatatypeConstructorDecl("nil4")
    list4.addConstructor(nil4)

    ns4 = solver.mkDatatypeDecl("ns4")
    elem4 = solver.mkDatatypeConstructorDecl("elem3")
    elem4.addSelector("ndata", unresList4)
    ns4.addConstructor(elem4)

    dtdecls.clear()
    dtdecls.append(list4)
    dtdecls.append(ns4)

    # both are well-founded and have nested recursion
    dtsorts = solver.mkDatatypeSorts(dtdecls, unresTypes)
    assert len(dtsorts) == 2
    assert dtsorts[0].getDatatype().isWellFounded()
    assert dtsorts[1].getDatatype().isWellFounded()
    assert dtsorts[0].getDatatype().hasNestedRecursion()
    assert dtsorts[1].getDatatype().hasNestedRecursion()

    # Create mutual datatypes corresponding to this definition block:
    #   DATATYPE
    #     list5[X] = cons(car: X, cdr: list5[list5[X]]) | nil
    #   END
    unresTypes.clear()
    unresList5 = solver.mkSortConstructorSort("list5", 1)
    unresTypes.add(unresList5)

    v = []
    x = solver.mkParamSort("X")
    v.append(x)
    list5 = solver.mkDatatypeDecl("list5", v)

    args = [x]
    urListX = unresList5.instantiate(args)
    args[0] = urListX
    urListListX = unresList5.instantiate(args)

    cons5 = solver.mkDatatypeConstructorDecl("cons5")
    cons5.addSelector("car", x)
    cons5.addSelector("cdr", urListListX)
    list5.addConstructor(cons5)
    nil5 = solver.mkDatatypeConstructorDecl("nil5")
    list5.addConstructor(nil5)

    dtdecls.clear()
    dtdecls.append(list5)

    # well-founded and has nested recursion
    dtsorts = solver.mkDatatypeSorts(dtdecls, unresTypes)
    assert len(dtsorts) == 1
    assert dtsorts[0].getDatatype().isWellFounded()
    assert dtsorts[0].getDatatype().hasNestedRecursion()


def test_datatype_specialized_cons(solver):
    # Create mutual datatypes corresponding to this definition block:
    #   DATATYPE
    #     plist[X] = pcons(car: X, cdr: plist[X]) | pnil
    #   END

    # Make unresolved types as placeholders
    unresTypes = set([])
    unresList = solver.mkSortConstructorSort("plist", 1)
    unresTypes.add(unresList)

    v = []
    x = solver.mkParamSort("X")
    v.append(x)
    plist = solver.mkDatatypeDecl("plist", v)

    args = [x]
    urListX = unresList.instantiate(args)

    pcons = solver.mkDatatypeConstructorDecl("pcons")
    pcons.addSelector("car", x)
    pcons.addSelector("cdr", urListX)
    plist.addConstructor(pcons)
    nil5 = solver.mkDatatypeConstructorDecl("pnil")
    plist.addConstructor(nil5)

    dtdecls = [plist]

    # make the datatype sorts
    dtsorts = solver.mkDatatypeSorts(dtdecls, unresTypes)
    assert len(dtsorts) == 1
    d = dtsorts[0].getDatatype()
    nilc = d[0]

    isort = solver.getIntegerSort()
    iargs = [isort]
    listInt = dtsorts[0].instantiate(iargs)

    testConsTerm = Term(solver)
    # get the specialized constructor term for list[Int]
    testConsTerm = nilc.getSpecializedConstructorTerm(listInt)
    assert testConsTerm != nilc.getConstructorTerm()
    # error to get the specialized constructor term for Int
    with pytest.raises(RuntimeError):
        nilc.getSpecializedConstructorTerm(isort)
