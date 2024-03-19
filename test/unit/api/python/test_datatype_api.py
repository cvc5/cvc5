###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Andrew Reynolds, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

import pytest
import cvc5
from cvc5 import Sort, Term 
from cvc5 import DatatypeDecl
from cvc5 import Datatype
from cvc5 import DatatypeConstructorDecl
from cvc5 import DatatypeConstructor
from cvc5 import DatatypeSelector


@pytest.fixture
def tm():
    return cvc5.TermManager()


def test_mk_datatype_sort(tm):
    dtypeSpec = tm.mkDatatypeDecl("list")
    cons = tm.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", tm.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = tm.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    listSort = tm.mkDatatypeSort(dtypeSpec)
    d = listSort.getDatatype()
    consConstr = d[0]
    nilConstr = d[1]
    with pytest.raises(RuntimeError):
        d[2]
    consConstr.getTerm()
    nilConstr.getTerm()

def test_is_null(tm):
  # creating empty (null) objects.
  dtypeSpec = DatatypeDecl(tm)
  cons = DatatypeConstructorDecl(tm)
  d = Datatype(tm)
  consConstr = DatatypeConstructor(tm)
  sel = DatatypeSelector(tm)

  # verifying that the objects are considered null.
  assert dtypeSpec.isNull()
  assert cons.isNull()
  assert d.isNull()
  assert consConstr.isNull()
  assert sel.isNull()

  # changing the objects to be non-null
  dtypeSpec = tm.mkDatatypeDecl("list")
  cons = tm.mkDatatypeConstructorDecl("cons")
  cons.addSelector("head", tm.getIntegerSort())
  dtypeSpec.addConstructor(cons)
  assert dtypeSpec.getNumConstructors() == 1
  assert not dtypeSpec.isParametric()
  listSort = tm.mkDatatypeSort(dtypeSpec)
  d = listSort.getDatatype()
  consConstr = d[0]
  sel = consConstr[0]

  # verifying that the new objects are non-null
  assert not dtypeSpec.isNull()
  assert not cons.isNull()
  assert not d.isNull()
  assert not consConstr.isNull()
  assert not sel.isNull()

def test_mk_datatype_sorts(tm):
    # Create two mutual datatypes corresponding to this definition
    # block:
    #
    #   DATATYPE
    #     tree = node(left: tree, right: tree) | leaf(data: list),
    #     list = cons(car: tree, cdr: list) | nil
    #   END
    #

    #Make unresolved types as placeholders
    unresTree = tm.mkUnresolvedDatatypeSort("tree")
    unresList = tm.mkUnresolvedDatatypeSort("list")

    tree = tm.mkDatatypeDecl("tree")
    node = tm.mkDatatypeConstructorDecl("node")
    node.addSelector("left", unresTree)
    node.addSelector("right", unresTree)
    tree.addConstructor(node)

    leaf = tm.mkDatatypeConstructorDecl("leaf")
    leaf.addSelector("data", unresList)
    tree.addConstructor(leaf)

    llist = tm.mkDatatypeDecl("list")
    cons = tm.mkDatatypeConstructorDecl("cons")
    cons.addSelector("car", unresTree)
    cons.addSelector("cdr", unresTree)
    llist.addConstructor(cons)

    nil = tm.mkDatatypeConstructorDecl("nil")
    llist.addConstructor(nil)

    dtdecls = []
    dtdecls.append(tree)
    dtdecls.append(llist)
    dtsorts = []
    dtsorts = tm.mkDatatypeSorts(dtdecls)
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
    assert dtsTreeNodeLeft.getCodomainSort().isDatatype()
    assert dtsTreeNodeLeft.getCodomainSort() == dtsorts[0]

    # fails due to empty datatype
    dtdeclsBad = []
    emptyD = tm.mkDatatypeDecl("emptyD")
    dtdeclsBad.append(emptyD)
    with pytest.raises(RuntimeError):
        tm.mkDatatypeSorts(dtdeclsBad)


def test_mk_datatype_sorts_sel_unres(tm):
    # Same as above, using unresolved selectors

    tree = tm.mkDatatypeDecl("tree")
    node = tm.mkDatatypeConstructorDecl("node")
    node.addSelectorUnresolved("left", "tree")
    node.addSelectorUnresolved("right", "tree")
    tree.addConstructor(node)

    leaf = tm.mkDatatypeConstructorDecl("leaf")
    leaf.addSelectorUnresolved("data", "list")
    tree.addConstructor(leaf)

    llist = tm.mkDatatypeDecl("list")
    cons = tm.mkDatatypeConstructorDecl("cons")
    cons.addSelectorUnresolved("car", "tree")
    cons.addSelectorUnresolved("cdr", "tree")
    llist.addConstructor(cons)

    nil = tm.mkDatatypeConstructorDecl("nil")
    llist.addConstructor(nil)

    dtdecls = []
    dtdecls.append(tree)
    dtdecls.append(llist)
    dtsorts = []
    dtsorts = tm.mkDatatypeSorts(dtdecls)
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
    assert dtsTreeNodeLeft.getCodomainSort().isDatatype()
    assert dtsTreeNodeLeft.getCodomainSort() == dtsorts[0]

def test_datatype_structs(tm):
    intSort = tm.getIntegerSort()
    boolSort = tm.getBooleanSort()

    # create datatype sort to test
    dtypeSpec = tm.mkDatatypeDecl("list")
    cons = tm.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", intSort)
    cons.addSelectorSelf("tail")
    nullSort = Sort(tm)
    with pytest.raises(RuntimeError):
        cons.addSelector("null", nullSort)
    dtypeSpec.addConstructor(cons)
    nil = tm.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    dtypeSort = tm.mkDatatypeSort(dtypeSpec)
    dt = dtypeSort.getDatatype()
    # not parametric datatype
    with pytest.raises(RuntimeError): dt.getParameters()
    assert not dt.isCodatatype()
    assert not dt.isTuple()
    assert not dt.isRecord()
    assert not dt.isFinite()
    assert dt.isWellFounded()
    # get constructor
    dcons = dt[0]
    consTerm = dcons.getTerm()
    assert dcons.getNumSelectors() == 2

    # create datatype sort to test
    dtypeSpecEnum = tm.mkDatatypeDecl("enum")
    ca = tm.mkDatatypeConstructorDecl("A")
    dtypeSpecEnum.addConstructor(ca)
    cb = tm.mkDatatypeConstructorDecl("B")
    dtypeSpecEnum.addConstructor(cb)
    cc = tm.mkDatatypeConstructorDecl("C")
    dtypeSpecEnum.addConstructor(cc)
    dtypeSortEnum = tm.mkDatatypeSort(dtypeSpecEnum)
    dtEnum = dtypeSortEnum.getDatatype()
    assert not dtEnum.isTuple()
    assert dtEnum.isFinite()

    # create codatatype
    dtypeSpecStream = tm.mkDatatypeDecl("stream", True)
    consStream = tm.mkDatatypeConstructorDecl("cons")
    consStream.addSelector("head", intSort)
    consStream.addSelectorSelf("tail")
    dtypeSpecStream.addConstructor(consStream)
    dtypeSortStream = tm.mkDatatypeSort(dtypeSpecStream)
    dtStream = dtypeSortStream.getDatatype()
    assert dtStream.isCodatatype()
    assert not dtStream.isFinite()
    # codatatypes may be well-founded
    assert dtStream.isWellFounded()

    # create tuple
    tupSort = tm.mkTupleSort(boolSort)
    dtTuple = tupSort.getDatatype()
    assert dtTuple.isTuple()
    assert not dtTuple.isRecord()
    assert dtTuple.isFinite()
    assert dtTuple.isWellFounded()

    # create record
    fields = [("b", boolSort), ("i", intSort)]
    recSort = tm.mkRecordSort(*fields)
    assert recSort.isDatatype()
    dtRecord = recSort.getDatatype()
    assert not dtRecord.isTuple()
    assert dtRecord.isRecord()
    assert not dtRecord.isFinite()
    assert dtRecord.isWellFounded()


def test_datatype_names(tm):
    intSort = tm.getIntegerSort()

    # create datatype sort to test
    dtypeSpec = tm.mkDatatypeDecl("list")
    dtypeSpec.getName()
    assert dtypeSpec.getName() == "list"
    cons = tm.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", intSort)
    cons.addSelectorSelf("tail")
    dtypeSpec.addConstructor(cons)
    nil = tm.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    dtypeSort = tm.mkDatatypeSort(dtypeSpec)
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
    assert dselTail.getCodomainSort() == dtypeSort

    # get selector from datatype
    dt.getSelector("head")
    with pytest.raises(RuntimeError):
        dt.getSelector("cons")

    # possible to construct null datatype declarations if not using mkDatatypeDecl
    with pytest.raises(RuntimeError):
        DatatypeDecl(tm).getName()


def test_parametric_datatype(tm):
    v = []
    t1 = tm.mkParamSort("T1")
    t2 = tm.mkParamSort("T2")
    v.append(t1)
    v.append(t2)
    pairSpec = tm.mkDatatypeDecl("pair", v)

    mkpair = tm.mkDatatypeConstructorDecl("mk-pair")
    mkpair.addSelector("first", t1)
    mkpair.addSelector("second", t2)
    pairSpec.addConstructor(mkpair)

    pairType = tm.mkDatatypeSort(pairSpec)

    assert pairType.getDatatype().isParametric()
    dparams = pairType.getDatatype().getParameters()
    assert dparams[0]==t1 and dparams[1]==t2

    v.clear()
    v.append(tm.getIntegerSort())
    v.append(tm.getIntegerSort())
    pairIntInt = pairType.instantiate(v)
    v.clear()
    v.append(tm.getRealSort())
    v.append(tm.getRealSort())
    pairRealReal = pairType.instantiate(v)
    v.clear()
    v.append(tm.getRealSort())
    v.append(tm.getIntegerSort())
    pairRealInt = pairType.instantiate(v)
    v.clear()
    v.append(tm.getIntegerSort())
    v.append(tm.getRealSort())
    pairIntReal = pairType.instantiate(v)

    assert pairIntInt != pairRealReal
    assert pairIntReal != pairRealReal
    assert pairRealInt != pairRealReal
    assert pairIntInt != pairIntReal
    assert pairIntInt != pairRealInt
    assert pairIntReal != pairRealInt

def test_is_finite(tm):
    dtypedecl = tm.mkDatatypeDecl("dt", [])
    ctordecl = tm.mkDatatypeConstructorDecl("cons")
    ctordecl.addSelector("sel", tm.getBooleanSort())
    dtypedecl.addConstructor(ctordecl)
    dtype = tm.mkDatatypeSort(dtypedecl)
    assert dtype.getDatatype().isFinite()

    p = tm.mkParamSort("p1")
    pdtypedecl = tm.mkDatatypeDecl("dt", [p])
    pctordecl = tm.mkDatatypeConstructorDecl("cons")
    pctordecl.addSelector("sel", p)
    pdtypedecl.addConstructor(pctordecl)
    pdtype = tm.mkDatatypeSort(pdtypedecl)
    with pytest.raises(RuntimeError):
        pdtype.getDatatype().isFinite()

def test_datatype_simply_rec(tm):
    # Create mutual datatypes corresponding to this definition block:
    #
    #   DATATYPE
    #     wlist = leaf(data: list),
    #     list = cons(car: wlist, cdr: list) | nil,
    #     ns = elem(ndata: set(wlist)) | elemArray(ndata2: array(list, list))
    #   END

    # Make unresolved types as placeholders
    unresWList = tm.mkUnresolvedDatatypeSort("wlist")
    unresList = tm.mkUnresolvedDatatypeSort("list")
    unresNs = tm.mkUnresolvedDatatypeSort("ns")

    wlist = tm.mkDatatypeDecl("wlist")
    leaf = tm.mkDatatypeConstructorDecl("leaf")
    leaf.addSelector("data", unresList)
    wlist.addConstructor(leaf)

    llist = tm.mkDatatypeDecl("list")
    cons = tm.mkDatatypeConstructorDecl("cons")
    cons.addSelector("car", unresWList)
    cons.addSelector("cdr", unresList)
    llist.addConstructor(cons)
    nil = tm.mkDatatypeConstructorDecl("nil")
    llist.addConstructor(nil)

    ns = tm.mkDatatypeDecl("ns")
    elem = tm.mkDatatypeConstructorDecl("elem")
    elem.addSelector("ndata", tm.mkSetSort(unresWList))
    ns.addConstructor(elem)
    elemArray = tm.mkDatatypeConstructorDecl("elemArray")
    elemArray.addSelector("ndata", tm.mkArraySort(unresList, unresList))
    ns.addConstructor(elemArray)

    dtdecls = [wlist, llist, ns]
    # this is well-founded and has no nested recursion
    dtsorts = tm.mkDatatypeSorts(dtdecls)
    assert len(dtsorts) == 3
    assert dtsorts[0].getDatatype().isWellFounded()
    assert dtsorts[1].getDatatype().isWellFounded()
    assert dtsorts[2].getDatatype().isWellFounded()

    # Create mutual datatypes corresponding to this definition block:
    #   DATATYPE
    #     ns2 = elem2(ndata: array(int,ns2)) | nil2
    #   END

    unresNs2 = tm.mkUnresolvedDatatypeSort("ns2")

    ns2 = tm.mkDatatypeDecl("ns2")
    elem2 = tm.mkDatatypeConstructorDecl("elem2")
    elem2.addSelector("ndata",
                      tm.mkArraySort(tm.getIntegerSort(), unresNs2))
    ns2.addConstructor(elem2)
    nil2 = tm.mkDatatypeConstructorDecl("nil2")
    ns2.addConstructor(nil2)

    dtdecls.clear()
    dtdecls.append(ns2)

    # this is not well-founded due to non-simple recursion
    dtsorts = tm.mkDatatypeSorts(dtdecls)
    assert len(dtsorts) == 1
    assert dtsorts[0].getDatatype()[0][0].getCodomainSort().isArray()
    assert dtsorts[0].getDatatype()[0][0].getCodomainSort().getArrayElementSort() \
        == dtsorts[0]
    assert dtsorts[0].getDatatype().isWellFounded()

    # Create mutual datatypes corresponding to this definition block:
    #   DATATYPE
    #     list3 = cons3(car: ns3, cdr: list3) | nil3,
    #     ns3 = elem3(ndata: set(list3))
    #   END

    unresNs3 = tm.mkUnresolvedDatatypeSort("ns3")
    unresList3 = tm.mkUnresolvedDatatypeSort("list3")

    list3 = tm.mkDatatypeDecl("list3")
    cons3 = tm.mkDatatypeConstructorDecl("cons3")
    cons3.addSelector("car", unresNs3)
    cons3.addSelector("cdr", unresList3)
    list3.addConstructor(cons3)
    nil3 = tm.mkDatatypeConstructorDecl("nil3")
    list3.addConstructor(nil3)

    ns3 = tm.mkDatatypeDecl("ns3")
    elem3 = tm.mkDatatypeConstructorDecl("elem3")
    elem3.addSelector("ndata", tm.mkSetSort(unresList3))
    ns3.addConstructor(elem3)

    dtdecls.clear()
    dtdecls.append(list3)
    dtdecls.append(ns3)

    # both are well-founded and have nested recursion
    dtsorts = tm.mkDatatypeSorts(dtdecls)
    assert len(dtsorts) == 2
    assert dtsorts[0].getDatatype().isWellFounded()
    assert dtsorts[1].getDatatype().isWellFounded()

    # Create mutual datatypes corresponding to this definition block:
    #   DATATYPE
    #     list4 = cons(car: set(ns4), cdr: list4) | nil,
    #     ns4 = elem(ndata: list4)
    #   END
    unresNs4 = tm.mkUnresolvedDatatypeSort("ns4")
    unresList4 = tm.mkUnresolvedDatatypeSort("list4")

    list4 = tm.mkDatatypeDecl("list4")
    cons4 = tm.mkDatatypeConstructorDecl("cons4")
    cons4.addSelector("car", tm.mkSetSort(unresNs4))
    cons4.addSelector("cdr", unresList4)
    list4.addConstructor(cons4)
    nil4 = tm.mkDatatypeConstructorDecl("nil4")
    list4.addConstructor(nil4)

    ns4 = tm.mkDatatypeDecl("ns4")
    elem4 = tm.mkDatatypeConstructorDecl("elem3")
    elem4.addSelector("ndata", unresList4)
    ns4.addConstructor(elem4)

    dtdecls.clear()
    dtdecls.append(list4)
    dtdecls.append(ns4)

    # both are well-founded and have nested recursion
    dtsorts = tm.mkDatatypeSorts(dtdecls)
    assert len(dtsorts) == 2
    assert dtsorts[0].getDatatype().isWellFounded()
    assert dtsorts[1].getDatatype().isWellFounded()

    # Create mutual datatypes corresponding to this definition block:
    #   DATATYPE
    #     list5[X] = cons(car: X, cdr: list5[list5[X]]) | nil
    #   END
    unresList5 = tm.mkUninterpretedSortConstructorSort(1, "list5")

    v = []
    x = tm.mkParamSort("X")
    v.append(x)
    list5 = tm.mkDatatypeDecl("list5", v)

    args = [x]
    urListX = unresList5.instantiate(args)
    args[0] = urListX
    urListListX = unresList5.instantiate(args)

    cons5 = tm.mkDatatypeConstructorDecl("cons5")
    cons5.addSelector("car", x)
    cons5.addSelector("cdr", urListListX)
    list5.addConstructor(cons5)
    nil5 = tm.mkDatatypeConstructorDecl("nil5")
    list5.addConstructor(nil5)

    dtdecls.clear()
    dtdecls.append(list5)

    # well-founded and has nested recursion
    dtsorts = tm.mkDatatypeSorts(dtdecls)
    assert len(dtsorts) == 1
    assert dtsorts[0].getDatatype().isWellFounded()


def test_datatype_specialized_cons(tm):
    # Create mutual datatypes corresponding to this definition block:
    #   DATATYPE
    #     plist[X] = pcons(car: X, cdr: plist[X]) | pnil
    #   END

    # Make unresolved types as placeholders
    unresList = tm.mkUninterpretedSortConstructorSort(1, "plist")
    v = []
    x = tm.mkParamSort("X")
    v.append(x)
    plist = tm.mkDatatypeDecl("plist", v)

    args = [x]
    urListX = unresList.instantiate(args)

    pcons = tm.mkDatatypeConstructorDecl("pcons")
    pcons.addSelector("car", x)
    pcons.addSelector("cdr", urListX)
    plist.addConstructor(pcons)
    nil5 = tm.mkDatatypeConstructorDecl("pnil")
    plist.addConstructor(nil5)

    dtdecls = [plist]

    # make the datatype sorts
    dtsorts = tm.mkDatatypeSorts(dtdecls)
    assert len(dtsorts) == 1
    d = dtsorts[0].getDatatype()
    nilc = d[0]

    isort = tm.getIntegerSort()
    iargs = [isort]
    listInt = dtsorts[0].instantiate(iargs)

    testConsTerm = Term(tm)
    # get the specialized constructor term for list[Int]
    testConsTerm = nilc.getInstantiatedTerm(listInt)
    assert testConsTerm != nilc.getTerm()
    # error to get the specialized constructor term for Int
    with pytest.raises(RuntimeError):
        nilc.getInstantiatedTerm(isort)
