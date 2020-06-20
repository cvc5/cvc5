import pytest

import pycvc4
from pycvc4 import kinds


def test_get_datatype():
    solver = pycvc4.Solver()
    dtypeSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    dtypeSort = solver.mkDatatypeSort(dtypeSpec)

    # expecting no Error
    dtypeSort.getDatatype()

    bvSort = solver.mkBitVectorSort(32)
    with pytest.raises(Exception):
        # expect an exception
        bvSort.getDatatype()


def test_datatype_sorts():
    solver = pycvc4.Solver()
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
    assert not dtypeSort.isConstructor()

    with pytest.raises(Exception):
        dtypeSort.getConstructorCodomainSort()

    with pytest.raises(Exception):
        dtypeSort.getConstructorDomainSorts()

    with pytest.raises(Exception):
        dtypeSort.getConstructorArity()

    # get constructor
    dcons = dt[0]
    consTerm = dcons.getConstructorTerm()
    consSort = consTerm.getSort()
    assert consSort.isConstructor()
    assert not consSort.isTester()
    assert not consSort.isSelector()
    assert consSort.getConstructorArity() == 2
    consDomSorts = consSort.getConstructorDomainSorts()
    assert consDomSorts[0] == intSort
    assert consDomSorts[1] == dtypeSort
    assert consSort.getConstructorCodomainSort() == dtypeSort

    # get tester
    isConsTerm = dcons.getTesterTerm()
    assert isConsTerm.getSort().isTester()

    # get selector
    dselTail = dcons[1]
    tailTerm = dselTail.getSelectorTerm()
    assert tailTerm.getSort().isSelector()
