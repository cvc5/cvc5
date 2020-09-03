import pytest

import pycvc4
from pycvc4 import kinds


def test_datatype_simply_rec():
    solver = pycvc4.Solver()

    # Create mutual datatypes corresponding to this definition block:
    #
    #   DATATYPE
    #     wlist = leaf(data: list),
    #     list = cons(car: wlist, cdr: list) | nil,
    #     ns = elem(ndata: set(wlist)) | elemArray(ndata2: array(list, list))
    #   END;

    # Make unresolved types as placeholders
    unres_wlist = solver.mkUninterpretedSort('wlist')
    unres_list = solver.mkUninterpretedSort('list')
    unres_ns = solver.mkUninterpretedSort('ns')
    unres_types = set([unres_wlist, unres_list, unres_ns])

    wlist = solver.mkDatatypeDecl('wlist')
    leaf = solver.mkDatatypeConstructorDecl('leaf')
    leaf.addSelector('data', unres_list)
    wlist.addConstructor(leaf)

    dlist = solver.mkDatatypeDecl('list')
    cons = solver.mkDatatypeConstructorDecl('cons')
    cons.addSelector('car', unres_wlist)
    cons.addSelector('cdr', unres_list)
    dlist.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dlist.addConstructor(nil)

    ns = solver.mkDatatypeDecl('ns')
    elem = solver.mkDatatypeConstructorDecl('elem')
    elem.addSelector('ndata', solver.mkSetSort(unres_wlist))
    ns.addConstructor(elem)
    elem_array = solver.mkDatatypeConstructorDecl('elemArray')
    elem_array.addSelector('ndata', solver.mkArraySort(unres_list, unres_list))
    ns.addConstructor(elem_array)

    # this is well-founded and has no nested recursion
    dtdecls = [wlist, dlist, ns]
    dtsorts = solver.mkDatatypeSorts(dtdecls, unres_types)
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
    #   END;
    unres_ns2 = solver.mkUninterpretedSort('ns2')
    unres_types = set([unres_ns2])

    ns2 = solver.mkDatatypeDecl('ns2')
    elem2 = solver.mkDatatypeConstructorDecl('elem2')
    elem2.addSelector('ndata',
                      solver.mkArraySort(solver.getIntegerSort(), unres_ns2))
    ns2.addConstructor(elem2)
    nil2 = solver.mkDatatypeConstructorDecl('nil2')
    ns2.addConstructor(nil2)

    # this is not well-founded due to non-simple recursion
    dtdecls = [ns2]
    dtsorts = solver.mkDatatypeSorts(dtdecls, unres_types)
    assert len(dtsorts) == 1
    assert dtsorts[0].getDatatype()[0][0].getRangeSort().isArray()
    elem_sort = dtsorts[0].getDatatype()[0][0].getRangeSort().getArrayElementSort()
    assert elem_sort == dtsorts[0]
    assert dtsorts[0].getDatatype().isWellFounded()
    assert dtsorts[0].getDatatype().hasNestedRecursion()

    # Create mutual datatypes corresponding to this definition block:
    #  DATATYPE
    #    list3 = cons3(car: ns3, cdr: list3) | nil3,
    #    ns3 = elem3(ndata: set(list3))
    #  END
    unres_ns3 = solver.mkUninterpretedSort('ns3')
    unres_list3 = solver.mkUninterpretedSort('list3')
    unres_types = set([unres_ns3, unres_list3])

    list3 = solver.mkDatatypeDecl('list3')
    cons3 = solver.mkDatatypeConstructorDecl('cons3')
    cons3.addSelector('car', unres_ns3)
    cons3.addSelector('cdr', unres_list3)
    list3.addConstructor(cons3)
    nil3 = solver.mkDatatypeConstructorDecl('nil3')
    list3.addConstructor(nil3)

    ns3 = solver.mkDatatypeDecl('ns3')
    elem3 = solver.mkDatatypeConstructorDecl('elem3')
    elem3.addSelector('ndata', solver.mkSetSort(unres_list3))
    ns3.addConstructor(elem3)

    # both are well-founded and have nested recursion
    dtdecls = [list3, ns3]
    dtsorts = solver.mkDatatypeSorts(dtdecls, unres_types)
    assert len(dtsorts) == 2
    assert dtsorts[0].getDatatype().isWellFounded()
    assert dtsorts[1].getDatatype().isWellFounded()
    assert dtsorts[0].getDatatype().hasNestedRecursion()
    assert dtsorts[1].getDatatype().hasNestedRecursion()

    # Create mutual datatypes corresponding to this definition block:
    #  DATATYPE
    #    list4 = cons(car: set(ns4), cdr: list4) | nil,
    #    ns4 = elem(ndata: list4)
    #  END
    unres_ns4 = solver.mkUninterpretedSort('ns4')
    unres_list4 = solver.mkUninterpretedSort('list4')
    unres_types = set([unres_ns4, unres_list4])

    list4 = solver.mkDatatypeDecl('list4')
    cons4 = solver.mkDatatypeConstructorDecl('cons4')
    cons4.addSelector('car', solver.mkSetSort(unres_ns4))
    cons4.addSelector('cdr', unres_list4)
    list4.addConstructor(cons4)
    nil4 = solver.mkDatatypeConstructorDecl('nil4')
    list4.addConstructor(nil4)

    ns4 = solver.mkDatatypeDecl('ns4')
    elem4 = solver.mkDatatypeConstructorDecl('elem3')
    elem4.addSelector('ndata', unres_list4)
    ns4.addConstructor(elem4)

    # both are well-founded and have nested recursion
    dtdecls = [list4, ns4]
    dtsorts = solver.mkDatatypeSorts(dtdecls, unres_types)
    assert len(dtsorts) == 2
    assert dtsorts[0].getDatatype().isWellFounded()
    assert dtsorts[1].getDatatype().isWellFounded()
    assert dtsorts[0].getDatatype().hasNestedRecursion()
    assert dtsorts[1].getDatatype().hasNestedRecursion()

    # Create mutual datatypes corresponding to this definition block:
    #  DATATYPE
    #    list5[X] = cons(car: X, cdr: list5[list5[X]]) | nil
    #  END
    unres_list5 = solver.mkSortConstructorSort('list5', 1)
    unres_types = set([unres_list5])

    x = solver.mkParamSort('X')
    v = [x]
    list5 = solver.mkDatatypeDecl('list5', v)

    args = [x]
    ur_list_x = unres_list5.instantiate(args)
    args = [ur_list_x]
    ur_list_list_x = unres_list5.instantiate(args)

    cons5 = solver.mkDatatypeConstructorDecl('cons5')
    cons5.addSelector('car', x)
    cons5.addSelector('cdr', ur_list_list_x)
    list5.addConstructor(cons5)
    nil5 = solver.mkDatatypeConstructorDecl('nil5')
    list5.addConstructor(nil5)

    # well-founded and has nested recursion
    dtdecls = [list5]
    dtsorts = solver.mkDatatypeSorts(dtdecls, unres_types)
    assert len(dtsorts) == 1
    assert dtsorts[0].getDatatype().isWellFounded()
    assert dtsorts[0].getDatatype().hasNestedRecursion()
