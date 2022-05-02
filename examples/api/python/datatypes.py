#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Makai Mann, Aina Niemetz, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5 datatypes
# solver through the Python API. This is a direct translation of
# datatypes-new.cpp.
##

import cvc5
from cvc5 import Kind

def test(slv, consListSort):
    # Now our old "consListSpec" is useless--the relevant information
    # has been copied out, so we can throw that spec away.  We can get
    # the complete spec for the datatype from the DatatypeSort, and
    # this Datatype object has constructor symbols (and others) filled in.

    consList = consListSort.getDatatype()

    # t = cons 0 nil
    #
    # Here, consList["cons"] gives you the DatatypeConstructor.  To get
    # the constructor symbol for application, use .getConstructor("cons"),
    # which is equivalent to consList["cons"].getConstructor().  Note that
    # "nil" is a constructor too

    t = slv.mkTerm(
            Kind.APPLY_CONSTRUCTOR,
            consList.getConstructor("cons").getTerm(),
            slv.mkInteger(0),
            slv.mkTerm(
                Kind.APPLY_CONSTRUCTOR,
                consList.getConstructor("nil").getTerm()))

    print("t is {}\nsort of cons is {}\n sort of nil is {}".format(
        t,
        consList.getConstructor("cons").getTerm().getSort(),
        consList.getConstructor("nil").getTerm().getSort()))

    # t2 = head(cons 0 nil), and of course this can be evaluated
    #
    # Here we first get the DatatypeConstructor for cons (with
    # consList["cons"]) in order to get the "head" selector symbol
    # to apply.

    t2 = slv.mkTerm(
            Kind.APPLY_SELECTOR,
            consList["cons"].getSelector("head").getTerm(),
            t)

    print("t2 is {}\nsimplify(t2) is {}\n\n".format(t2, slv.simplify(t2)))

    # You can also iterate over a Datatype to get all its constructors,
    # and over a DatatypeConstructor to get all its "args" (selectors)
    for i in consList:
        print("ctor:", i)
        for j in i:
            print(" + args:", j)
        print()

    # You can also define a tester term for constructor 'cons': (_ is cons)
    t_is_cons = slv.mkTerm(
            Kind.APPLY_TESTER, consList["cons"].getTesterTerm(), t)
    print("t_is_cons is {}\n\n".format(t_is_cons))
    slv.assertFormula(t_is_cons)
    # Updating t at 'head' with value 1 is defined as follows:
    t_updated = slv.mkTerm(Kind.APPLY_UPDATER,
                           consList["cons"]["head"].getUpdaterTerm(),
                           t,
                           slv.mkInteger(1))
    print("t_updated is {}\n\n".format(t_updated))
    slv.assertFormula(slv.mkTerm(Kind.DISTINCT, t, t_updated))

    # You can also define parameterized datatypes.
    # This example builds a simple parameterized list of sort T, with one
    # constructor "cons".
    sort = slv.mkParamSort("T")
    paramConsListSpec = slv.mkDatatypeDecl("paramlist", [sort])
    paramCons = slv.mkDatatypeConstructorDecl("cons")
    paramNil = slv.mkDatatypeConstructorDecl("nil")
    paramCons.addSelector("head", sort)
    paramCons.addSelectorSelf("tail")
    paramConsListSpec.addConstructor(paramCons)
    paramConsListSpec.addConstructor(paramNil)

    paramConsListSort = slv.mkDatatypeSort(paramConsListSpec)
    paramConsIntListSort = paramConsListSort.instantiate([slv.getIntegerSort()])
    paramConsList = paramConsListSort.getDatatype()

    a = slv.mkConst(paramConsIntListSort, "a")
    print("term {} is of sort {}".format(a, a.getSort()))

    head_a = slv.mkTerm(
            Kind.APPLY_SELECTOR,
            paramConsList["cons"].getSelector("head").getTerm(),
            a)
    print("head_a is {} of sort {}".format(head_a, head_a.getSort()))
    print("sort of cons is",
          paramConsList.getConstructor("cons").getTerm().getSort())

    assertion = slv.mkTerm(Kind.GT, head_a, slv.mkInteger(50))
    print("Assert", assertion)
    slv.assertFormula(assertion)
    print("Expect sat.")
    print("cvc5:", slv.checkSat())


if __name__ == "__main__":
    slv = cvc5.Solver()

    # This example builds a simple "cons list" of integers, with
    # two constructors, "cons" and "nil."

    # Building a datatype consists of two steps.
    # First, the datatype is specified.
    # Second, it is "resolved" to an actual sort, at which point function
    # symbols are assigned to its constructors, selectors, and testers.

    consListSpec = slv.mkDatatypeDecl("list") # give the datatype a name
    cons = slv.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", slv.getIntegerSort())
    cons.addSelectorSelf("tail")
    consListSpec.addConstructor(cons)
    nil = slv.mkDatatypeConstructorDecl("nil")
    consListSpec.addConstructor(nil)

    print("spec is {}".format(consListSpec))

    # Keep in mind that "DatatypeDecl" is the specification class for
    # datatypes---"DatatypeDecl" is not itself a cvc5 Sort.
    # Now that our Datatype is fully specified, we can get a Sort for it.
    # This step resolves the "SelfSort" reference and creates
    # symbols for all the constructors, etc.

    consListSort = slv.mkDatatypeSort(consListSpec)
    test(slv, consListSort)

    print("### Alternatively, use declareDatatype")

    cons2 = slv.mkDatatypeConstructorDecl("cons")
    cons2.addSelector("head", slv.getIntegerSort())
    cons2.addSelectorSelf("tail")
    nil2 = slv.mkDatatypeConstructorDecl("nil")
    consListSort2 = slv.declareDatatype("list2", cons2, nil2)
    test(slv, consListSort2)
