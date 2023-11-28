###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Aina Niemetz, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Two tests to validate the use of the separation logic API.
#
# First test validates that we cannot use the API if not using separation
# logic.
#
# Second test validates that the expressions returned from the API are
# correct and can be interrogated.
##

import cvc5
from cvc5 import Kind


# Test function to validate that we *cannot* obtain the heap/nil expressions
# when *not* using the separation logic theory
def validate_exception():
    slv = cvc5.Solver()
    # Setup some options for cvc5 -- we explictly want to use a simplistic
    # theory (e.g., QF_IDL)
    slv.setLogic("QF_IDL")
    slv.setOption("produce-models", "true")
    slv.setOption("incremental", "false")

    # Our integer type
    integer = slv.getIntegerSort()

    # we intentionally do not set the separation logic heap

    # Our SMT constants
    x = slv.mkConst(integer, "x")
    y = slv.mkConst(integer, "y")

    # y > x
    y_gt_x = slv.mkTerm(Kind.GT, y, x)

    # assert it
    slv.assertFormula(y_gt_x)

    # check
    r = slv.checkSat()

    # If this is UNSAT, we have an issue so bail-out
    if not r.isSat():
        return False

    # We now try to obtain our separation logic expressions from the solver --
    # we want to validate that we get our expected exceptions.

    caught_on_heap = False
    caught_on_nil = False

    # The exception message we expect to obtain
    expected = \
        "Cannot obtain separation logic expressions if not using the separation " \
        "logic theory."

    # test the heap expression
    try:
        heap_expr = slv.getValueSepHeap()
    except RuntimeError as e:
        caught_on_heap = True
        # Check we get the correct exception string
        if str(e) != expected:
            return False

    # test the nil expression
    try:
        nil_expr = slv.getValueSepNil()
    except RuntimeError as e:
        caught_on_nil = True

        # Check we get the correct exception string
        if str(e) != expected:
            return False

    if not caught_on_heap or not caught_on_nil:
        return False

    # All tests pass!
    return True


# Test function to demonstrate the use of, and validate the capability, of
# obtaining the heap/nil expressions when using separation logic.
def validate_getters():
    slv = cvc5.Solver()

    # Setup some options for cvc5
    slv.setLogic("QF_ALL")
    slv.setOption("produce-models", "true")
    slv.setOption("incremental", "false")

    # Our integer type
    integer = slv.getIntegerSort()

    #* Declare the separation logic heap types
    slv.declareSepHeap(integer, integer)

    # A "random" constant
    random_constant = slv.mkInteger(0xDEAD)

    # Another random constant
    expr_nil_val = slv.mkInteger(0xFBAD)

    # Our nil term
    nil = slv.mkSepNil(integer)

    # Our SMT constants
    x = slv.mkConst(integer, "x")
    y = slv.mkConst(integer, "y")
    p1 = slv.mkConst(integer, "p1")
    p2 = slv.mkConst(integer, "p2")

    # Constraints on x and y
    x_equal_const = slv.mkTerm(Kind.EQUAL, x, random_constant)
    y_gt_x = slv.mkTerm(Kind.GT, y, x)

    # Points-to expressions
    p1_to_x = slv.mkTerm(Kind.SEP_PTO, p1, x)
    p2_to_y = slv.mkTerm(Kind.SEP_PTO, p2, y)

    # Heap -- the points-to have to be "starred"!
    heap = slv.mkTerm(Kind.SEP_STAR, p1_to_x, p2_to_y)

    # Constain "nil" to be something random
    fix_nil = slv.mkTerm(Kind.EQUAL, nil, expr_nil_val)

    # Add it all to the solver!
    slv.assertFormula(x_equal_const)
    slv.assertFormula(y_gt_x)
    slv.assertFormula(heap)
    slv.assertFormula(fix_nil)

    # Incremental is disabled due to using separation logic, so don't query
    # twice!

    r = (slv.checkSat())

    # If this is UNSAT, we have an issue so bail-out
    if not r.isSat():
        return False

    # Obtain our separation logic terms from the solver
    heap_expr = slv.getValueSepHeap()
    nil_expr = slv.getValueSepNil()

    # If the heap is not a separating conjunction, bail-out
    if (heap_expr.getKind() != Kind.SEP_STAR):
        return False

    # If nil is not a direct equality, bail-out
    if (nil_expr.getKind() != Kind.EQUAL):
        return False

    # Obtain the values for our "pointers"
    val_for_p1 = slv.getValue(p1)
    val_for_p2 = slv.getValue(p2)

    # We need to make sure we find both pointers in the heap
    checked_p1 = False
    checked_p2 = False

    # Walk all the children
    for child in heap_expr:
        # If we don't have a PTO operator, bail-out
        if (child.getKind() != Kind.SEP_PTO):
            return False

        # Find both sides of the PTO operator
        addr = slv.getValue(child[0])
        value = slv.getValue(child[1])

        # If the current address is the value for p1
        if (addr == val_for_p1):
            checked_p1 = True

            # If it doesn't match the random constant, we have a problem
            if value != random_constant:
                return False
            continue

        if (addr == val_for_p2):
            checked_p2 = True

            # Our earlier constraint was that what p2 points to must be *greater*
            # than the random constant -- if we get a value that is LTE, then
            # something has gone wrong!

            if int(str(value)) <= int(str(random_constant)):
                return False
            continue

        # We should only have two addresses in heap, so if we haven't hit the
        # "continue" for p1 or p2, then bail-out

        return True

    # If we complete the loop and we haven't validated both p1 and p2, then we
    # have a problem
    if (not checked_p1 or not checked_p2):
        return False

    # We now get our value for what nil is
    value_for_nil = slv.getValue(nil_expr[1])

    # The value for nil from the solver should be the value we originally tied
    # nil to

    if (value_for_nil != expr_nil_val):
        return False

    # All tests pass!
    return True


# check that we get an exception when we should
assert validate_exception()

# check the getters
assert validate_getters()
