#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Mudathir Mohamed, Aina Niemetz, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5 relations solver
# through the Python API. This is a direct translation of relations.cpp.
##

import cvc5
from cvc5 import Kind

if __name__ == "__main__":
    solver = cvc5.Solver()

    # Set the logic
    solver.setLogic("ALL")

    # options
    solver.setOption("produce-models", "true")
    # we need finite model finding to answer sat problems with universal
    # quantified formulas
    solver.setOption("finite-model-find", "true")
    # we need sets extension to support set.universe operator
    solver.setOption("sets-ext", "true")

    integer = solver.getIntegerSort()
    set_ = solver.mkSetSort(integer)

    # Verify union distributions over intersection
    # (A union B) intersection C = (A intersection C) union (B intersection C)

    # (declare-sort Person 0)
    personSort = solver.mkUninterpretedSort("Person")

    # (Tuple Person)
    tupleArity1 = solver.mkTupleSort(personSort)
    # (Relation Person)
    relationArity1 = solver.mkSetSort(tupleArity1)

    # (Tuple Person Person)
    tupleArity2 = solver.mkTupleSort(personSort, personSort)
    # (Relation Person Person)
    relationArity2 = solver.mkSetSort(tupleArity2)

    # empty set
    emptySetTerm = solver.mkEmptySet(relationArity1)

    # empty relation
    emptyRelationTerm = solver.mkEmptySet(relationArity2)

    # universe set
    universeSet = solver.mkUniverseSet(relationArity1)

    # variables
    people = solver.mkConst(relationArity1, "people")
    males = solver.mkConst(relationArity1, "males")
    females = solver.mkConst(relationArity1, "females")
    father = solver.mkConst(relationArity2, "father")
    mother = solver.mkConst(relationArity2, "mother")
    parent = solver.mkConst(relationArity2, "parent")
    ancestor = solver.mkConst(relationArity2, "ancestor")
    descendant = solver.mkConst(relationArity2, "descendant")

    isEmpty1 = solver.mkTerm(Kind.EQUAL, males, emptySetTerm)
    isEmpty2 = solver.mkTerm(Kind.EQUAL, females, emptySetTerm)

    # (assert (= people (as set.universe (Relation Person))))
    peopleAreTheUniverse = solver.mkTerm(Kind.EQUAL, people, universeSet)
    # (assert (not (= males (as set.empty (Relation Person)))))
    maleSetIsNotEmpty = solver.mkTerm(Kind.NOT, isEmpty1)
    # (assert (not (= females (as set.empty (Relation Person)))))
    femaleSetIsNotEmpty = solver.mkTerm(Kind.NOT, isEmpty2)

    # (assert (= (set.inter males females)
    #            (as set.empty (Relation Person))))
    malesFemalesIntersection = solver.mkTerm(Kind.SET_INTER, males, females)
    malesAndFemalesAreDisjoint = \
            solver.mkTerm(Kind.EQUAL, malesFemalesIntersection, emptySetTerm)

    # (assert (not (= father (as set.empty (Relation Person Person)))))
    # (assert (not (= mother (as set.empty (Relation Person Person)))))
    isEmpty3 = solver.mkTerm(Kind.EQUAL, father, emptyRelationTerm)
    isEmpty4 = solver.mkTerm(Kind.EQUAL, mother, emptyRelationTerm)
    fatherIsNotEmpty = solver.mkTerm(Kind.NOT, isEmpty3)
    motherIsNotEmpty = solver.mkTerm(Kind.NOT, isEmpty4)

    # fathers are males
    # (assert (set.subset (rel.join father people) males))
    fathers = solver.mkTerm(Kind.RELATION_JOIN, father, people)
    fathersAreMales = solver.mkTerm(Kind.SET_SUBSET, fathers, males)

    # mothers are females
    # (assert (set.subset (rel.join mother people) females))
    mothers = solver.mkTerm(Kind.RELATION_JOIN, mother, people)
    mothersAreFemales = solver.mkTerm(Kind.SET_SUBSET, mothers, females)

    # (assert (= parent (set.union father mother)))
    unionFatherMother = solver.mkTerm(Kind.SET_UNION, father, mother)
    parentIsFatherOrMother = \
            solver.mkTerm(Kind.EQUAL, parent, unionFatherMother)

    # (assert (= ancestor (rel.tclosure parent)))
    transitiveClosure = solver.mkTerm(Kind.RELATION_TCLOSURE, parent)
    ancestorFormula = solver.mkTerm(Kind.EQUAL, ancestor, transitiveClosure)

    # (assert (= descendant (rel.transpose ancestor)))
    transpose = solver.mkTerm(Kind.RELATION_TRANSPOSE, ancestor)
    descendantFormula = solver.mkTerm(Kind.EQUAL, descendant, transpose)

    # (assert (forall ((x Person)) (not (set.member (tuple x x) ancestor))))
    x = solver.mkVar(personSort, "x")
    xxTuple = solver.mkTuple([x, x])
    member = solver.mkTerm(Kind.SET_MEMBER, xxTuple, ancestor)
    notMember = solver.mkTerm(Kind.NOT, member)

    quantifiedVariables = solver.mkTerm(Kind.VARIABLE_LIST, x)
    noSelfAncestor = solver.mkTerm(Kind.FORALL, quantifiedVariables, notMember)

    # formulas
    solver.assertFormula(peopleAreTheUniverse)
    solver.assertFormula(maleSetIsNotEmpty)
    solver.assertFormula(femaleSetIsNotEmpty)
    solver.assertFormula(malesAndFemalesAreDisjoint)
    solver.assertFormula(fatherIsNotEmpty)
    solver.assertFormula(motherIsNotEmpty)
    solver.assertFormula(fathersAreMales)
    solver.assertFormula(mothersAreFemales)
    solver.assertFormula(parentIsFatherOrMother)
    solver.assertFormula(descendantFormula)
    solver.assertFormula(ancestorFormula)
    solver.assertFormula(noSelfAncestor)

    # check sat
    result = solver.checkSat()

    # output
    print("Result     = {}".format(result))
    print("people     = {}".format(solver.getValue(people)))
    print("males      = {}".format(solver.getValue(males)))
    print("females    = {}".format(solver.getValue(females)))
    print("father     = {}".format(solver.getValue(father)))
    print("mother     = {}".format(solver.getValue(mother)))
    print("parent     = {}".format(solver.getValue(parent)))
    print("descendant = {}".format(solver.getValue(descendant)))
    print("ancestor   = {}".format(solver.getValue(ancestor)))
