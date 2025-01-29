#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Mudathir Mohamed, Aina Niemetz, Makai Mann
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
    tm = cvc5.TermManager()
    solver = cvc5.Solver(tm)

    # Set the logic
    solver.setLogic("ALL")

    # options
    solver.setOption("produce-models", "true")
    # we need finite model finding to answer sat problems with universal
    # quantified formulas
    solver.setOption("finite-model-find", "true")
    # we need sets extension to support set.universe operator
    solver.setOption("sets-exp", "true")

    integer = tm.getIntegerSort()
    set_ = tm.mkSetSort(integer)

    # Verify union distributions over intersection
    # (A union B) intersection C = (A intersection C) union (B intersection C)

    # (declare-sort Person 0)
    personSort = tm.mkUninterpretedSort("Person")

    # (Tuple Person)
    tupleArity1 = tm.mkTupleSort(personSort)
    # (Relation Person)
    relationArity1 = tm.mkSetSort(tupleArity1)

    # (Tuple Person Person)
    tupleArity2 = tm.mkTupleSort(personSort, personSort)
    # (Relation Person Person)
    relationArity2 = tm.mkSetSort(tupleArity2)

    # empty set
    emptySetTerm = tm.mkEmptySet(relationArity1)

    # empty relation
    emptyRelationTerm = tm.mkEmptySet(relationArity2)

    # universe set
    universeSet = tm.mkUniverseSet(relationArity1)

    # variables
    people = tm.mkConst(relationArity1, "people")
    males = tm.mkConst(relationArity1, "males")
    females = tm.mkConst(relationArity1, "females")
    father = tm.mkConst(relationArity2, "father")
    mother = tm.mkConst(relationArity2, "mother")
    parent = tm.mkConst(relationArity2, "parent")
    ancestor = tm.mkConst(relationArity2, "ancestor")
    descendant = tm.mkConst(relationArity2, "descendant")

    isEmpty1 = tm.mkTerm(Kind.EQUAL, males, emptySetTerm)
    isEmpty2 = tm.mkTerm(Kind.EQUAL, females, emptySetTerm)

    # (assert (= people (as set.universe (Relation Person))))
    peopleAreTheUniverse = tm.mkTerm(Kind.EQUAL, people, universeSet)
    # (assert (not (= males (as set.empty (Relation Person)))))
    maleSetIsNotEmpty = tm.mkTerm(Kind.NOT, isEmpty1)
    # (assert (not (= females (as set.empty (Relation Person)))))
    femaleSetIsNotEmpty = tm.mkTerm(Kind.NOT, isEmpty2)

    # (assert (= (set.inter males females)
    #            (as set.empty (Relation Person))))
    malesFemalesIntersection = tm.mkTerm(Kind.SET_INTER, males, females)
    malesAndFemalesAreDisjoint = \
            tm.mkTerm(Kind.EQUAL, malesFemalesIntersection, emptySetTerm)

    # (assert (not (= father (as set.empty (Relation Person Person)))))
    # (assert (not (= mother (as set.empty (Relation Person Person)))))
    isEmpty3 = tm.mkTerm(Kind.EQUAL, father, emptyRelationTerm)
    isEmpty4 = tm.mkTerm(Kind.EQUAL, mother, emptyRelationTerm)
    fatherIsNotEmpty = tm.mkTerm(Kind.NOT, isEmpty3)
    motherIsNotEmpty = tm.mkTerm(Kind.NOT, isEmpty4)

    # fathers are males
    # (assert (set.subset (rel.join father people) males))
    fathers = tm.mkTerm(Kind.RELATION_JOIN, father, people)
    fathersAreMales = tm.mkTerm(Kind.SET_SUBSET, fathers, males)

    # mothers are females
    # (assert (set.subset (rel.join mother people) females))
    mothers = tm.mkTerm(Kind.RELATION_JOIN, mother, people)
    mothersAreFemales = tm.mkTerm(Kind.SET_SUBSET, mothers, females)

    # (assert (= parent (set.union father mother)))
    unionFatherMother = tm.mkTerm(Kind.SET_UNION, father, mother)
    parentIsFatherOrMother = \
            tm.mkTerm(Kind.EQUAL, parent, unionFatherMother)

    # (assert (= ancestor (rel.tclosure parent)))
    transitiveClosure = tm.mkTerm(Kind.RELATION_TCLOSURE, parent)
    ancestorFormula = tm.mkTerm(Kind.EQUAL, ancestor, transitiveClosure)

    # (assert (= descendant (rel.transpose ancestor)))
    transpose = tm.mkTerm(Kind.RELATION_TRANSPOSE, ancestor)
    descendantFormula = tm.mkTerm(Kind.EQUAL, descendant, transpose)

    # (assert (forall ((x Person)) (not (set.member (tuple x x) ancestor))))
    x = tm.mkVar(personSort, "x")
    xxTuple = tm.mkTuple([x, x])
    member = tm.mkTerm(Kind.SET_MEMBER, xxTuple, ancestor)
    notMember = tm.mkTerm(Kind.NOT, member)

    quantifiedVariables = tm.mkTerm(Kind.VARIABLE_LIST, x)
    noSelfAncestor = tm.mkTerm(Kind.FORALL, quantifiedVariables, notMember)

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
