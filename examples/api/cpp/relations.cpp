/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of reasoning about relations with cvc5 via C++ API.
 */

#include <cvc5/cvc5.h>

#include <iostream>

using namespace cvc5;

int main()
{
  Solver solver;

  // Set the logic
  solver.setLogic("ALL");

  // options
  solver.setOption("produce-models", "true");
  // we need finite model finding to answer sat problems with universal
  // quantified formulas
  solver.setOption("finite-model-find", "true");
  // we need sets extension to support set.universe operator
  solver.setOption("sets-ext", "true");

  // (declare-sort Person 0)
  Sort personSort = solver.mkUninterpretedSort("Person");

  // (Tuple Person)
  Sort tupleArity1 = solver.mkTupleSort({personSort});
  // (Relation Person)
  Sort relationArity1 = solver.mkSetSort(tupleArity1);

  // (Tuple Person Person)
  Sort tupleArity2 = solver.mkTupleSort({personSort, personSort});
  // (Relation Person Person)
  Sort relationArity2 = solver.mkSetSort(tupleArity2);

  // empty set
  Term emptySetTerm = solver.mkEmptySet(relationArity1);

  // empty relation
  Term emptyRelationTerm = solver.mkEmptySet(relationArity2);

  // universe set
  Term universeSet = solver.mkUniverseSet(relationArity1);

  // variables
  Term people = solver.mkConst(relationArity1, "people");
  Term males = solver.mkConst(relationArity1, "males");
  Term females = solver.mkConst(relationArity1, "females");
  Term father = solver.mkConst(relationArity2, "father");
  Term mother = solver.mkConst(relationArity2, "mother");
  Term parent = solver.mkConst(relationArity2, "parent");
  Term ancestor = solver.mkConst(relationArity2, "ancestor");
  Term descendant = solver.mkConst(relationArity2, "descendant");

  Term isEmpty1 = solver.mkTerm(EQUAL, {males, emptySetTerm});
  Term isEmpty2 = solver.mkTerm(EQUAL, {females, emptySetTerm});

  // (assert (= people (as set.universe (Relation Person))))
  Term peopleAreTheUniverse = solver.mkTerm(EQUAL, {people, universeSet});
  // (assert (not (= males (as set.empty (Relation Person)))))
  Term maleSetIsNotEmpty = solver.mkTerm(NOT, {isEmpty1});
  // (assert (not (= females (as set.empty (Relation Person)))))
  Term femaleSetIsNotEmpty = solver.mkTerm(NOT, {isEmpty2});

  // (assert (= (set.inter males females)
  //            (as set.empty (Relation Person))))
  Term malesFemalesIntersection = solver.mkTerm(SET_INTER, {males, females});
  Term malesAndFemalesAreDisjoint =
      solver.mkTerm(EQUAL, {malesFemalesIntersection, emptySetTerm});

  // (assert (not (= father (as set.empty (Relation Person Person)))))
  // (assert (not (= mother (as set.empty (Relation Person Person)))))
  Term isEmpty3 = solver.mkTerm(EQUAL, {father, emptyRelationTerm});
  Term isEmpty4 = solver.mkTerm(EQUAL, {mother, emptyRelationTerm});
  Term fatherIsNotEmpty = solver.mkTerm(NOT, {isEmpty3});
  Term motherIsNotEmpty = solver.mkTerm(NOT, {isEmpty4});

  // fathers are males
  // (assert (set.subset (rel.join father people) males))
  Term fathers = solver.mkTerm(RELATION_JOIN, {father, people});
  Term fathersAreMales = solver.mkTerm(SET_SUBSET, {fathers, males});

  // mothers are females
  // (assert (set.subset (rel.join mother people) females))
  Term mothers = solver.mkTerm(RELATION_JOIN, {mother, people});
  Term mothersAreFemales = solver.mkTerm(SET_SUBSET, {mothers, females});

  // (assert (= parent (set.union father mother)))
  Term unionFatherMother = solver.mkTerm(SET_UNION, {father, mother});
  Term parentIsFatherOrMother =
      solver.mkTerm(EQUAL, {parent, unionFatherMother});

  // (assert (= ancestor (rel.tclosure parent)))
  Term transitiveClosure = solver.mkTerm(RELATION_TCLOSURE, {parent});
  Term ancestorFormula = solver.mkTerm(EQUAL, {ancestor, transitiveClosure});

  // (assert (= descendant (rel.transpose descendant)))
  Term transpose = solver.mkTerm(RELATION_TRANSPOSE, {ancestor});
  Term descendantFormula = solver.mkTerm(EQUAL, {descendant, transpose});

  // (assert (forall ((x Person)) (not (set.member (tuple x x) ancestor))))
  Term x = solver.mkVar(personSort, "x");
  Term xxTuple = solver.mkTuple({x, x});
  Term member = solver.mkTerm(SET_MEMBER, {xxTuple, ancestor});
  Term notMember = solver.mkTerm(NOT, {member});

  Term quantifiedVariables = solver.mkTerm(VARIABLE_LIST, {x});
  Term noSelfAncestor = solver.mkTerm(FORALL, {quantifiedVariables, notMember});

  // formulas
  solver.assertFormula(peopleAreTheUniverse);
  solver.assertFormula(maleSetIsNotEmpty);
  solver.assertFormula(femaleSetIsNotEmpty);
  solver.assertFormula(malesAndFemalesAreDisjoint);
  solver.assertFormula(fatherIsNotEmpty);
  solver.assertFormula(motherIsNotEmpty);
  solver.assertFormula(fathersAreMales);
  solver.assertFormula(mothersAreFemales);
  solver.assertFormula(parentIsFatherOrMother);
  solver.assertFormula(descendantFormula);
  solver.assertFormula(ancestorFormula);
  solver.assertFormula(noSelfAncestor);

  // check sat
  Result result = solver.checkSat();

  // output
  std::cout << "Result     = " << result << std::endl;
  std::cout << "people     = " << solver.getValue(people) << std::endl;
  std::cout << "males      = " << solver.getValue(males) << std::endl;
  std::cout << "females    = " << solver.getValue(females) << std::endl;
  std::cout << "father     = " << solver.getValue(father) << std::endl;
  std::cout << "mother     = " << solver.getValue(mother) << std::endl;
  std::cout << "parent     = " << solver.getValue(parent) << std::endl;
  std::cout << "descendant = " << solver.getValue(descendant) << std::endl;
  std::cout << "ancestor   = " << solver.getValue(ancestor) << std::endl;
}
