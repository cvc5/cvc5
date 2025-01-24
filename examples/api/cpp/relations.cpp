/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of reasoning about relations via the C++ API.
 */

#include <cvc5/cvc5.h>

#include <iostream>

using namespace cvc5;

int main()
{
  TermManager tm;
  Solver solver(tm);

  // Set the logic
  solver.setLogic("ALL");

  // options
  solver.setOption("produce-models", "true");
  // we need finite model finding to answer sat problems with universal
  // quantified formulas
  solver.setOption("finite-model-find", "true");
  // we need sets extension to support set.universe operator
  solver.setOption("sets-exp", "true");

  // (declare-sort Person 0)
  Sort personSort = tm.mkUninterpretedSort("Person");

  // (Tuple Person)
  Sort tupleArity1 = tm.mkTupleSort({personSort});
  // (Relation Person)
  Sort relationArity1 = tm.mkSetSort(tupleArity1);

  // (Tuple Person Person)
  Sort tupleArity2 = tm.mkTupleSort({personSort, personSort});
  // (Relation Person Person)
  Sort relationArity2 = tm.mkSetSort(tupleArity2);

  // empty set
  Term emptySetTerm = tm.mkEmptySet(relationArity1);

  // empty relation
  Term emptyRelationTerm = tm.mkEmptySet(relationArity2);

  // universe set
  Term universeSet = tm.mkUniverseSet(relationArity1);

  // variables
  Term people = tm.mkConst(relationArity1, "people");
  Term males = tm.mkConst(relationArity1, "males");
  Term females = tm.mkConst(relationArity1, "females");
  Term father = tm.mkConst(relationArity2, "father");
  Term mother = tm.mkConst(relationArity2, "mother");
  Term parent = tm.mkConst(relationArity2, "parent");
  Term ancestor = tm.mkConst(relationArity2, "ancestor");
  Term descendant = tm.mkConst(relationArity2, "descendant");

  Term isEmpty1 = tm.mkTerm(Kind::EQUAL, {males, emptySetTerm});
  Term isEmpty2 = tm.mkTerm(Kind::EQUAL, {females, emptySetTerm});

  // (assert (= people (as set.universe (Relation Person))))
  Term peopleAreTheUniverse = tm.mkTerm(Kind::EQUAL, {people, universeSet});
  // (assert (not (= males (as set.empty (Relation Person)))))
  Term maleSetIsNotEmpty = tm.mkTerm(Kind::NOT, {isEmpty1});
  // (assert (not (= females (as set.empty (Relation Person)))))
  Term femaleSetIsNotEmpty = tm.mkTerm(Kind::NOT, {isEmpty2});

  // (assert (= (set.inter males females)
  //            (as set.empty (Relation Person))))
  Term malesFemalesIntersection = tm.mkTerm(Kind::SET_INTER, {males, females});
  Term malesAndFemalesAreDisjoint =
      tm.mkTerm(Kind::EQUAL, {malesFemalesIntersection, emptySetTerm});

  // (assert (not (= father (as set.empty (Relation Person Person)))))
  // (assert (not (= mother (as set.empty (Relation Person Person)))))
  Term isEmpty3 = tm.mkTerm(Kind::EQUAL, {father, emptyRelationTerm});
  Term isEmpty4 = tm.mkTerm(Kind::EQUAL, {mother, emptyRelationTerm});
  Term fatherIsNotEmpty = tm.mkTerm(Kind::NOT, {isEmpty3});
  Term motherIsNotEmpty = tm.mkTerm(Kind::NOT, {isEmpty4});

  // fathers are males
  // (assert (set.subset (rel.join father people) males))
  Term fathers = tm.mkTerm(Kind::RELATION_JOIN, {father, people});
  Term fathersAreMales = tm.mkTerm(Kind::SET_SUBSET, {fathers, males});

  // mothers are females
  // (assert (set.subset (rel.join mother people) females))
  Term mothers = tm.mkTerm(Kind::RELATION_JOIN, {mother, people});
  Term mothersAreFemales = tm.mkTerm(Kind::SET_SUBSET, {mothers, females});

  // (assert (= parent (set.union father mother)))
  Term unionFatherMother = tm.mkTerm(Kind::SET_UNION, {father, mother});
  Term parentIsFatherOrMother =
      tm.mkTerm(Kind::EQUAL, {parent, unionFatherMother});

  // (assert (= ancestor (rel.tclosure parent)))
  Term transitiveClosure = tm.mkTerm(Kind::RELATION_TCLOSURE, {parent});
  Term ancestorFormula = tm.mkTerm(Kind::EQUAL, {ancestor, transitiveClosure});

  // (assert (= descendant (rel.transpose descendant)))
  Term transpose = tm.mkTerm(Kind::RELATION_TRANSPOSE, {ancestor});
  Term descendantFormula = tm.mkTerm(Kind::EQUAL, {descendant, transpose});

  // (assert (forall ((x Person)) (not (set.member (tuple x x) ancestor))))
  Term x = tm.mkVar(personSort, "x");
  Term xxTuple = tm.mkTuple({x, x});
  Term member = tm.mkTerm(Kind::SET_MEMBER, {xxTuple, ancestor});
  Term notMember = tm.mkTerm(Kind::NOT, {member});

  Term quantifiedVariables = tm.mkTerm(Kind::VARIABLE_LIST, {x});
  Term noSelfAncestor =
      tm.mkTerm(Kind::FORALL, {quantifiedVariables, notMember});

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
