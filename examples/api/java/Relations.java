/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of reasoning about relations with cvc5 via Java API.
 */

import static io.github.cvc5.api.Kind.*;

import io.github.cvc5.api.*;

/*
This file uses the API to make a sat call equivalent to the following benchmark:
(set-logic ALL)

(set-option :finite-model-find true)
(set-option :produce-models true)
(set-option :sets-ext true)

(declare-sort Person 0)

(declare-fun people () (Set (Tuple Person)))
(declare-fun males () (Set (Tuple Person)))
(declare-fun females () (Set (Tuple Person)))
(declare-fun father () (Set (Tuple Person Person)))
(declare-fun mother () (Set (Tuple Person Person)))
(declare-fun parent () (Set (Tuple Person Person)))
(declare-fun ancestor () (Set (Tuple Person Person)))
(declare-fun descendant () (Set (Tuple Person Person)))

(assert (= people (as set.universe (Set (Tuple Person)))))
(assert (not (= males (as set.empty (Set (Tuple Person))))))
(assert (not (= females (as set.empty (Set (Tuple Person))))))
(assert (= (set.inter males females) (as set.empty (Set (Tuple Person)))))
; father relation is not empty
(assert (not (= father (as set.empty (Set (Tuple Person Person))))))
; mother relation is not empty
(assert (not (= mother (as set.empty (Set (Tuple Person Person))))))
; fathers are males
(assert (set.subset (rel.join father people) males))
; mothers are females
(assert (set.subset (rel.join mother people) females))
; parent
(assert (= parent (set.union father mother)))
; no self ancestor
(assert (forall ((x Person)) (not (set.member (tuple x x) ancestor))))
; descendant
(assert (= descendant (rel.tclosure parent)))
; ancestor
(assert (= ancestor (rel.transpose descendant)))
(check-sat)
(get-model)
 */

public class Relations
{
  public static void main(String[] args) throws CVC5ApiException
  {
    try (Solver solver = new Solver())
    {
      // Set the logic
      solver.setLogic("ALL");

      // options
      solver.setOption("produce-models", "true");
      solver.setOption("finite-model-find", "true");
      solver.setOption("sets-ext", "true");
      solver.setOption("output-language", "smt2");

      // (declare-sort Person 0)
      Sort personSort = solver.mkUninterpretedSort("Person");

      // (Tuple Person)
      Sort tupleArity1 = solver.mkTupleSort(new Sort[] {personSort});
      // (Set (Tuple Person))
      Sort relationArity1 = solver.mkSetSort(tupleArity1);

      // (Tuple Person Person)
      Sort tupleArity2 = solver.mkTupleSort(new Sort[] {personSort, personSort});
      // (Set (Tuple Person Person))
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

      Term isEmpty1 = solver.mkTerm(EQUAL, males, emptySetTerm);
      Term isEmpty2 = solver.mkTerm(EQUAL, females, emptySetTerm);

      // (assert (= people (as set.universe (Set (Tuple Person)))))
      Term peopleAreTheUniverse = solver.mkTerm(EQUAL, people, universeSet);
      // (assert (not (= males (as set.empty (Set (Tuple Person))))))
      Term maleSetIsNotEmpty = solver.mkTerm(NOT, isEmpty1);
      // (assert (not (= females (as set.empty (Set (Tuple Person))))))
      Term femaleSetIsNotEmpty = solver.mkTerm(NOT, isEmpty2);

      // (assert (= (set.inter males females) (as set.empty (Set (Tuple
      // Person)))))
      Term malesFemalesIntersection = solver.mkTerm(SET_INTER, males, females);
      Term malesAndFemalesAreDisjoint =
          solver.mkTerm(EQUAL, malesFemalesIntersection, emptySetTerm);

      // (assert (not (= father (as set.empty (Set (Tuple Person Person))))))
      // (assert (not (= mother (as set.empty (Set (Tuple Person Person))))))
      Term isEmpty3 = solver.mkTerm(EQUAL, father, emptyRelationTerm);
      Term isEmpty4 = solver.mkTerm(EQUAL, mother, emptyRelationTerm);
      Term fatherIsNotEmpty = solver.mkTerm(NOT, isEmpty3);
      Term motherIsNotEmpty = solver.mkTerm(NOT, isEmpty4);

      // fathers are males
      // (assert (set.subset (rel.join father people) males))
      Term fathers = solver.mkTerm(RELATION_JOIN, father, people);
      Term fathersAreMales = solver.mkTerm(SET_SUBSET, fathers, males);

      // mothers are females
      // (assert (set.subset (rel.join mother people) females))
      Term mothers = solver.mkTerm(RELATION_JOIN, mother, people);
      Term mothersAreFemales = solver.mkTerm(SET_SUBSET, mothers, females);

      // (assert (= parent (set.union father mother)))
      Term unionFatherMother = solver.mkTerm(SET_UNION, father, mother);
      Term parentIsFatherOrMother = solver.mkTerm(EQUAL, parent, unionFatherMother);

      // (assert (= descendant (rel.tclosure parent)))
      Term transitiveClosure = solver.mkTerm(RELATION_TCLOSURE, parent);
      Term descendantFormula = solver.mkTerm(EQUAL, descendant, transitiveClosure);

      // (assert (= ancestor (rel.transpose descendant)))
      Term transpose = solver.mkTerm(RELATION_TRANSPOSE, descendant);
      Term ancestorFormula = solver.mkTerm(EQUAL, ancestor, transpose);

      // (assert (forall ((x Person)) (not (set.member (mkTuple x x) ancestor))))
      Term x = solver.mkVar(personSort, "x");
      DatatypeConstructor constructor = tupleArity2.getDatatype().getConstructor(0);
      Term xxTuple = solver.mkTerm(APPLY_CONSTRUCTOR, constructor.getConstructorTerm(), x, x);
      Term member = solver.mkTerm(SET_MEMBER, xxTuple, ancestor);
      Term notMember = solver.mkTerm(NOT, member);

      Term quantifiedVariables = solver.mkTerm(VARIABLE_LIST, x);
      Term noSelfAncestor = solver.mkTerm(FORALL, quantifiedVariables, notMember);

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
      System.out.println("Result     = " + result);
      System.out.println("people     = " + solver.getValue(people));
      System.out.println("males      = " + solver.getValue(males));
      System.out.println("females    = " + solver.getValue(females));
      System.out.println("father     = " + solver.getValue(father));
      System.out.println("mother     = " + solver.getValue(mother));
      System.out.println("parent     = " + solver.getValue(parent));
      System.out.println("descendant = " + solver.getValue(descendant));
      System.out.println("ancestor   = " + solver.getValue(ancestor));
    }
  }
}
