/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An example of accessing cvc5's statistics using the Java API.
 */

import static io.github.cvc5.Kind.*;

import io.github.cvc5.*;
import java.util.List;
import java.util.Map;

public class Statistics
{
  public static void main(String[] args)
  {
    Solver solver = new Solver();
    {
      // Get the statistics from the `Solver` and iterate over them. The
      // `Statistics` class implements the `Iterable<Pair<String, Stat>>` interface.
      io.github.cvc5.Statistics stats = solver.getStatistics();
      // short version
      System.out.println("Short version:");
      System.out.println(stats);

      System.out.println("-------------------------------------------------------");

      System.out.println("Long version:");

      // long version
      for (Map.Entry<String, Stat> pair : stats)
      {
        Stat stat = pair.getValue();
        if (stat.isInt())
        {
          System.out.println(pair.getKey() + " = " + stat.getInt());
        }
        else if (stat.isDouble())
        {
          System.out.println(pair.getKey() + " = " + stat.getDouble());
        }
        else if (stat.isString())
        {
          System.out.println(pair.getKey() + " = " + stat.getString());
        }
        else if (stat.isHistogram())
        {
          System.out.println("-------------------------------------------------------");
          System.out.println(pair.getKey() + " : Map");
          for (Map.Entry<String, Long> entry : stat.getHistogram().entrySet())
          {
            System.out.println(entry.getKey() + " = " + entry.getValue());
          }
          System.out.println("-------------------------------------------------------");
        }
      }
    }
  }

  private static Solver getSolver()
  {
    Solver solver = new Solver();

    // String type
    Sort string = solver.getStringSort();

    // std::string
    String str_ab = "ab";
    // String constants
    Term ab = solver.mkString(str_ab);
    Term abc = solver.mkString("abc");
    // String variables
    Term x = solver.mkConst(string, "x");
    Term y = solver.mkConst(string, "y");
    Term z = solver.mkConst(string, "z");

    // String concatenation: x.ab.y
    Term lhs = solver.mkTerm(STRING_CONCAT, x, ab, y);
    // String concatenation: abc.z
    Term rhs = solver.mkTerm(STRING_CONCAT, abc, z);
    // x.ab.y = abc.z
    Term formula1 = solver.mkTerm(EQUAL, lhs, rhs);

    // Length of y: |y|
    Term leny = solver.mkTerm(STRING_LENGTH, y);
    // |y| >= 0
    Term formula2 = solver.mkTerm(GEQ, leny, solver.mkInteger(0));

    // Regular expression: (ab[c-e]*f)|g|h
    Term r = solver.mkTerm(REGEXP_UNION,
        solver.mkTerm(REGEXP_CONCAT,
            solver.mkTerm(STRING_TO_REGEXP, solver.mkString("ab")),
            solver.mkTerm(REGEXP_STAR,
                solver.mkTerm(REGEXP_RANGE, solver.mkString("c"), solver.mkString("e"))),
            solver.mkTerm(STRING_TO_REGEXP, solver.mkString("f"))),
        solver.mkTerm(STRING_TO_REGEXP, solver.mkString("g")),
        solver.mkTerm(STRING_TO_REGEXP, solver.mkString("h")));

    // String variables
    Term s1 = solver.mkConst(string, "s1");
    Term s2 = solver.mkConst(string, "s2");
    // String concatenation: s1.s2
    Term s = solver.mkTerm(STRING_CONCAT, s1, s2);

    // s1.s2 in (ab[c-e]*f)|g|h
    Term formula3 = solver.mkTerm(STRING_IN_REGEXP, s, r);

    // Make a query
    Term q = solver.mkTerm(AND, formula1, formula2, formula3);

    // options
    solver.setOption("produce-models", "true");
    solver.setOption("finite-model-find", "true");
    solver.setOption("sets-ext", "true");
    solver.setOption("output-language", "smt2");

    // (declare-sort Person 0)
    Sort personSort = solver.mkUninterpretedSort("Person");

    // (Tuple Person)
    Sort tupleArity1 = solver.mkTupleSort(new Sort[] {personSort});
    // (Relation Person)
    Sort relationArity1 = solver.mkSetSort(tupleArity1);

    // (Tuple Person Person)
    Sort tupleArity2 = solver.mkTupleSort(new Sort[] {personSort, personSort});
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

    Term isEmpty1 = solver.mkTerm(EQUAL, males, emptySetTerm);
    Term isEmpty2 = solver.mkTerm(EQUAL, females, emptySetTerm);

    // (assert (= people (as set.universe (Relation Person))))
    Term peopleAreTheUniverse = solver.mkTerm(EQUAL, people, universeSet);
    // (assert (not (= males (as set.empty (Relation Person)))))
    Term maleSetIsNotEmpty = solver.mkTerm(NOT, isEmpty1);
    // (assert (not (= females (as set.empty (Relation Person)))))
    Term femaleSetIsNotEmpty = solver.mkTerm(NOT, isEmpty2);

    // (assert (= (set.inter males females) (as set.empty (Set (Tuple
    // Person)))))
    Term malesFemalesIntersection = solver.mkTerm(SET_INTER, males, females);
    Term malesAndFemalesAreDisjoint = solver.mkTerm(EQUAL, malesFemalesIntersection, emptySetTerm);

    // (assert (not (= father (as set.empty (Relation Person Person)))))
    // (assert (not (= mother (as set.empty (Relation Person Person)))))
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
    Term var = solver.mkVar(personSort, "x");
    DatatypeConstructor constructor = tupleArity2.getDatatype().getConstructor(0);
    Term xxTuple = solver.mkTerm(APPLY_CONSTRUCTOR, constructor.getTerm(), var, var);
    Term member = solver.mkTerm(SET_MEMBER, xxTuple, ancestor);
    Term notMember = solver.mkTerm(NOT, member);

    Term quantifiedVariables = solver.mkTerm(VARIABLE_LIST, var);
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
    solver.checkSatAssuming(q);

    return solver;
  }
}
