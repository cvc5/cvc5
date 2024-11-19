/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of reasoning about relations via the C API.
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);

  // Set the logic
  cvc5_set_logic(slv, "ALL");

  // options
  cvc5_set_option(slv, "produce-models", "true");
  // we need finite model finding to answer sat problems with universal
  // quantified formulas
  cvc5_set_option(slv, "finite-model-find", "true");
  // we need sets extension to support set.universe operator
  cvc5_set_option(slv, "sets-exp", "true");

  // (declare-sort Person 0)
  Cvc5Sort person_sort = cvc5_mk_uninterpreted_sort(tm, "Person");

  // (Tuple Person)
  Cvc5Sort sorts1[1] = {person_sort};
  Cvc5Sort tuple_arity1 = cvc5_mk_tuple_sort(tm, 1, sorts1);
  // (Relation Person)
  Cvc5Sort rel_arity1 = cvc5_mk_set_sort(tm, tuple_arity1);

  // (Tuple Person Person)
  Cvc5Sort sorts2[2] = {person_sort, person_sort};
  Cvc5Sort tuple_arity2 = cvc5_mk_tuple_sort(tm, 2, sorts2);
  // (Relation Person Person)
  Cvc5Sort rel_arity2 = cvc5_mk_set_sort(tm, tuple_arity2);

  // empty set
  Cvc5Term empty_set = cvc5_mk_empty_set(tm, rel_arity1);

  // empty relation
  Cvc5Term empty_rel = cvc5_mk_empty_set(tm, rel_arity2);

  // universe set
  Cvc5Term universe_set = cvc5_mk_universe_set(tm, rel_arity1);

  // variables
  Cvc5Term people = cvc5_mk_const(tm, rel_arity1, "people");
  Cvc5Term males = cvc5_mk_const(tm, rel_arity1, "males");
  Cvc5Term females = cvc5_mk_const(tm, rel_arity1, "females");
  Cvc5Term father = cvc5_mk_const(tm, rel_arity2, "father");
  Cvc5Term mother = cvc5_mk_const(tm, rel_arity2, "mother");
  Cvc5Term parent = cvc5_mk_const(tm, rel_arity2, "parent");
  Cvc5Term ancestor = cvc5_mk_const(tm, rel_arity2, "ancestor");
  Cvc5Term descendant = cvc5_mk_const(tm, rel_arity2, "descendant");

  Cvc5Term args2[2] = {males, empty_set};
  Cvc5Term is_empty1 = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  args2[0] = females;
  Cvc5Term is_empty2 = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);

  // (assert (= people (as set.universe (Relation Person))))
  args2[0] = people;
  args2[1] = universe_set;
  Cvc5Term people_universe = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  // (assert (not (= males (as set.empty (Relation Person)))))
  Cvc5Term args1[1] = {is_empty1};
  Cvc5Term male_not_empty = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, args1);
  // (assert (not (= females (as set.empty (Relation Person)))))
  args1[0] = is_empty2;
  Cvc5Term female_not_empty = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, args1);

  // (assert (= (set.inter males females)
  //            (as set.empty (Relation Person))))
  args2[0] = males;
  args2[1] = females;
  Cvc5Term inter_males_females =
      cvc5_mk_term(tm, CVC5_KIND_SET_INTER, 2, args2);
  args2[0] = inter_males_females;
  args2[1] = empty_set;
  Cvc5Term disjoint_males_females = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);

  // (assert (not (= father (as set.empty (Relation Person Person)))))
  // (assert (not (= mother (as set.empty (Relation Person Person)))))
  args2[0] = father;
  args2[1] = empty_rel;
  Cvc5Term is_empty3 = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  args2[0] = mother;
  args2[1] = empty_rel;
  Cvc5Term is_empty4 = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);
  args1[0] = is_empty3;
  Cvc5Term father_not_empty = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, args1);
  args1[0] = is_empty4;
  Cvc5Term mother_not_empty = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, args1);

  // fathers are males
  // (assert (set.subset (rel.join father people) males))
  args2[0] = father;
  args2[1] = people;
  Cvc5Term fathers = cvc5_mk_term(tm, CVC5_KIND_RELATION_JOIN, 2, args2);
  args2[0] = fathers;
  args2[1] = males;
  Cvc5Term fathers_are_males = cvc5_mk_term(tm, CVC5_KIND_SET_SUBSET, 2, args2);

  // mothers are females
  // (assert (set.subset (rel.join mother people) females))
  args2[0] = mother;
  args2[1] = people;
  Cvc5Term mothers = cvc5_mk_term(tm, CVC5_KIND_RELATION_JOIN, 2, args2);
  args2[0] = mothers;
  args2[1] = females;
  Cvc5Term mothers_are_females =
      cvc5_mk_term(tm, CVC5_KIND_SET_SUBSET, 2, args2);

  // (assert (= parent (set.union father mother)))
  args2[0] = father;
  args2[1] = mother;
  Cvc5Term union_father_mother =
      cvc5_mk_term(tm, CVC5_KIND_SET_UNION, 2, args2);
  args2[0] = parent;
  args2[1] = union_father_mother;
  Cvc5Term parent_is_father_or_mother =
      cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);

  // (assert (= ancestor (rel.tclosure parent)))
  args1[0] = parent;
  Cvc5Term trans_closure =
      cvc5_mk_term(tm, CVC5_KIND_RELATION_TCLOSURE, 1, args1);
  args2[0] = ancestor;
  args2[1] = trans_closure;
  Cvc5Term ancestor_formula = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);

  // (assert (= descendant (rel.transpose descendant)))
  args1[0] = ancestor;
  Cvc5Term transpose = cvc5_mk_term(tm, CVC5_KIND_RELATION_TRANSPOSE, 1, args1);
  args2[0] = descendant;
  args2[1] = transpose;
  Cvc5Term descendant_formula = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args2);

  // (assert (forall ((x Person)) (not (set.member (tuple x x) ancestor))))
  Cvc5Term x = cvc5_mk_var(tm, person_sort, "x");
  args2[0] = x;
  args2[1] = x;
  Cvc5Term xx_tuple = cvc5_mk_tuple(tm, 2, args2);
  args2[0] = xx_tuple;
  args2[1] = ancestor;
  Cvc5Term member = cvc5_mk_term(tm, CVC5_KIND_SET_MEMBER, 2, args2);
  args1[0] = member;
  Cvc5Term not_member = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, args1);

  args1[0] = x;
  Cvc5Term vars = cvc5_mk_term(tm, CVC5_KIND_VARIABLE_LIST, 1, args1);
  args2[0] = vars;
  args2[1] = not_member;
  Cvc5Term not_self_ancestor = cvc5_mk_term(tm, CVC5_KIND_FORALL, 2, args2);

  // formulas
  cvc5_assert_formula(slv, people_universe);
  cvc5_assert_formula(slv, male_not_empty);
  cvc5_assert_formula(slv, female_not_empty);
  cvc5_assert_formula(slv, disjoint_males_females);
  cvc5_assert_formula(slv, father_not_empty);
  cvc5_assert_formula(slv, mother_not_empty);
  cvc5_assert_formula(slv, fathers_are_males);
  cvc5_assert_formula(slv, mothers_are_females);
  cvc5_assert_formula(slv, parent_is_father_or_mother);
  cvc5_assert_formula(slv, descendant_formula);
  cvc5_assert_formula(slv, ancestor_formula);
  cvc5_assert_formula(slv, not_self_ancestor);

  // check sat
  Cvc5Result result = cvc5_check_sat(slv);

  // output
  printf("Result     = %s\n", cvc5_result_to_string(result));
  printf("people     = %s\n", cvc5_term_to_string(cvc5_get_value(slv, people)));
  printf("males      = %s\n", cvc5_term_to_string(cvc5_get_value(slv, males)));
  printf("females    = %s\n",
         cvc5_term_to_string(cvc5_get_value(slv, females)));
  printf("father     = %s\n", cvc5_term_to_string(cvc5_get_value(slv, father)));
  printf("mother     = %s\n", cvc5_term_to_string(cvc5_get_value(slv, mother)));
  printf("parent     = %s\n", cvc5_term_to_string(cvc5_get_value(slv, parent)));
  printf("descendant = %s\n",
         cvc5_term_to_string(cvc5_get_value(slv, descendant)));
  printf("ancestor   = %s\n",
         cvc5_term_to_string(cvc5_get_value(slv, ancestor)));

  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
}
