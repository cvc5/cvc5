/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Skolem identifier enumeration.
 */

#if (!defined(CVC5_API_USE_C_ENUMS)                \
     && !defined(CVC5__API__CVC5_CPP_SKOLEM_ID_H)) \
    || (defined(CVC5_API_USE_C_ENUMS)              \
        && !defined(CVC5__API__CVC5_C_SKOLEM_ID_H))

#ifdef CVC5_API_USE_C_ENUMS
#include <stddef.h>
#include <stdint.h>
#undef ENUM
#define ENUM(name) Cvc5##name
#else
#include <cvc5/cvc5_export.h>

#include <cstdint>
#include <ostream>
namespace cvc5 {
#undef ENUM
#define ENUM(name) class name
#undef EVALUE
#define EVALUE(name) name
#endif

#ifdef CVC5_API_USE_C_ENUMS
#undef EVALUE
#define EVALUE(name) CVC5_SKOLEM_ID_##name
#endif

// clang-format off
/**
 * The kind of a cvc5 skolem. A skolem is a (family of) internal functions or
 * constants that are introduced by cvc5. These symbols are treated as
 * uninterpreted internally. We track their definition for the purposes of
 * formal bookkeeping for the user of features like proofs, lemma exporting,
 * simplification and so on.
 * 
 * A skolem has an identifier and a set of "skolem indices". The skolem
 * indices are *not* children of the skolem function, but rather should
 * be seen as the way of distinguishing skolems from the same family.
 *
 * For example, the family of "array diff" skolems ``ARRAY_DEQ_DIFF`` witness
 * the disequality between two arrays, which are its skolem indices.
 * 
 * Say that skolem k witnesses the disequality between two arrays A and B
 * of type ``(Array Int Int)``. Then, k is a term whose skolem identifier is
 * ``ARRAY_DEQ_DIFF``, skolem indices are A and B, and whose type is ``Int``.
 * 
 * Note the type of k is not ``(-> (Array Int Int) (Array Int Int) Int)``.
 * Intuitively, this is due to the fact that cvc5 does not reason about array
 * diff skolem as a function symbol. Furthermore, the array diff skolem that
 * witnesses the disequality of arrays C and D is a separate skolem function k2
 * from this family, also of type ``Int``, where internally k2 has no relation
 * to k apart from having the same skolem identifier.
 * 
 * In contrast, cvc5 reasons about division-by-zero using a single skolem
 * function whose identifier is ``DIV_BY_ZERO``. This means its skolem indices
 * are empty and the skolem has a functional type ``(-> Real Real)``.
 *
 * \internal
 * 
 */
enum ENUM(SkolemId)
{
  /**
   * The identifier of the skolem is not exported. These skolems should not
   * appear in any user-level API calls.
   */
  EVALUE(INTERNAL),
  /** 
   * The purification skolem for a term. This is a variable that is semantically
   * equivalent to the indexed term t.
   * 
   * - Number of skolem indices: ``1``
   *   - ``1:`` The term t that this skolem purifies.
   * - Sort: The sort of t.
   */
  EVALUE(PURIFY),
  /** 
   * An arbitrary ground term of a given sort.
   * 
   * - Number of skolem indices: ``1``
   *   - ``1:`` A term that represents the sort of the term.
   * - Sort: The sort given by the index.
   */
  EVALUE(GROUND_TERM),
  /** 
   * The array diff skolem, which is the witness k for the inference
   * ``(=> (not (= A B)) (not (= (select A k) (select B k))))``.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` The first array of sort ``(Array T1 T2)``.
   *   - ``2:`` The second array of sort ``(Array T1 T2)``.
   * - Sort: ``T1``
   */
  EVALUE(ARRAY_DEQ_DIFF),
  /** 
   * The empty bitvector.
   *
   * - Number of skolem indices: ``0``
   * - Type: ``(_ BitVec 0)``
   */
  EVALUE(BV_EMPTY),
  /** 
   * The function for division by zero. This is semantically equivalent to the
   * SMT-LIB term ``(lambda ((x Real)) (/ x 0.0))``.
   *
   * - Number of skolem indices: ``0``
   * - Sort: ``(-> Real Real)``
   */
  EVALUE(DIV_BY_ZERO),
  /** 
   * The function for integer division by zero. This is semantically equivalent
   * to the SMT-LIB term ``(lambda ((x Int)) (div x 0))``.
   *
   * - Number of skolem indices: ``0``
   * - Sort: ``(-> Int Int)``
   */
  EVALUE(INT_DIV_BY_ZERO),
  /** 
   * The function for integer modulus by zero. This is semantically equivalent
   * to the SMT-LIB term ``(lambda ((x Int)) (mod x 0))``.
   *
   * - Number of skolem indices: ``0``
   * - Sort: ``(-> Int Int)``
   */
  EVALUE(MOD_BY_ZERO),
  /** 
   * A function introduced to eliminate extended trancendental functions.
   * Transcendental functions like sqrt, arccos, arcsin, etc. are replaced
   * during processing with uninterpreted functions that are unique to
   * each function.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` A lambda corresponding to the function, e.g. 
   *   `(lambda ((x Real)) (sqrt x))`.
   * - Sort: ``(-> Real Real)``
   */
  EVALUE(TRANSCENDENTAL_PURIFY),
  /**
   * Argument used to purify trancendental function app ``(f x)``.
   * For ``(sin x)``, this is a variable that is assumed to be in phase with
   * ``x`` that is between ``-pi`` and ``pi``.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` The application of a trancendental function.
   * - Sort: ``Real``
   */
  EVALUE(TRANSCENDENTAL_PURIFY_ARG),
  /** 
   * A shared datatype selector, see Reynolds et. al. "Datatypes with Shared
   * Selectors", IJCAR 2018. Represents a selector that can extract fields
   * of multiple constructors.
   *
   * - Number of skolem indices: ``3``
   *   - ``1:`` A term that represents the datatype we are extracting from.
   *   - ``2:`` A term that represents the sort of field we are extracting.
   *   - ``3:`` An integer n such that this shared selector returns the n^th
   *            subfield term of the given sort.
   * - Sort: A selector sort whose domain is given by first index,
   *         and whose codomain is the given by the second index.
   */
  EVALUE(SHARED_SELECTOR),
  /**
   * The n^th skolem for quantified formula Q.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` The quantified formula Q.
   *   - ``2:`` The variable in the binder of Q to skolemize.
   * - Sort: The type of the second index.
   */
  EVALUE(QUANTIFIERS_SKOLEMIZE),
  /** 
   * An integer corresponding to the number of times a string occurs in another
   * string. This is used to reason about str.replace_all.
   * 
   * - Number of skolem indices: ``2``
   *   - ``1:`` The first string.
   *   - ``2:`` The second string.
   * - Sort: ``Int``
   */
  EVALUE(STRINGS_NUM_OCCUR),
  /** 
   * A function k such that for x = 0...n, (k x) is the end
   * index of the x^th occurrence of a string b in string a, where n is the
   * number of occurrences of b in a, and ``(= (k 0) 0)``. This is used to
   * reason about str.replace_all.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` The first string.
   *   - ``2:`` The second string.
   * - Sort: ``(-> Int Int)``
   */
  EVALUE(STRINGS_OCCUR_INDEX),
  /**
   * Analogous to STRINGS_NUM_OCCUR, but for regular expressions.
   * An integer corresponding to the number of times a regular expression can
   * be matched in a string.  This is used to reason about str.replace_all_re.
   * 
   * - Number of skolem indices: ``2``
   *   - ``1:`` The string to match.
   *   - ``2:`` The regular expression to find.
   * - Sort: ``Int``
   */
  EVALUE(STRINGS_NUM_OCCUR_RE),
  /** 
   * Analogous to STRINGS_OCCUR_INDEX, but for regular expressions.
   * A function k such that for x = 0...n, (k x) is the end
   * index of the x^th occurrence of a regular expression R in string a, where
   * n is the number of occurrences of R in a, and ``(= (k 0) 0)``. This is used
   * to reason about str.replace_all_re.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` The string to match.
   *   - ``2:`` The regular expression to find.
   * - Sort: ``(-> Int Int)``
   */
  EVALUE(STRINGS_OCCUR_INDEX_RE),
  /**
   * A function k where for x = 0...n, ``(k x)`` is the length of
   * the x^th occurrence of R in a (excluding matches of empty strings) where R
   * is a regular expression, n is the number of occurrences of R in a, and
   * ``(= (k 0) 0)``.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` The string to match.
   *   - ``2:`` The regular expression to find.
   * - Sort: ``(-> Int Int)``
   */
  EVALUE(STRINGS_OCCUR_LEN_RE),
  /**
   * Difference index for string disequalities, such that k is the witness for
   * the inference
   *  ``(=> (not (= a b)) (not (= (substr a k 1) (substr b k 1))))``
   * where note that `k` may be out of bounds for at most of a,b.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` The first string.
   *   - ``2:`` The second string.
   * - Sort: ``Int``
   */
  EVALUE(STRINGS_DEQ_DIFF),
  /**
   * A function used to define intermediate results of str.replace_all and
   * str.replace_re_all applications. This denotes a function that denotes the
   * result of processing the string or sequence after processing the n^th
   * occurrence of string or match of the regular expression in the given
   * replace_all term.
   * 
   * - Number of skolem indices: ``1``
   *   - ``1:`` The application of replace_all or replace_all_re.
   * - Sort: ``(-> Int S)`` where S is either ``String`` or ``(Seq T)`` for
   * some ``T``.
   */
  EVALUE(STRINGS_REPLACE_ALL_RESULT),
  /**
   * A function used to define intermediate results of str.from_int
   * applications. This is a function k denoting the result
   * of processing the first n digits of the argument.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` The argument to str.from_int.
   * - Sort: ``(-> Int Int)``
   */
  EVALUE(STRINGS_ITOS_RESULT),
  /**
   * A function used to define intermediate results of str.from_int
   * applications. This is a function k of type ``(-> Int String)`` denoting the
   * result of processing the first n characters of the argument.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` The argument to str.to_int.
   * - Sort: ``(-> Int String)``
   */
  EVALUE(STRINGS_STOI_RESULT),
  /**
   * A position containing a non-digit in a string, used when ``(str.to_int a)``
   * is equal to -1. This is an integer that returns a position for which the
   * argument string is not a digit if one exists, or is unconstrained otherwise.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` The argument to str.to_int.
   * - Sort: ``Int``
   */
  EVALUE(STRINGS_STOI_NON_DIGIT),
  /**
   * The next three skolems are used to decompose the match of a regular
   * expression in string.
   *
   * For string a and regular expression R, this skolem is the prefix of
   * string a before the first, shortest match of R in a. Formally, if
   * ``(str.in_re a (re.++ (re.* re.allchar) R (re.* re.allchar)))``, then
   * there exists strings k_pre, k_match, k_post such that:
   *       ``(= a (str.++ k_pre k_match k_post))`` and
   *       ``(= (len k_pre) (indexof_re a R 0))`` and
   *       ``(forall ((l Int)) (=> (< 0 l (len k_match))
   *         (not (str.in_re (substr k_match 0 l) R))))`` and
   *       ``(str.in_re k_match R)``
   * This skolem is k_pre, and the proceeding two skolems are k_match and
   * k_post.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` The string.
   *   - ``2:`` The regular expression to match.
   * - Sort: ``String``
   */
  EVALUE(RE_FIRST_MATCH_PRE),
  /**
   * For string a and regular expression R, this skolem is the string that
   * the first, shortest match of R was matched to in a.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` The string.
   *   - ``2:`` The regular expression to match.
   * - Sort: ``String``
   */
  EVALUE(RE_FIRST_MATCH),
  /**
   * For string a and regular expression ``R``, this skolem is the remainder
   * of a after the first, shortest match of ``R`` in a.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` The string.
   *   - ``2:`` The regular expression to match.
   * - Sort: ``String``
   */
  EVALUE(RE_FIRST_MATCH_POST),
  /**
   * Regular expression unfold component: if ``(str.in_re a R)``, where R is
   * ``(re.++ R0 ... Rn)``, then the ``RE_UNFOLD_POS_COMPONENT`` for indices
   * (a,R,i) is a string ki such that ``(= a (str.++ k0 ... kn))`` and
   * ``(str.in_re k0 R0)`` for i = 0, ..., n.
   *
   * - Number of skolem indices: ``3``
   *   - ``1:`` The string.
   *   - ``2:`` The regular expression.
   *   - ``3:`` The index of the skolem.
   * - Sort: ``String``
   */
  EVALUE(RE_UNFOLD_POS_COMPONENT),
  /**
   * An uninterpreted function for bag.card operator:
   * To compute ``(bag.card A)``, we need a function that
   * counts multiplicities of distinct elements. We call this function
   * combine of type Int -> Int where:
   * combine(0) = 0.
   * combine(i) = m(elements(i), A) + combine(i-1) for 1 <= i <= n.
   * elements: a skolem function for (bag.fold f t A).
   *           See ``BAGS_DISTINCT_ELEMENTS``.
   * n: is the number of distinct elements in A.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` the bag argument A.
   * - Sort: ``(-> Int Int)``
   */
  EVALUE(BAGS_CARD_COMBINE),
  /**
   * An uninterpreted function for the union of distinct elements 
   * in a bag (Bag T). To compute operators like bag.card, 
   * we need a function for distinct elements in A of type (-> Int T)
   * (see ``BAGS_DISTINCT_ELEMENTS``).
   * We also need to restrict the range [1, n] to only elements in the bag 
   * as follows:
   * unionDisjoint(0) = bag.empty.
   * unionDisjoint(i) = disjoint union of {<elements(i), m(elements(i), A)>}
   *                    and unionDisjoint(i-1).
   * unionDisjoint(n) = A.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` the bag argument A of type (Bag T).
   * - Sort: ``(-> Int (Bag T))``
   */
  EVALUE(BAGS_DISTINCT_ELEMENTS_UNION_DISJOINT),
  /**
   * An uninterpreted function for bag.fold operator:
   * To compute ``(bag.fold f t A)``, we need to guess the cardinality n of
   * bag A using a skolem function with ``BAGS_FOLD_CARD`` id.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` the bag argument A.
   * - Sort: ``Int``
   */
  EVALUE(BAGS_FOLD_CARD),
  /**
   * An uninterpreted function for bag.fold operator:
   * To compute ``(bag.fold f t A)``, we need a function that
   * accumulates intermidiate values. We call this function
   * combine of type Int -> T2 where:
   * combine(0) = t
   * combine(i) = f(elements(i), combine(i - 1)) for 1 <= i <= n.
   * elements: a skolem function for (bag.fold f t A)
   *           see ``BAGS_FOLD_ELEMENTS``.
   * n: is the cardinality of A.
   * T2: is the type of initial value t.
   *
   * - Number of skolem indices: ``3``
   *   - ``1:`` the function f of type ``(-> T1 T2)``.
   *   - ``2:`` the initial value t of type ``T2``.
   *   - ``3:`` the bag argument A of type ``(Bag T1)``.
   * - Sort: ``(-> Int T2)``
   */
  EVALUE(BAGS_FOLD_COMBINE),
  /**
   * An uninterpreted function for bag.fold operator:
   * To compute ``(bag.fold f t A)``, we need a function for
   * elements of A. We call this function
   * elements of type ``(-> Int T1)`` where T1 is the type of
   * elements of A.
   * If the cardinality of A is n, then
   * A is the disjoint union of {elements(i)} for 1 <= i <= n.
   * See ``BAGS_FOLD_UNION_DISJOINT``.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` a bag argument A of type ``(Bag T1)``
   * - Sort: ``(-> Int T1)``
   */
  EVALUE(BAGS_FOLD_ELEMENTS),
  /**
   * An uninterpreted function for bag.fold operator:
   * To compute ``(bag.fold f t A)``, we need a function for
   * elements of A which is given by elements defined in
   * ``BAGS_FOLD_ELEMENTS``.
   * We also need unionDisjoint: ``(-> Int (Bag T1))`` to compute
   * the disjoint union such that:
   * unionDisjoint(0) = bag.empty.
   * unionDisjoint(i) = disjoint union of {elements(i)} and unionDisjoint (i-1).
   * unionDisjoint(n) = A.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` the bag argument A of type ``(Bag T1)``.
   * - Sort: ``(-> Int (Bag T1))``
   */
  EVALUE(BAGS_FOLD_UNION_DISJOINT),
  /**
   * An interpreted function ``uf`` for bag.choose operator:
   * ``(bag.choose A)`` is replaced by ``(uf A)`` along with the inference
   * that ``(>= (bag.count (uf A) A) 1)`` when ``A`` is non-empty.
   * where ``T`` is the type of elements of A.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` the bag to chose from, of type (Bag T).
   * - Sort: ``(-> (Bag T) T)``
   */
  EVALUE(BAGS_CHOOSE),
  /**
   * An uninterpreted function for distinct elements of a bag A, which returns
   * the n^th distinct element of the bag.
   * See ``BAGS_DISTINCT_ELEMENTS_UNION_DISJOINT``.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` the bag argument A of type ``(Bag T)``.
   * - Sort: ``(-> Int T)``
   */
  EVALUE(BAGS_DISTINCT_ELEMENTS),
  /**
   * A skolem variable for the size of the distinct elements of a bag A.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` the bag argument A.
   * - Sort: ``Int``
   */
  EVALUE(BAGS_DISTINCT_ELEMENTS_SIZE),
 /**
   * A skolem for the preimage of an element y in ``(bag.map f A)`` such that
   * ``(= (f x) y)`` where f: ``(-> E T)`` is an injective function.
   *
   * - Number of skolem indices: ``3``
   *   - ``1:`` the function f of type ``(-> E T)``.
   *   - ``2:`` the bag argument A of ``(Bag E)``.
   *   - ``3:`` the element argument y type ``T``.
   * - Sort: ``E``
   */
  EVALUE(BAGS_MAP_PREIMAGE_INJECTIVE),
  /**
   * A skolem variable for the index that is unique per terms
   * ``(bag.map f A)``, y, e where:
   * f: ``(-> E T)``,
   * A: ``(Bag E)``,
   * y: ``T``,
   * e: ``E``
   *
   * - Number of skolem indices: ``5``
   *   - ``1:`` a map term of the form ``(bag.map f A)``.
   *   - ``2:`` a skolem function with id ``BAGS_DISTINCT_ELEMENTS``.
   *   - ``3:`` a skolem function with id ``BAGS_DISTINCT_ELEMENTS_SIZE``.
   *   - ``4:`` an element y of type ``T`` representing the mapped value.
   *   - ``5:`` an element x of type ``E``.
   * - Sort: ``Int``
   */
  EVALUE(BAGS_MAP_INDEX),
  /**
   * An uninterpreted function for bag.map operator:
   * If bag A is {uf(1), ..., uf(n)} (see ``BAGS_DISTINCT_ELEMENTS``},
   * then the multiplicity of an element y in a bag ``(bag.map f A)`` is sum(n),
   * where sum: ``(-> Int Int)`` is a skolem function such that:
   * sum(0) = 0
   * sum(i) = sum (i-1) + (bag.count (uf i) A)
   *
   * - Number of skolem indices: ``3``
   *   - ``1:`` the function f of type ``(-> E T)``.
   *   - ``2:`` the bag argument A of ``(Bag E)``.
   *   - ``3:`` the element argument e type ``E``.
   * - Sort: ``(-> Int Int)``
   */
  EVALUE(BAGS_MAP_SUM),
  /** 
   * The bag diff skolem, which is the witness k for the inference
   * ``(=> (not (= A B)) (not (= (bag.count k A) (bag.count k B))))``.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` The first bag of type ``(Bag T)``.
   *   - ``2:`` The second bag of type ``(Bag T)``.
   * - Sort: ``T``
   */
  EVALUE(BAGS_DEQ_DIFF),
  /**
   * Given a group term ``((_ table.group n1 ... nk) A)`` of type
   * ``(Bag (Table T))``, this skolem maps elements of A to their parts in the
   * resulting partition.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` a group term of the form ``((_ table.group n1 ... nk) A)``.
   * - Sort: ``(-> T (Table T))``
   */
  EVALUE(TABLES_GROUP_PART),
  /**
   * Given a group term ``((_ table.group n1 ... nk) A)`` of type
   * ``(Bag (Table T))`` and a part B of type ``(Table T)``, this function
   * returns a skolem element that is a member of B if B is not empty.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` a group term of the form ``((_ table.group n1 ... nk) A)``.
   *   - ``2:`` a table B of type ``(Table T)``.
   * - Sort: ``T``
   */
  EVALUE(TABLES_GROUP_PART_ELEMENT),
  /**
   * Given a group term ``((_ rel.group n1 ... nk) A)`` of type
   * ``(Set (Relation T))`` this skolem maps elements of A to their parts in the
   * resulting partition. 
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` a relation of the form ``((_ rel.group n1 ... nk) A)``.
   * - Sort: ``(-> T (Relation T))``
   */
  EVALUE(RELATIONS_GROUP_PART),
  /**
   * Given a group term ((_ rel.group n1 ... nk) A) of type (Set (Relation T))
   * and a part B of type (Relation T), this function returns a skolem element
   * that is a member of B if B is not empty.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` a group term of the form ``((_ rel.group n1 ... nk) A)``.
   *   - ``2:`` a relation B of type ``(Relation T)``.
   * - Sort: ``T``
   */
  EVALUE(RELATIONS_GROUP_PART_ELEMENT),
  /**
   * An interpreted function for set.choose operator, where ``(set.choose A)``
   * is expanded to ``(uf A)`` along with the inference
   * ``(set.member (uf A) A))`` when ``A`` is non-empty,
   * where uf: ``(-> (Set E) E)`` is this skolem function, and E is the type of
   * elements of ``A``.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` a ground value for the type ``(Set E)``.
   * - Sort: ``(-> (Set E) E)``
   */
  EVALUE(SETS_CHOOSE),
  /** 
   * The set diff skolem, which is the witness k for the inference
   * ``(=> (not (= A B)) (not (= (set.member k A) (set.member k B))))``.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` The first set of type ``(Set E)``.
   *   - ``2:`` The second set of type ``(Set E)``.
   * - Sort: ``E``
   */
  EVALUE(SETS_DEQ_DIFF),
  /**
   * An uninterpreted function for set.fold operator:
   * To compute ``(set.fold f t A)``, we need to guess the cardinality n of
   * set A using a skolem function with SETS_FOLD_CARD id.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` the set argument A.
   * - Sort: ``Int``
   */
  EVALUE(SETS_FOLD_CARD),
  /**
   * An uninterpreted function for set.fold operator:
   * To compute ``(set.fold f t A)``, we need a function that
   * accumulates intermidiate values. We call this function
   * combine of type Int -> T2 where:
   * combine(0) = t
   * combine(i) = f(elements(i), combine(i - 1)) for 1 <= i <= n
   * elements: a skolem function for (set.fold f t A)
   *           see SETS_FOLD_ELEMENTS
   * n: is the cardinality of A
   * T2: is the type of initial value t
   *
   * - Number of skolem indices: ``3``
   *   - ``1:`` the function f of type ``(-> T1 T2)``.
   *   - ``2:`` the initial value t of type ``T2``.
   *   - ``3:`` the set argument A of type ``(Set T1)``.
   * - Sort: ``(-> Int T2)``
   */
  EVALUE(SETS_FOLD_COMBINE),
  /**
   * An uninterpreted function for set.fold operator:
   * To compute ``(set.fold f t A)``, we need a function for
   * elements of A. We call this function
   * elements of type ``(-> Int T)`` where T is the type of
   * elements of A.
   * If the cardinality of A is n, then
   * A is the union of {elements(i)} for 1 <= i <= n.
   * See SETS_FOLD_UNION_DISJOINT.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` a set argument A of type ``(Set T)``.
   * - Sort: ``(-> Int T)``
   */
  EVALUE(SETS_FOLD_ELEMENTS),
  /**
   * An uninterpreted function for set.fold operator:
   * To compute ``(set.fold f t A)``, we need a function for
   * elements of A which is given by elements defined in
   * SETS_FOLD_ELEMENTS.
   * We also need unionFn: ``(-> Int (Set E))`` to compute
   * the union such that:
   * unionFn(0) = set.empty
   * unionFn(i) = union of {elements(i)} and unionFn (i-1)
   * unionFn(n) = A
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` a set argument A of type ``(Set E)``.
   * - Sort: ``(-> Int (Set E))``
   */
  EVALUE(SETS_FOLD_UNION),
  /**
   * A skolem variable that is unique per terms ``(set.map f A)``, y which is an
   * element in ``(set.map f A)``. The skolem is constrained to be an element in
   * A, and it is mapped to y by f.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` a map term of the form ``(set.map f A)`` where A of type ``(Set E)``
   *   - ``2:`` the element argument y.
   * - Sort: ``E``
   */
  EVALUE(SETS_MAP_DOWN_ELEMENT),
  /**
   * A skolem function that is unique per floating-point sort, introduced for
   * the undefined zero case of ``fp.min``.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` The floating-point sort ``FP`` of the fp.min operator.
   * - Sort: ``(-> FP FP (_ BitVec 1))``
   */
  EVALUE(FP_MIN_ZERO),
  /**
   * A skolem function that is unique per floating-point sort, introduced for
   * the undefined zero case of ``fp.max``.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` The floating-point sort ``FP`` of the fp.max operator.
   * - Sort: ``(-> FP FP (_ BitVec 1))``
   */
  EVALUE(FP_MAX_ZERO),
  /**
   * A skolem function introduced for the undefined out-ouf-bounds case of
   * ``fp.to_ubv`` that is unique per floating-point sort and sort of the
   * arguments to the operator.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` The floating-point sort ``FP`` of operand of fp.to_ubv.
   *   - ``2:`` The bit-vector sort ``BV`` to convert to.
   * - Sort: ``(-> RoundingMode FP BV)``
   */
  EVALUE(FP_TO_UBV),
  /**
   * A skolem function introduced for the undefined out-ouf-bounds case of
   * ``fp.to_sbv`` that is unique per floating-point sort and sort of the
   * arguments to the operator.
   *
   * - Number of skolem indices: ``2``
   *   - ``1:`` The floating-point sort ``FP`` of operand of fp.to_sbv.
   *   - ``2:`` The bit-vector sort ``BV`` to convert to.
   * - Sort: ``(-> RoundingMode FP BV)``
   */
  EVALUE(FP_TO_SBV),
  /**
   * A skolem function introduced for the undefined of ``fp.to_real`` that is
   * unique per floating-point sort.
   *
   * - Number of skolem indices: ``1``
   *   - ``1:`` The floating-point sort ``FP`` of the operand of fp.to_real.
   * - Sort: ``(-> FP Real)``
   */
  EVALUE(FP_TO_REAL),
  //================================================= Unknown rule
  /** Indicates this is not a skolem. */
  EVALUE(NONE),
#ifdef CVC5_API_USE_C_ENUMS
  // must be last entry
  EVALUE(LAST),
#endif
};
// clang-format on

#ifdef CVC5_API_USE_C_ENUMS
#ifndef DOXYGEN_SKIP
typedef enum ENUM(SkolemId) ENUM(SkolemId);
#endif
#endif

#ifdef CVC5_API_USE_C_ENUMS

/**
 * Get a string representation of a Cvc5SkolemId.
 * @param id The skolem id.
 * @return The string representation.
 */
const char* cvc5_skolem_id_to_string(Cvc5SkolemId id);

/**
 * Hash function for Cvc5SkolemId.
 * @param id The skolem id.
 * @return The hash value.
 */
size_t cvc5_skolem_id_hash(Cvc5SkolemId id);

#else

/**
 * Writes a skolem id to a stream.
 *
 * @param out The stream to write to
 * @param id The skolem id to write to the stream
 * @return The stream
 */
CVC5_EXPORT std::ostream& operator<<(std::ostream& out, SkolemId id);
}  // namespace cvc5

namespace std {
/**
 * Hash function for SkolemIds.
 */
template <>
struct CVC5_EXPORT hash<cvc5::SkolemId>
{
  /**
   * Hashes a SkolemId to a size_t.
   * @param id The skolem id.
   * @return The hash value.
   */
  size_t operator()(cvc5::SkolemId id) const;
};
/**
 * Get the string representation of a given skolem identifier.
 * @param id The skolem identifier
 * @return The string representation.
 */
std::string to_string(cvc5::SkolemId id);

}  // namespace std

#endif
#endif

#ifdef CVC5_API_USE_C_ENUMS
#ifndef CVC5__API__CVC5_C_SKOLEM_ID_H
#define CVC5__API__CVC5_C_SKOLEM_ID_H
#endif
#else
#ifndef CVC5__API__CVC5_CPP_SKOLEM_ID_H
#define CVC5__API__CVC5_CPP_SKOLEM_ID_H
#endif
#endif
