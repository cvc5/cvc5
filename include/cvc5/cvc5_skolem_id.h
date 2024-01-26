/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Skolem identifier enumeration.
 */

#if (!defined(CVC5_API_USE_C_ENUMS)                 \
     && !defined(CVC5__API__CVC5_CPP_SKOLEM_ID_H)) \
    || (defined(CVC5_API_USE_C_ENUMS)               \
        && !defined(CVC5__API__CVC5_C_SKOLEM_ID_H))

#include <iosfwd>
#include <cstdint>

#ifdef CVC5_API_USE_C_ENUMS
#undef ENUM
#define ENUM(name) Cvc5##name
#else
#include <cvc5/cvc5_export.h>

#include <cstdint>
#include <ostream>
namespace cvc5 {
#undef ENUM
#define ENUM(name) class name
#define EVALUE(name) name
#endif

#ifdef CVC5_API_USE_C_ENUMS
#undef EVALUE
#define EVALUE(name) CVC5_SKOLEM_ID_##name
#endif

// clang-format off
/**
 * The kind of a cvc5 skolem
 *
 * \internal
 * 
 */
enum ENUM(SkolemFunId) : uint32_t
{
  /** The skolem is not exported */
  EVALUE(INTERNAL),
  
  /** input variable with a given name */
  EVALUE(INPUT_VARIABLE),
  /** purification skolem for a term t */
  EVALUE(PURIFY),
  /** array diff to witness (not (= A B)) */
  EVALUE(ARRAY_DEQ_DIFF),
  /** an uninterpreted function f s.t. f(x) = x / 0.0 (real division) */
  EVALUE(DIV_BY_ZERO),
  /** an uninterpreted function f s.t. f(x) = x / 0 (integer division) */
  EVALUE(INT_DIV_BY_ZERO),
  /** an uninterpreted function f s.t. f(x) = x mod 0 */
  EVALUE(MOD_BY_ZERO),
  /** an uninterpreted function f s.t. f(x) = sqrt(x) */
  EVALUE(SQRT),
  /**
   * Argument used to purify trancendental function app f(x).
   * For sin(x), this is a variable that is assumed to be in phase with x that
   * is between -pi and pi
   */
  EVALUE(TRANSCENDENTAL_PURIFY_ARG),
  /** a shared selector */
  EVALUE(SHARED_SELECTOR),
  /**
   * The n^th skolem for quantified formula Q. Its arguments are (Q,n).
   */
  EVALUE(QUANTIFIERS_SKOLEMIZE),
  /**
   * Quantifiers synth fun embedding, for function-to-synthesize, this the
   * first order datatype variable for f.
   */
  EVALUE(QUANTIFIERS_SYNTH_FUN_EMBED),
  //----- string skolems are cached based on (a, b)
  /** exists k. ( string b occurs k times in string a ) */
  EVALUE(STRINGS_NUM_OCCUR),
  /** exists k. ( regular expression b can be matched k times in a ) */
  EVALUE(STRINGS_NUM_OCCUR_RE),
  /** For function k: Int -> Int
   *   exists k.
   *     forall 0 <= x <= n,
   *       k(x) is the end index of the x^th occurrence of b in a
   *   where n is the number of occurrences of b in a, and k(0)=0.
   */
  EVALUE(STRINGS_OCCUR_INDEX),
  /** Same, but where b is a regular expression */
  EVALUE(STRINGS_OCCUR_INDEX_RE),
  /**
   * For function k: Int -> Int
   *   exists k.
   *     forall 0 <= x < n,
   *       k(x) is the length of the x^th occurrence of b in a (excluding
   *       matches of empty strings)
   *   where b is a regular expression, n is the number of occurrences of b
   *   in a, and k(0)=0.
   */
  EVALUE(STRINGS_OCCUR_LEN),
  /** Same, but where b is a regular expression */
  EVALUE(STRINGS_OCCUR_LEN_RE),
  /**
   * Diff index for disequalities a != b => substr(a,k,1) != substr(b,k,1)
   */
  EVALUE(STRINGS_DEQ_DIFF),
  //-----
  /**
   * A function used to define intermediate results of str.replace_all and
   * str.replace_re_all applications.
   */
  EVALUE(STRINGS_REPLACE_ALL_RESULT),
  /**
   * A function used to define intermediate results of str.from_int
   * applications.
   */
  EVALUE(STRINGS_ITOS_RESULT),
  /**
   * A function used to define intermediate results of str.to_int
   * applications.
   */
  EVALUE(STRINGS_STOI_RESULT),
  /**
   * An index containing a non-digit in a string, used when (str.to_int a) = -1.
   */
  EVALUE(STRINGS_STOI_NON_DIGIT),
  /**
   * For sequence a and regular expression b,
   * in_re(a, re.++(_*, b, _*)) =>
   *    exists k_pre, k_match, k_post.
   *       a = k_pre ++ k_match ++ k_post ^
   *       len(k_pre) = indexof_re(x, y, 0) ^
   *       (forall l. 0 < l < len(k_match) =>
   *         ~in_re(substr(k_match, 0, l), r)) ^
   *       in_re(k_match, b)
   *
   * k_pre is the prefix before the first, shortest match of b in a. k_match
   * is the substring of a matched by b. It is either empty or there is no
   * shorter string that matches b.
   */
  EVALUE(RE_FIRST_MATCH_PRE),
  EVALUE(RE_FIRST_MATCH),
  EVALUE(RE_FIRST_MATCH_POST),
  /**
   * Regular expression unfold component: if (str.in_re t R), where R is
   * (re.++ r0 ... rn), then the RE_UNFOLD_POS_COMPONENT{t,R,i} is a string
   * skolem ki such that t = (str.++ k0 ... kn) and (str.in_re k0 r0) for
   * i = 0, ..., n.
   */
  EVALUE(RE_UNFOLD_POS_COMPONENT),
  /** Sequence model construction, element for base */
  EVALUE(SEQ_MODEL_BASE_ELEMENT),
  EVALUE(BAGS_CARD_CARDINALITY),
  EVALUE(BAGS_CARD_ELEMENTS),
  EVALUE(BAGS_CARD_N),
  EVALUE(BAGS_CARD_UNION_DISJOINT),
  EVALUE(BAGS_FOLD_CARD),
  EVALUE(BAGS_FOLD_COMBINE),
  EVALUE(BAGS_FOLD_ELEMENTS),
  EVALUE(BAGS_FOLD_UNION_DISJOINT),
  /** An interpreted function for bag.choose operator:
   * (bag.choose A) is expanded as
   * (witness ((x elementType))
   *    (ite
   *      (= A (as emptybag (Bag E)))
   *      (= x (uf A))
   *      (and (>= (bag.count x A) 1) (= x (uf A)))
   * where uf: (Bag E) -> E is a skolem function, and E is the type of elements
   * of A
   */
  EVALUE(BAGS_CHOOSE),
  /** An uninterpreted function for bag.map operator:
   * To compute (bag.count y (bag.map f A)), we need to find the distinct
   * elements in A that are mapped to y by function f (i.e., preimage of {y}).
   * If n is the cardinality of this preimage, then
   * the preimage is the set {uf(1), ..., uf(n)}
   * where uf: Int -> E is a skolem function, and E is the type of elements of A
   */
  EVALUE(BAGS_MAP_PREIMAGE),
  /**
   * A skolem variable for the size of the preimage of {y} that is unique per
   * terms (bag.map f A), y which might be an element in (bag.map f A). (see the
   * documentation for BAGS_MAP_PREIMAGE)
   */
  EVALUE(BAGS_MAP_PREIMAGE_SIZE),
  /**
   * A skolem variable for the index that is unique per terms
   * (bag.map f A), y, preImageSize, y, e which might be an element in A.
   * (see the documentation for BAGS_MAP_PREIMAGE)
   */
  EVALUE(BAGS_MAP_PREIMAGE_INDEX),
  /** An uninterpreted function for bag.map operator:
   * If the preimage of {y} in A is {uf(1), ..., uf(n)} (see BAGS_MAP_PREIMAGE},
   * then the multiplicity of an element y in a bag (map f A) is sum(n),
   * where sum: Int -> Int is a skolem function such that:
   * sum(0) = 0
   * sum(i) = sum (i-1) + (bag.count (uf i) A)
   */
  EVALUE(BAGS_MAP_SUM),
  /** bag diff to witness (not (= A B)) */
  EVALUE(BAGS_DEQ_DIFF),
  /** Given a group term ((_ table.group n1 ... nk) A) of type (Bag (Table T))
   * this uninterpreted function maps elements of A to their parts in the
   * resulting partition. It has type (-> T (Table T))
   */
  EVALUE(TABLES_GROUP_PART),
  /**
   * Given a group term ((_ table.group n1 ... nk) A) of type (Bag (Table T))
   * and a part B of type (Table T), this function returns a skolem element
   * that is a member of B if B is not empty.
   */
  EVALUE(TABLES_GROUP_PART_ELEMENT),
  /** Given a group term ((_ rel.group n1 ... nk) A) of type (Set (Relation T))
   * this uninterpreted function maps elements of A to their parts in the
   * resulting partition. It has type (-> T (Relation T))
   */
  EVALUE(RELATIONS_GROUP_PART),
  /**
   * Given a group term ((_ rel.group n1 ... nk) A) of type (Set (Relation T))
   * and a part B of type (Relation T), this function returns a skolem element
   * that is a member of B if B is not empty.
   */
  EVALUE(RELATIONS_GROUP_PART_ELEMENT),
  /** An interpreted function for bag.choose operator:
   * (choose A) is expanded as
   * (witness ((x elementType))
   *    (ite
   *      (= A (as set.empty (Set E)))
   *      (= x (uf A))
   *      (and (set.member x A) (= x uf(A)))
   * where uf: (Set E) -> E is a skolem function, and E is the type of elements
   * of A
   */
  EVALUE(SETS_CHOOSE),
  /** set diff to witness (not (= A B)) */
  EVALUE(SETS_DEQ_DIFF),
  EVALUE(SETS_FOLD_CARD),
  EVALUE(SETS_FOLD_COMBINE),
  EVALUE(SETS_FOLD_ELEMENTS),
  EVALUE(SETS_FOLD_UNION),
  /**
   * A skolem variable that is unique per terms (set.map f A), y which is an
   * element in (set.map f A). The skolem is constrained to be an element in A,
   * and it is mapped to y by f.
   */
  EVALUE(SETS_MAP_DOWN_ELEMENT),
  /** Higher-order type match predicate, see HoTermDb */
  EVALUE(HO_TYPE_MATCH_PRED),
  //-------------------- internal
  /** abstract value for a term t */
  EVALUE(ABSTRACT_VALUE),
  /** the "none" term, for instantiation evaluation */
  EVALUE(IEVAL_NONE),
  /** the "some" term, for instantiation evaluation */
  EVALUE(IEVAL_SOME),
  /** sygus "any constant" placeholder */
  EVALUE(SYGUS_ANY_CONSTANT),
  //================================================= Unknown rule
  EVALUE(NONE),
};
// clang-format on

#ifdef CVC5_API_USE_C_ENUMS
#ifndef DOXYGEN_SKIP
typedef enum ENUM(SkolemFunId) ENUM(SkolemFunId);
#endif
#endif

#ifdef CVC5_API_USE_C_ENUMS

/**
 * Get a string representation of a Cvc5SkolemFunId.
 * @param rule The proof rule.
 * @return The string representation.
 */
const char* cvc5_skolem_id_to_string(Cvc5SkolemFunId kind);

/**
 * Hash function for Cvc5SkolemFunId.
 * @param rule The proof rule.
 * @return The hash value.
 */
size_t cvc5_skolem_id_hash(Cvc5SkolemFunId rule);

#else
/**
 * Converts a proof rule to a string. Note: This function is also used in
 * `safe_print()`. Changing this function name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param id The proof rule
 * @return The name of the proof rule
 */
const char* toString(SkolemFunId id);

/**
 * Writes a proof rule name to a stream.
 *
 * @param out The stream to write to
 * @param id The proof rule to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, SkolemFunId id);
}  // namespace cvc5

namespace std {
/**
 * Hash function for SkolemFunIds.
 */
template <>
struct CVC5_EXPORT hash<cvc5::SkolemFunId>
{
  /**
   * Hashes a SkolemFunId to a size_t.
   * @param rule The proof rule.
   * @return The hash value.
   */
  size_t operator()(cvc5::SkolemFunId rule) const;
};
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
