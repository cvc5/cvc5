/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The sort kinds of the cvc5 C++ API.
 */

#include <cvc5/cvc5_export.h>

#ifndef CVC5__API__CVC5_SORT_KIND_H
#define CVC5__API__CVC5_SORT_KIND_H

#include <ostream>

namespace cvc5 {

/* -------------------------------------------------------------------------- */
/* SortKind */
/* -------------------------------------------------------------------------- */

// clang-format off
/**
 * The kind of a cvc5 Sort.
 *
 * \internal
 *
 * Note that the API type `cvc5::SortKind` roughly corresponds to
 * `cvc5::internal::Kind`, but is a different type. It hides internal kinds
 * that should not be exported to the API, and maps all kinds that we want to
 * export to its corresponding internal kinds. The underlying type of
 * `cvc5::Kind` must be signed (to enable range checks for validity). The size
 * of this type depends on the size of `cvc5::internal::Kind`
 * (`NodeValue::NBITS_KIND`, currently 10 bits, see expr/node_value.h).
 */
enum SortKind : int32_t
{
  /**
   * Internal kind.
   *
   * This kind serves as an abstraction for internal kinds that are not exposed
   * via the API but may appear in terms returned by API functions, e.g.,
   * when querying the simplified form of a term.
   *
   * \rst
   * .. note:: Should never be created via the API.
   * \endrst
   */
  INTERNAL_SORT_KIND = -2,
  /**
   * Undefined kind.
   *
   * \rst
   * .. note:: Should never be exposed or created via the API.
   * \endrst
   */
  UNDEFINED_SORT_KIND = -1,
  /**
   * Null kind.
   *
   * The kind of a null sort (Sort::Sort()).
   *
   * \rst
   * .. note:: May not be explicitly created via API functions other than
   *           :cpp:func:`Sort::Sort()`.
   * \endrst
   */
  NULL_SORT,

  /* Sort Kinds ------------------------------------------------------------ */
  /**
   * An abstract sort.
   * 
   * An abstract sort represents a sort whose parameters or argument sorts are
   * unspecified. For example, `mkAbstractSort(BITVECTOR_SORT)` returns a
   * sort that represents the sort of bit-vectors whose bit-width is
   * unspecified.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkAbstractSort(SortKind) const
   */
  ABSTRACT_SORT,
  /**
   * An array sort, whose argument sorts are the index and element sorts of the
   * array.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkArraySort(Sort, Sort) const
   */
  ARRAY_SORT,
  /**
   * A bag sort, whose argument sort is the element sort of the bag.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkBagSort(Sort) const
   */
  BAG_SORT,
  /**
   * The Boolean sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::getBooleanSort() const
   */
  BOOLEAN_SORT,
  /**
   * A bit-vector sort, parameterized by an integer denoting its bit-width.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkBitVectorSort(uint32_t) const
   */
  BITVECTOR_SORT,
  /**
   * A datatype sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkDatatypeSort(DatatypeDecl)
   *   - Solver::mkDatatypeSorts(const std::vector<DatatypeDecl>&)
   */
  DATATYPE_SORT,
  /**
   * A finite field sort, parameterized by a size.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkFiniteFieldSort(const std::string&) const
   */
  FINITE_FIELD_SORT,
  /**
   * A floating-point sort, parameterized by two integers denoting its
   * exponent and significand bit-widths.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkFloatingPointSort(uint32_t, uint32_t) const
   */
  FLOATINGPOINT_SORT,
  /**
   * A function sort with given domain sorts and codomain sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkFunctionSort(const std::vector<Sort>&, Sort) const
   */
  FUNCTION_SORT,
  /**
   * The integer sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::getIntegerSort() const
   */
  INTEGER_SORT,
  /**
   * The real sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::getRealSort() const
   */
  REAL_SORT,
  /**
   * The regular language sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::getRegExpSort() const
   */
  REGLAN_SORT,
  /**
   * The rounding mode sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::getRoundingModeSort() const
   */
  ROUNDINGMODE_SORT,
  /**
   * A sequence sort, whose argument sort is the element sort of the sequence.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkSequenceSort(Sort) const
   */
  SEQUENCE_SORT,
  /**
   * A set sort, whose argument sort is the element sort of the set.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkSetSort(Sort) const
   */
  SET_SORT,
  /**
   * The string sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::getStringSort() const
   */
  STRING_SORT,
  /**
   * A tuple sort, whose argument sorts denote the sorts of the direct children
   * of the tuple.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkTupleSort(const std::vector<Sort>&) const
   */
  TUPLE_SORT,
  /**
   * An uninterpreted sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkUninterpretedSort(const std::optional<std::string>&) const
   */
  UNINTERPRETED_SORT,
  /* ----------------------------------------------------------------------- */
  /** Marks the upper-bound of this enumeration. */
  LAST_SORT_KIND
};
// clang-format on

/**
 * Get the string representation of a given kind.
 * @param k the sort kind
 * @return the string representation of kind k
 */
std::string sortKindToString(SortKind k) CVC5_EXPORT;

/**
 * Serialize a kind to given stream.
 * @param out the output stream
 * @param k the sort kind to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, SortKind k) CVC5_EXPORT;

}  // namespace cvc5

namespace std {

/**
 * Hash function for Kinds.
 */
template <>
struct CVC5_EXPORT hash<cvc5::SortKind>
{
  /**
   * Hashes a SortKind to a size_t.
   */
  size_t operator()(cvc5::SortKind k) const;
};

}  // namespace std

#endif
