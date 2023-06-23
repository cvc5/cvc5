/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for cardinality classes.
 */

#include "cvc5_private.h"

#ifndef CVC5__UTIL__CARDINALITY_CLASS_H
#define CVC5__UTIL__CARDINALITY_CLASS_H

#include <iosfwd>

namespace cvc5::internal {

/**
 * Cardinality classes. A type has exactly one cardinality class. The
 * cardinality class of a type is independent of the state of solver.
 *
 * The purposes of these classifications is solely to determine whether or not
 * a type should be considered finite. This includes use cases for when
 * finite model finding is enabled or disabled.
 *
 * Note that the order of this enum is important for the implementation of
 * minCardinalityClass and maxCardinalityClass below.
 */
enum class CardinalityClass : uint64_t
{
  // the type has cardinality one in all interpretations
  //
  // Examples: unit datatypes, arrays with unit datatype elements
  ONE,
  // the type has cardinality one under the assumption that uninterpreted
  // sorts have cardinality one
  //
  // Examples: uninterpreted sorts, arrays with uninterpreted sort elements
  INTERPRETED_ONE,
  // the type is finite in all interpretations, and does not fit any of the
  // above classifications
  //
  // Examples: Booleans, bitvectors, floating points, sets of Bools
  FINITE,
  // the type is finite under the assumption that uninterpreted sorts have
  // cardinality one, and does not fit any of the above classifications
  //
  // Examples: sets of uninterpreted sorts, arrays whose index types are
  // uninterpreted sorts and element sorts are finite
  INTERPRETED_FINITE,
  // the type is infinite in all interpretations
  //
  // Examples: integers, reals, strings, sequences, bags
  INFINITE,
  // the cardinality is unknown
  UNKNOWN
};

/**
 * Converts a cardinality class to a string.
 *
 * @param c The proof rule
 * @return The name of the proof rule
 */
const char* toString(CardinalityClass c);

/**
 * Writes a cardinality class name to a stream.
 *
 * @param out The stream to write to
 * @param c The cardinality class to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, CardinalityClass c);

/** Take the max class of c1 and c2 */
CardinalityClass maxCardinalityClass(CardinalityClass c1, CardinalityClass c2);
/**
 * Is a type with the given cardinality class finite?
 *
 * If fmfEnabled is true, then this method assumes that uninterpreted sorts
 * have cardinality one. If fmfEnabled is false, then this method assumes that
 * uninterpreted sorts have infinite cardinality.
 */
bool isCardinalityClassFinite(CardinalityClass c, bool fmfEnabled);

}  // namespace cvc5::internal

#endif
