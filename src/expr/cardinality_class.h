/*********************                                                        */
/*! \file cardinality_class.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for cardinality classes
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__CARDINALITY_CLASS_H
#define CVC4__EXPR__CARDINALITY_CLASS_H

#include <iosfwd>

#include "expr/type_node.h"

namespace cvc5 {

/** Constructor cardinality type */
enum class CardinalityClass
{
  // the cardinality is unknown
  UNKNOWN,
  // the type has cardinality one in all interpretations
  ONE,
  // the type has cardinality one under the assumption that uninterpreted sorts
  // have cardinality one
  INTERPRETED_ONE,
  // the type is finite in all interpretations
  FINITE,
  // the type is finite under the assumption that uninterpreted sorts have
  // cardinality one
  INTERPRETED_FINITE,
  // the type is infinte in all interpretations
  INFINITE
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

/** Get the class of type tn */
CardinalityClass getCardinalityClass(TypeNode tn);
/** Take the min class of c1 and c2 */
CardinalityClass minCardinalityClass(CardinalityClass c1, CardinalityClass c2);
/** Take the max class of c1 and c2 */
CardinalityClass maxCardinalityClass(CardinalityClass c1, CardinalityClass c2);

}  // namespace cvc5

#endif
