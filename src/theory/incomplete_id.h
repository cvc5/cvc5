/*********************                                                        */
/*! \file incomplete_id.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Incompleteness enumeration.
 **/

#include "cvc4_private.h"

#include <iosfwd>

#ifndef CVC4__THEORY__INCOMPLETE_ID_H
#define CVC4__THEORY__INCOMPLETE_ID_H

namespace cvc5 {
namespace theory {

/**
 * Reasons for incompleteness in CVC4.
 */
enum class IncompleteId
{
  // the non-linear arithmetic solver was disabled
  ARITH_NL_DISABLED,
  // the non-linear arithmetic solver was incomplete
  ARITH_NL,
  // we failed to verify the correctness of a candidate solution in SyGuS
  QUANTIFIERS_SYGUS_NO_VERIFY,
  // relations were used in combination with set cardinality constraints
  SETS_RELS_CARD,
  // we skipped processing a looping word equation
  STRINGS_LOOP_SKIP,
  // we could not simplify a regular expression membership
  STRINGS_REGEXP_NO_SIMPLIFY,
  // HO extensionality axiom was disabled
  UF_HO_EXT_DISABLED,
  // UF+cardinality solver was disabled
  UF_CARD_DISABLED,
  
  //-------------------------------------- unknown
  UNKNOWN
};

/**
 * Converts an incompleteness id to a string.
 *
 * @param i The incompleteness identifier
 * @return The name of the incompleteness identifier
 */
const char* toString(IncompleteId i);

/**
 * Writes an incompleteness identifier to a stream.
 *
 * @param out The stream to write to
 * @param i The incompleteness identifier to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, IncompleteId i);

}  // namespace theory
}  // namespace cvc5

#endif /* CVC4__THEORY__INCOMPLETE_ID_H */
