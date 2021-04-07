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
