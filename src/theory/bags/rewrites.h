/*********************                                                        */
/*! \file rewrites.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Type for rewrites for bags.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__REWRITES_H
#define CVC4__THEORY__BAGS__REWRITES_H

#include <iosfwd>

namespace CVC4 {
namespace theory {
namespace bags {

/** Types of rewrites used by bags
 *
 * This rewrites are documented where they are used in the rewriter.
 */
enum class Rewrite : uint32_t
{
  NO_REWRITE,

};

/**
 * Converts an rewrite to a string. Note: This function is also used in
 * `safe_print()`. Changing this functions name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param r The rewrite
 * @return The name of the rewrite
 */
const char* toString(Rewrite r);

/**
 * Writes an rewrite name to a stream.
 *
 * @param out The stream to write to
 * @param r The rewrite to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, Rewrite r);

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__REWRITES_H */
