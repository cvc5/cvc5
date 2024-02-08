/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The lemma property definition.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__LEMMA_PROPERTY_H
#define CVC5__THEORY__LEMMA_PROPERTY_H

#include <iosfwd>

namespace cvc5::internal {
namespace theory {

/** Properties of lemmas */
enum class LemmaProperty : uint32_t
{
  // default
  NONE = 0,
  // whether the lemma is removable
  REMOVABLE = 1,
  // whether the processing of the lemma should send atoms to the caller
  SEND_ATOMS = 2,
  // whether the lemma is part of the justification for answering "sat"
  NEEDS_JUSTIFY = 4
};
/** Define operator lhs | rhs */
LemmaProperty operator|(LemmaProperty lhs, LemmaProperty rhs);
/** Define operator lhs |= rhs */
LemmaProperty& operator|=(LemmaProperty& lhs, LemmaProperty rhs);
/** Define operator lhs & rhs */
LemmaProperty operator&(LemmaProperty lhs, LemmaProperty rhs);
/** Define operator lhs &= rhs */
LemmaProperty& operator&=(LemmaProperty& lhs, LemmaProperty rhs);
/** is the removable bit set on p? */
bool isLemmaPropertyRemovable(LemmaProperty p);
/** is the send atoms bit set on p? */
bool isLemmaPropertySendAtoms(LemmaProperty p);
/** is the needs justify bit set on p? */
bool isLemmaPropertyNeedsJustify(LemmaProperty p);

/**
 * Writes an lemma property name to a stream.
 *
 * @param out The stream to write to
 * @param p The lemma property to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, LemmaProperty p);

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__LEMMA_PROPERTY_H */
