/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The lemma property definition
 */

#include "theory/lemma_property.h"

#include <ostream>

namespace cvc5::internal {
namespace theory {

LemmaProperty operator|(LemmaProperty lhs, LemmaProperty rhs)
{
  return static_cast<LemmaProperty>(static_cast<uint32_t>(lhs)
                                    | static_cast<uint32_t>(rhs));
}
LemmaProperty& operator|=(LemmaProperty& lhs, LemmaProperty rhs)
{
  lhs = lhs | rhs;
  return lhs;
}
LemmaProperty operator&(LemmaProperty lhs, LemmaProperty rhs)
{
  return static_cast<LemmaProperty>(static_cast<uint32_t>(lhs)
                                    & static_cast<uint32_t>(rhs));
}
LemmaProperty& operator&=(LemmaProperty& lhs, LemmaProperty rhs)
{
  lhs = lhs & rhs;
  return lhs;
}
bool isLemmaPropertyRemovable(LemmaProperty p)
{
  return (p & LemmaProperty::REMOVABLE) == LemmaProperty::REMOVABLE;
}
bool isLemmaPropertySendAtoms(LemmaProperty p)
{
  return (p & LemmaProperty::SEND_ATOMS) == LemmaProperty::SEND_ATOMS;
}
bool isLemmaPropertyNeedsJustify(LemmaProperty p)
{
  return (p & LemmaProperty::NEEDS_JUSTIFY) == LemmaProperty::NEEDS_JUSTIFY;
}
bool isLemmaPropertyInprocess(LemmaProperty p)
{
  return (p & LemmaProperty::INPROCESS) == LemmaProperty::INPROCESS;
}
bool isLemmaPropertyLocal(LemmaProperty p)
{
  return (p & LemmaProperty::LOCAL) == LemmaProperty::LOCAL;
}

std::ostream& operator<<(std::ostream& out, LemmaProperty p)
{
  if (p == LemmaProperty::NONE)
  {
    out << "NONE";
  }
  else
  {
    out << "{";
    if (isLemmaPropertyRemovable(p))
    {
      out << " REMOVABLE";
    }
    if (isLemmaPropertySendAtoms(p))
    {
      out << " SEND_ATOMS";
    }
    if (isLemmaPropertyNeedsJustify(p))
    {
      out << " NEEDS_JUSTIFY";
    }
    if (isLemmaPropertyInprocess(p))
    {
      out << " INPROCESS";
    }
    if (isLemmaPropertyLocal(p))
    {
      out << " LOCAL";
    }
    out << " }";
  }
  return out;
}

}  // namespace theory
}  // namespace cvc5::internal
