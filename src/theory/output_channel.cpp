/*********************                                                        */
/*! \file output_channel.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory output channel interface
 **/

#include "theory/output_channel.h"

namespace CVC4 {
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
  return (p & LemmaProperty::REMOVABLE) != LemmaProperty::NONE;
}
bool isLemmaPropertyPreprocess(LemmaProperty p)
{
  return (p & LemmaProperty::PREPROCESS) != LemmaProperty::NONE;
}
bool isLemmaPropertySendAtoms(LemmaProperty p)
{
  return (p & LemmaProperty::SEND_ATOMS) != LemmaProperty::NONE;
}
bool isLemmaPropertyNeedsJustify(LemmaProperty p)
{
  return (p & LemmaProperty::NEEDS_JUSTIFY) != LemmaProperty::NONE;
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
    if (isLemmaPropertyPreprocess(p))
    {
      out << " PREPROCESS";
    }
    if (isLemmaPropertySendAtoms(p))
    {
      out << " SEND_ATOMS";
    }
    if (isLemmaPropertyNeedsJustify(p))
    {
      out << " NEEDS_JUSTIFY";
    }
    out << " }";
  }
  return out;
}

LemmaStatus::LemmaStatus(TNode rewrittenLemma, unsigned level)
    : d_rewrittenLemma(rewrittenLemma), d_level(level)
{
}

TNode LemmaStatus::getRewrittenLemma() const { return d_rewrittenLemma; }

unsigned LemmaStatus::getLevel() const { return d_level; }

LemmaStatus OutputChannel::split(TNode n)
{
  return splitLemma(n.orNode(n.notNode()));
}

void OutputChannel::trustedConflict(TrustNode pconf)
{
  Unreachable() << "OutputChannel::trustedConflict: no implementation"
                << std::endl;
}

LemmaStatus OutputChannel::trustedLemma(TrustNode lem, LemmaProperty p)
{
  Unreachable() << "OutputChannel::trustedLemma: no implementation"
                << std::endl;
}

}  // namespace theory
}  // namespace CVC4
