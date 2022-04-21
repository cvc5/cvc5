/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Info per pattern term in CCFV.
 */

#include "theory/quantifiers/ieval/match_pat_info.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

MatchPatInfo::MatchPatInfo() : d_watchEqcIndex(0) {}

void MatchPatInfo::addWatchEqc(TNode eqc)
{
  if (d_watchEqc.find(eqc) == d_watchEqc.end())
  {
    d_watchEqc.insert(eqc);
    d_watchEqcList.push_back(eqc);
  }
}

TNode MatchPatInfo::getNextWatchEqc()
{
  if (d_watchEqcIndex >= d_watchEqcList.size())
  {
    return TNode::null();
  }
  TNode next = d_watchEqcList[d_watchEqcIndex];
  d_watchEqcIndex = d_watchEqcIndex + 1;
  return next;
}

void MatchPatInfo::addMaybeEqc(TNode eqc) { d_maybeEqc.insert(eqc); }

bool MatchPatInfo::isMaybeEqc(TNode eqc) const
{
  return d_maybeEqc.find(eqc) != d_maybeEqc.end();
}

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
