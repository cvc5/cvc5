/*********************                                                        */
/*! \file rcons_obligation_info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Reconstruct Obligation Info class implementation
 **/

#include "rcons_obligation_info.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

RConsObligationInfo::RConsObligationInfo(Node builtin) : d_builtin(builtin) {}

Node RConsObligationInfo::getBuiltin() const { return d_builtin; }

void RConsObligationInfo::addCandidateSolution(Node candSol)
{
  d_candSols.emplace(candSol);
}

const std::unordered_set<Node, NodeHashFunction>&
RConsObligationInfo::getCandidateSolutions() const
{
  return d_candSols;
}

void RConsObligationInfo::addCandidateSolutionToWatchSet(Node candSol)
{
  d_watchSet.emplace(candSol);
}

const std::unordered_set<Node, NodeHashFunction>&
RConsObligationInfo::getWatchSet() const
{
  return d_watchSet;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
