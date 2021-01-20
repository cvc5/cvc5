/*********************                                                        */
/*! \file sygus_reconstruct.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Obligation Info class implementation
 **/

#include "obligation_info.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

ObligationInfo::ObligationInfo(const Node& builtin) : d_builtin(builtin) {}

const Node& ObligationInfo::getBuiltin() const { return d_builtin; }

void ObligationInfo::addCandidateSolution(const Node& candSol)
{
  d_candSols.emplace(candSol);
}

const std::unordered_set<Node, NodeHashFunction>&
ObligationInfo::getCandidateSolutions() const
{
  return d_candSols;
}

void ObligationInfo::addCandidateSolutionToWatchSet(const Node& candSol)
{
  d_watchSet.emplace(candSol);
}

const std::unordered_set<Node, NodeHashFunction>& ObligationInfo::getWatchSet()
    const
{
  return d_watchSet;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
