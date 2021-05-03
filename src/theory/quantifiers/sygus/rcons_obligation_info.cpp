/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Reconstruct Obligation Info class implementation.
 */

#include "rcons_obligation_info.h"

#include <sstream>

#include "expr/node_algorithm.h"
#include "theory/datatypes/sygus_datatype_utils.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

RConsObligationInfo::RConsObligationInfo(Node builtin) : d_builtins({builtin})
{
}

const std::unordered_set<Node, NodeHashFunction>&
RConsObligationInfo::getBuiltins() const
{
  return d_builtins;
}

void RConsObligationInfo::addCandidateSolution(Node candSol)
{
  d_candSols.emplace(candSol);
}

void RConsObligationInfo::addBuiltin(Node builtin)
{
  d_builtins.emplace(builtin);
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

std::string RConsObligationInfo::obToString(Node k,
                                            const RConsObligationInfo& obInfo)
{
  std::stringstream ss;
  ss << "([";
  std::unordered_set<Node, NodeHashFunction>::const_iterator it =
      obInfo.getBuiltins().cbegin();
  ss << *it;
  ++it;
  while (it != obInfo.getBuiltins().cend())
  {
    ss << ", " << *it;
    ++it;
  }
  ss << "]), " << k.getType() << ')' << std::endl;
  return ss.str();
}

void RConsObligationInfo::printCandSols(
    const Node& root,
    const std::unordered_map<Node, RConsObligationInfo, NodeHashFunction>&
        obInfo)
{
  std::unordered_set<Node, NodeHashFunction> visited;
  std::vector<Node> stack;
  stack.push_back(root);

  Trace("sygus-rcons") << "\nEq classes: \n[";

  while (!stack.empty())
  {
    const Node& k = stack.back();
    stack.pop_back();
    visited.emplace(k);

    Trace("sygus-rcons") << std::endl
                         << datatypes::utils::sygusToBuiltin(k) << " "
                         << obToString(k, obInfo.at(k)) << ":\n [";

    for (const Node& j : obInfo.at(k).getCandidateSolutions())
    {
      Trace("sygus-rcons") << datatypes::utils::sygusToBuiltin(j) << " ";
      std::unordered_set<TNode, TNodeHashFunction> subObs;
      expr::getVariables(j, subObs);
      for (const TNode& l : subObs)
      {
        if (visited.find(l) == visited.cend()
            && obInfo.find(l) != obInfo.cend())
        {
          stack.push_back(l);
        }
      }
    }
    Trace("sygus-rcons") << "]" << std::endl;
  }

  Trace("sygus-rcons") << "]" << std::endl;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
