/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * RConsObligation class implementation.
 */

#include "rcons_obligation.h"

#include <sstream>

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "theory/datatypes/sygus_datatype_utils.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

RConsObligation::RConsObligation(TypeNode stn, Node t) : d_ts({t})
{
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  d_k = sm->mkDummySkolem("sygus_rcons", stn);
}

TypeNode RConsObligation::getType() const { return d_k.getType(); }

Node RConsObligation::getSkolem() const { return d_k; }

void RConsObligation::addBuiltin(Node builtin) { d_ts.emplace(builtin); }

const std::unordered_set<Node>& RConsObligation::getBuiltins() const
{
  return d_ts;
}

void RConsObligation::addCandidateSolution(Node candSol)
{
  d_candSols.emplace(candSol);
}

const std::unordered_set<Node>& RConsObligation::getCandidateSolutions() const
{
  return d_candSols;
}

void RConsObligation::addCandidateSolutionToWatchSet(Node candSol)
{
  d_watchSet.emplace(candSol);
}

const std::unordered_set<Node>& RConsObligation::getWatchSet() const
{
  return d_watchSet;
}

void RConsObligation::printCandSols(
    const RConsObligation* root,
    const std::vector<std::unique_ptr<RConsObligation>>& obs)
{
  std::unordered_set<Node> visited;
  std::vector<const RConsObligation*> stack;
  stack.push_back(root);
  Trace("sygus-rcons") << std::endl << "Eq classes: " << std::endl << '[';

  while (!stack.empty())
  {
    const RConsObligation* curr = stack.back();
    stack.pop_back();
    visited.emplace(curr->getSkolem());

    Trace("sygus-rcons") << std::endl
                         << "  " << *curr << std::endl
                         << "  {" << std::endl;

    for (const Node& candSol : curr->getCandidateSolutions())
    {
      Trace("sygus-rcons") << "    "
                           << datatypes::utils::sygusToBuiltin(candSol)
                           << std::endl;
      std::unordered_set<TNode> vars;
      expr::getVariables(candSol, vars);
      for (TNode var : vars)
      {
        if (visited.find(var) == visited.cend())
          for (const std::unique_ptr<RConsObligation>& ob : obs)
          {
            if (ob->getSkolem() == var)
            {
              stack.push_back(ob.get());
            }
          }
      }
    }
    Trace("sygus-rcons") << "  }" << std::endl;
  }

  Trace("sygus-rcons") << ']' << std::endl;
}

std::ostream& operator<<(std::ostream& out, const RConsObligation& ob)
{
  out << '(' << ob.getType() << ", " << ob.getSkolem() << ", {";
  std::unordered_set<Node>::const_iterator it = ob.getBuiltins().cbegin();
  out << *it;
  ++it;
  while (it != ob.getBuiltins().cend())
  {
    out << ", " << *it;
    ++it;
  }
  out << "})";
  return out;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
