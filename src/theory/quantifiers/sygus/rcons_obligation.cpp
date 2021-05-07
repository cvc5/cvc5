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

#include "rcons_obligation.h"

#include <sstream>

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "theory/datatypes/sygus_datatype_utils.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

Obligation::Obligation(TypeNode stn, Node t) : d_ts({t})
{
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  d_k = sm->mkDummySkolem("sygus_rcons", stn);
}

TypeNode Obligation::getType() const { return d_k.getType(); }

Node Obligation::getSkolem() const { return d_k; }

void Obligation::addBuiltin(Node builtin) { d_ts.emplace(builtin); }

const std::unordered_set<Node, NodeHashFunction>& Obligation::getBuiltins()
    const
{
  return d_ts;
}

void Obligation::addCandidateSolution(Node candSol)
{
  d_candSols.emplace(candSol);
}

const std::unordered_set<Node, NodeHashFunction>&
Obligation::getCandidateSolutions() const
{
  return d_candSols;
}

void Obligation::addCandidateSolutionToWatchSet(Node candSol)
{
  d_watchSet.emplace(candSol);
}

const std::unordered_set<Node, NodeHashFunction>& Obligation::getWatchSet()
    const
{
  return d_watchSet;
}

void Obligation::printCandSols(
    const Obligation* root, const std::vector<std::unique_ptr<Obligation>>& obs)
{
  std::unordered_set<Node, NodeHashFunction> visited;
  std::vector<const Obligation*> stack;
  stack.push_back(root);
  Trace("sygus-rcons") << std::endl << "Eq classes: " << std::endl << '[';

  while (!stack.empty())
  {
    const Obligation* curr = stack.back();
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
      std::unordered_set<TNode, TNodeHashFunction> vars;
      expr::getVariables(candSol, vars);
      for (TNode var : vars)
      {
        if (visited.find(var) == visited.cend())
          for (const std::unique_ptr<Obligation>& ob : obs)
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

std::ostream& operator<<(std::ostream& out, const Obligation& ob)
{
  out << '(' << ob.getType() << ", " << ob.getSkolem() << ", {";
  std::unordered_set<Node, NodeHashFunction>::const_iterator it =
      ob.getBuiltins().cbegin();
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
}  // namespace cvc5
