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

Node Obligation::getSkolem() const { return d_k; }

TypeNode Obligation::getType() const { return d_k.getType(); }

const std::unordered_set<Node, NodeHashFunction>& Obligation::getBuiltins()
    const
{
  return d_ts;
}

void Obligation::addCandidateSolution(Node candSol)
{
  d_candSols.emplace(candSol);
}

void Obligation::addBuiltin(Node builtin) { d_ts.emplace(builtin); }

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
    const std::vector<std::unique_ptr<Obligation>>& obs)
{
  Trace("sygus-rcons") << std::endl << "Eq classes: " << std::endl << '[';

  for (const std::unique_ptr<Obligation>& ob : obs)
  {
    Trace("sygus-rcons") << std::endl
                         << "  "
                         << datatypes::utils::sygusToBuiltin(ob->getSkolem())
                         << ' ' << *ob << std::endl << "  {" << std::endl;

    for (const Node& j : ob->getCandidateSolutions())
    {
      Trace("sygus-rcons") << "    " << datatypes::utils::sygusToBuiltin(j)
                           << std::endl;
    }
    Trace("sygus-rcons") << "  }" << std::endl;
  }

  Trace("sygus-rcons") << ']' << std::endl;
}

std::ostream& operator<<(std::ostream& out, const Obligation& ob)
{
  out << '(' << ob.getType()  << ", {";
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
