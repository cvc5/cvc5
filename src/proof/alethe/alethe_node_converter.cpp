/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Alethe node conversion
 */

#include "proof/alethe/alethe_node_converter.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"

namespace cvc5::internal {
namespace proof {

Node AletheNodeConverter::preConvert(Node n)
{
  Kind k = n.getKind();
  if (k == kind::SKOLEM || k == kind::BOOLEAN_TERM_VARIABLE)
  {
    Trace("alethe-conv") << "AletheNodeConverter: [PRE] handling skolem " << n
                         << "\n";
    Node wi = SkolemManager::getWitnessForm(n);
    // true skolem with witness form, just convert that
    if (!wi.isNull())
    {
      Trace("alethe-conv") << "AletheNodeConverter: ..skolem " << n
                           << " has witness form " << wi << "\n";
      return wi;
    }
    // purification skolem, so we simply retrieve its original form and convert
    // that
    Node oi = SkolemManager::getOriginalForm(n);
    AlwaysAssert(!oi.isNull());
    Trace("alethe-conv")
        << "AletheNodeConverter: ..pre-convert to original form " << oi << "\n";
    return oi;
  }
  return n;
}

Node AletheNodeConverter::postConvert(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  AlwaysAssert(k != kind::SKOLEM && k != kind::BOOLEAN_TERM_VARIABLE);
  switch (k)
  {
    case kind::FORALL:
    {
      // remove patterns, if any
      return n.getNumChildren() == 3 ? nm->mkNode(kind::FORALL, n[0], n[1]) : n;
    }
    // we must make it to be printed with "choice", so we create an operator
    // with that name and the correct type and do a function application
    case kind::WITNESS:
    {
      std::vector<TypeNode> childrenTypes;
      for (const Node& c : n)
      {
        childrenTypes.push_back(c.getType());
      }
      TypeNode fType = nm->mkFunctionType(childrenTypes, n.getType());
      Node choiceOp = mkInternalSymbol("choice", fType);
      return nm->mkNode(kind::APPLY_UF, choiceOp, n[0], n[1]);
    }
    default:
    {
      return n;
    }
  }
  return n;
}

Node AletheNodeConverter::mkInternalSymbol(const std::string& name)
{
  return mkInternalSymbol(name, NodeManager::currentNM()->sExprType());
}

Node AletheNodeConverter::mkInternalSymbol(const std::string& name, TypeNode tn)
{
  std::pair<TypeNode, std::string> key(tn, name);
  std::map<std::pair<TypeNode, std::string>, Node>::iterator it =
      d_symbolsMap.find(key);
  if (it != d_symbolsMap.end())
  {
    return it->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node sym = nm->mkBoundVar(name, tn);
  d_symbolsMap[key] = sym;
  return sym;
}

}  // namespace proof
}  // namespace cvc5::internal
