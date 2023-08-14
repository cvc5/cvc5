/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of subtype elimination node conversion
 */

#include "expr/canon_const_converter.h"

#include "expr/skolem_manager.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

CanonConstConverter::CanonConstConverter() {}

Node CanonConstConverter::preConvert(Node n)
{
  if (n.getKind() != kind::SKOLEM)
  {
    return n;
  }
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  SkolemFunId id;
  Node cacheVal;
  if (!sm->isSkolemFunction(n, id, cacheVal))
  {
    return n;
  }
  std::stringstream ss;
  ss << "(as (_ const " << id << ") " << n.getType() << ")";
  TypeNode ftype = n.getType();
  std::vector<Node> children;
  if (!cacheVal.isNull())
  {
    if (cacheVal.getKind() == kind::SEXPR)
    {
      children.insert(children.end(), cacheVal.begin(), cacheVal.end());
    }
    else
    {
      children.push_back(cacheVal);
    }
    std::vector<TypeNode> argTypes;
    for (const Node& c : children)
    {
      argTypes.push_back(c.getType());
    }
    ftype = nm->mkFunctionType(argTypes, ftype);
  }
  Node op = nm->mkRawSymbol(ss.str(), ftype);
  std::vector<Node> achildren;
  achildren.push_back(op);
  achildren.insert(achildren.end(), children.begin(), children.end());
  return nm->mkNode(kind::APPLY_UF, achildren);
}

}  // namespace cvc5::internal
