/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of subtype elimination node conversion
 */

#include "expr/subtype_elim_node_converter.h"

#include "expr/skolem_manager.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

SubtypeElimNodeConverter::SubtypeElimNodeConverter(NodeManager* nm)
    : NodeConverter(nm)
{
}

bool SubtypeElimNodeConverter::isRealTypeStrict(TypeNode tn)
{
  return tn.isReal();
}

Node SubtypeElimNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  bool convertToRealChildren = false;
  if (k == Kind::ADD || k == Kind::MULT || k == Kind::NONLINEAR_MULT
      || k == Kind::SUB)
  {
    convertToRealChildren = isRealTypeStrict(n.getType());
  }
  else if (k == Kind::TO_INTEGER || k == Kind::IS_INTEGER)
  {
    // always ensure that the arguments of these operators are Real
    convertToRealChildren = true;
  }
  else if (k == Kind::DIVISION || k == Kind::DIVISION_TOTAL || k == Kind::GEQ
           || k == Kind::GT || k == Kind::LEQ || k == Kind::LT)
  {
    // Each of the above terms we allow overloading (both arguments Int, or both
    // arguments Real) but not mixing arithmetic types.
    // This means that we allow real division between integer terms here, in
    // contrast to the SMT-LIB standard which only defines real division for
    // real terms. We do so to allow rational constants e.g. (/ 1 3) to be
    // represented as division terms, which avoids the need for logic-specific
    // parsing of the syntax for rational values in SMT-LIB.
    convertToRealChildren =
        isRealTypeStrict(n[0].getType()) || isRealTypeStrict(n[1].getType());
  }
  // note that EQUAL is strictly typed so we don't need to handle it here
  // also TO_REAL applied to reals is always rewritten, so it doesn't need to
  // be handled.
  if (convertToRealChildren)
  {
    std::vector<Node> children;
    bool childChanged = false;
    for (const Node& nc : n)
    {
      if (nc.getType().isInteger())
      {
        childChanged = true;
        if (nc.isConst())
        {
          // we convert constant integers to constant reals
          children.push_back(d_nm->mkConstReal(nc.getConst<Rational>()));
        }
        else
        {
          // otherwise, use TO_REAL
          children.push_back(d_nm->mkNode(Kind::TO_REAL, nc));
        }
      }
      else
      {
        children.push_back(nc);
      }
    }
    if (!childChanged)
    {
      return n;
    }
    return d_nm->mkNode(k, children);
  }
  // convert skolems as well, e.g. the purify skolem for (> 1 0.0) becomes the
  // purify skolem for (> 1.0 0.0).
  if (n.isVar())
  {
    SkolemManager* skm = d_nm->getSkolemManager();
    SkolemId id;
    Node cacheVal;
    if (skm->isSkolemFunction(n, id, cacheVal))
    {
      Node cacheValc = convert(cacheVal);
      if (cacheValc != cacheVal)
      {
        return skm->mkSkolemFunction(id, cacheValc);
      }
    }
  }
  return n;
}

}  // namespace cvc5::internal
