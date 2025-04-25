/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * FiniteFields theory rewriter.
 */

#include "theory/ff/theory_ff_rewriter.h"

#include "expr/algorithm/flatten.h"
#include "expr/attribute.h"
#include "expr/node_manager.h"
#include "util/finite_field_value.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

TheoryFiniteFieldsRewriter::TheoryFiniteFieldsRewriter(NodeManager* nm)
    : TheoryRewriter(nm)
{
}

Node TheoryFiniteFieldsRewriter::mkNary(Kind k, std::vector<Node>&& children)
{
  Assert(children.size() > 0);
  if (children.size() == 1)
  {
    return children[0];
  }
  else
  {
    return nodeManager()->mkNode(k, std::move(children));
  }
}

std::pair<Node, FiniteFieldValue> TheoryFiniteFieldsRewriter::parseScalar(
    TNode t)
{
  const TypeNode field = t.getType();
  Assert(field.isFiniteField());
  FiniteFieldValue scalar = FiniteFieldValue::mkOne(field.getFfSize());
  Node node = t;
  if (t.getKind() == Kind::FINITE_FIELD_MULT && t[0].isConst())
  {
    std::vector<Node> restChildren(std::next(t.begin()), t.end());
    node = mkNary(Kind::FINITE_FIELD_MULT, std::move(restChildren));
    scalar = t[0].getConst<FiniteFieldValue>();
  }
  return {node, scalar};
}

Node TheoryFiniteFieldsRewriter::preRewriteFfNeg(TNode t)
{
  Assert(t.getKind() == Kind::FINITE_FIELD_NEG);
  NodeManager* const nm = nodeManager();
  const Node negOne =
      nm->mkConst(FiniteFieldValue(Integer(-1), t.getType().getFfSize()));
  return nm->mkNode(Kind::FINITE_FIELD_MULT, negOne, t[0]);
}

Node TheoryFiniteFieldsRewriter::preRewriteFfAdd(TNode t)
{
  Assert(t.getKind() == Kind::FINITE_FIELD_ADD);
  return expr::algorithm::flatten(d_nm, t);
}

Node TheoryFiniteFieldsRewriter::postRewriteFfAdd(TNode t)
{
  const TypeNode field = t.getType();
  Assert(field.isFiniteField());

  FiniteFieldValue one = FiniteFieldValue::mkOne(field.getFfSize());

  FiniteFieldValue constantTerm = FiniteFieldValue::mkZero(field.getFfSize());
  std::map<Node, FiniteFieldValue> scalarTerms;

  std::vector<TNode> children;
  expr::algorithm::flatten(t, children);

  for (const auto& child : children)
  {
    if (child.isConst())
    {
      constantTerm = constantTerm + child.getConst<FiniteFieldValue>();
    }
    else
    {
      std::pair<Node, FiniteFieldValue> pair = parseScalar(child);
      auto entry = scalarTerms.find(pair.first);
      if (entry == scalarTerms.end())
      {
        entry = scalarTerms.insert(entry, pair);
      }
      else
      {
        entry->second = entry->second + pair.second;
      }
    }
  }
  NodeManager* const nm = nodeManager();
  std::vector<Node> summands;
  if (scalarTerms.empty() || !constantTerm.getValue().isZero())
  {
    summands.push_back(nm->mkConst(constantTerm));
  }
  for (const auto& summand : scalarTerms)
  {
    if (summand.second.getValue().isZero())
    {
      // drop this term
      //
      // While (* x 0) will never be found as an original summand,
      // x might get mapped to zero through cancellation.
      //
      // consider: (+ (+ x y) (+ (* -1 x) z)).
    }
    else if (summand.second.getValue().isOne())
    {
      summands.push_back(summand.first);
    }
    else
    {
      Node c = nm->mkConst(summand.second);
      summands.push_back(expr::algorithm::flatten(nm,
          nm->mkNode(Kind::FINITE_FIELD_MULT, c, summand.first)));
    }
  }
  if (summands.size() == 0)
  {
    // again, this is possible through cancellation.
    return nm->mkConst(FiniteFieldValue::mkZero(field.getFfSize()));
  }
  return mkNary(Kind::FINITE_FIELD_ADD, std::move(summands));
}

Node TheoryFiniteFieldsRewriter::preRewriteFfMult(TNode t)
{
  Assert(t.getKind() == Kind::FINITE_FIELD_MULT);
  return expr::algorithm::flatten(d_nm, t);
}

Node TheoryFiniteFieldsRewriter::postRewriteFfMult(TNode t)
{
  const TypeNode field = t.getType();
  Assert(field.isFiniteField());

  FiniteFieldValue one = FiniteFieldValue::mkOne(field.getFfSize());

  FiniteFieldValue constantTerm = FiniteFieldValue::mkOne(field.getFfSize());
  std::vector<Node> factors;

  std::vector<TNode> children;
  expr::algorithm::flatten(t, children);

  for (const auto& child : children)
  {
    if (child.isConst())
    {
      constantTerm = constantTerm * child.getConst<FiniteFieldValue>();
    }
    else
    {
      factors.push_back(child);
    }
  }
  NodeManager* const nm = nodeManager();
  if (constantTerm.getValue().isZero())
  {
    factors.clear();
  }
  if (!constantTerm.getValue().isOne() || factors.empty())
  {
    factors.insert(factors.begin(), nm->mkConst(constantTerm));
  }
  return mkNary(Kind::FINITE_FIELD_MULT, std::move(factors));
}

Node TheoryFiniteFieldsRewriter::postRewriteFfEq(TNode t)
{
  Assert(t.getKind() == Kind::EQUAL);
  if (t[0].isConst() && t[1].isConst())
  {
    FiniteFieldValue l = t[0].getConst<FiniteFieldValue>();
    FiniteFieldValue r = t[1].getConst<FiniteFieldValue>();
    return nodeManager()->mkConst<bool>(l == r);
  }
  else if (t[0] == t[1])
  {
    return nodeManager()->mkConst<bool>(true);
  }
  else if (t[0] > t[1])
  {
    return nodeManager()->mkNode(Kind::EQUAL, t[1], t[0]);
  }
  else
  {
    return t;
  }
}

RewriteResponse TheoryFiniteFieldsRewriter::postRewrite(TNode t)
{
  Trace("ff::rw::post") << "ff::postRewrite: " << t << std::endl;
  switch (t.getKind())
  {
    case Kind::FINITE_FIELD_NEG: return RewriteResponse(REWRITE_DONE, t);
    case Kind::FINITE_FIELD_ADD:
    {
      Node nt = postRewriteFfAdd(t);
      return RewriteResponse(nt == t ? REWRITE_DONE : REWRITE_AGAIN, nt);
    }
    case Kind::FINITE_FIELD_MULT:
      return RewriteResponse(REWRITE_DONE, postRewriteFfMult(t));
    case Kind::EQUAL: return RewriteResponse(REWRITE_DONE, postRewriteFfEq(t));
    default: return RewriteResponse(REWRITE_DONE, t);
  }
}

RewriteResponse TheoryFiniteFieldsRewriter::preRewrite(TNode t)
{
  Trace("ff::rw::pre") << "ff::preRewrite: " << t << std::endl;
  switch (t.getKind())
  {
    case Kind::FINITE_FIELD_NEG:
      return RewriteResponse(REWRITE_DONE, preRewriteFfNeg(t));
    case Kind::FINITE_FIELD_ADD:
      return RewriteResponse(REWRITE_DONE, preRewriteFfAdd(t));
    case Kind::FINITE_FIELD_MULT:
      return RewriteResponse(REWRITE_DONE, preRewriteFfMult(t));
    case Kind::EQUAL: return RewriteResponse(REWRITE_DONE, t);
    default: return RewriteResponse(REWRITE_DONE, t);
  }
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
