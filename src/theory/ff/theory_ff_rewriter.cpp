/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace {

Node mkNary(Kind k, std::vector<Node>&& children)
{
  Assert(children.size() > 0);
  if (children.size() == 1)
  {
    return children[0];
  }
  else
  {
    return NodeManager::currentNM()->mkNode(k, std::move(children));
  }
}

/** Parse as a product with a constant scalar
 *
 *  If there is no constant scalar, returns a 1.
 */
std::pair<Node, FiniteFieldValue> parseScalar(TNode t)
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

/** preRewrite negation */
Node preRewriteFfNeg(TNode t)
{
  Assert(t.getKind() == Kind::FINITE_FIELD_NEG);
  NodeManager* const nm = NodeManager::currentNM();
  const Node negOne = nm->mkConst(FiniteFieldValue(Integer(-1), t.getType().getFfSize()));
  return nm->mkNode(kind::FINITE_FIELD_MULT, negOne, t[0]);
}

/** preRewrite addition */
Node preRewriteFfAdd(TNode t)
{
  Assert(t.getKind() == Kind::FINITE_FIELD_ADD);
  return expr::algorithm::flatten(t);
}

/** postRewrite addition */
Node postRewriteFfAdd(TNode t)
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
  NodeManager* const nm = NodeManager::currentNM();
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
      summands.push_back(expr::algorithm::flatten(
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

/** preRewrite multiplication */
Node preRewriteFfMult(TNode t)
{
  Assert(t.getKind() == Kind::FINITE_FIELD_MULT);
  return expr::algorithm::flatten(t);
}

/** postRewrite multiplication */
Node postRewriteFfMult(TNode t)
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
  NodeManager* const nm = NodeManager::currentNM();
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

/** postRewrite equality */
Node postRewriteFfEq(TNode t)
{
  Assert(t.getKind() == Kind::EQUAL);
  if (t[0].isConst() && t[1].isConst())
  {
    FiniteFieldValue l = t[0].getConst<FiniteFieldValue>();
    FiniteFieldValue r = t[1].getConst<FiniteFieldValue>();
    return NodeManager::currentNM()->mkConst<bool>(l == r);
  }
  else if (t[0] == t[1])
  {
    return NodeManager::currentNM()->mkConst<bool>(true);
  }
  else if (t[0] > t[1])
  {
    return NodeManager::currentNM()->mkNode(kind::EQUAL, t[1], t[0]);
  }
  else
  {
    return t;
  }
}

}  // namespace

RewriteResponse TheoryFiniteFieldsRewriter::postRewrite(TNode t)
{
  Trace("ff::rw::post") << "ff::postRewrite: " << t << std::endl;
  switch (t.getKind())
  {
    case kind::FINITE_FIELD_NEG: return RewriteResponse(REWRITE_DONE, t);
    case kind::FINITE_FIELD_ADD:
      return RewriteResponse(REWRITE_DONE, postRewriteFfAdd(t));
    case kind::FINITE_FIELD_MULT:
      return RewriteResponse(REWRITE_DONE, postRewriteFfMult(t));
    case kind::EQUAL: return RewriteResponse(REWRITE_DONE, postRewriteFfEq(t));
    default: return RewriteResponse(REWRITE_DONE, t);
  }
}

RewriteResponse TheoryFiniteFieldsRewriter::preRewrite(TNode t)
{
  Trace("ff::rw::pre") << "ff::preRewrite: " << t << std::endl;
  switch (t.getKind())
  {
    case kind::FINITE_FIELD_NEG:
      return RewriteResponse(REWRITE_DONE, preRewriteFfNeg(t));
    case kind::FINITE_FIELD_ADD:
      return RewriteResponse(REWRITE_DONE, preRewriteFfAdd(t));
    case kind::FINITE_FIELD_MULT:
      return RewriteResponse(REWRITE_DONE, preRewriteFfMult(t));
    case kind::EQUAL: return RewriteResponse(REWRITE_DONE, t);
    default: return RewriteResponse(REWRITE_DONE, t);
  }
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
