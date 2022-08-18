/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
#include "util/finite_field.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

// static
RewriteResponse TheoryFiniteFieldsRewriter::postRewrite(TNode t)
{
  Trace("ff::rw::post") << "ff::postRewrite: " << t << std::endl;
  if (t.isConst())
  {
    return RewriteResponse(REWRITE_DONE, t);
  }
  else if (t.isVar())
  {
    return RewriteResponse(REWRITE_DONE, t);
  }
  else
  {
    switch (Kind k = t.getKind())
    {
      case kind::FINITE_FIELD_NEG: return RewriteResponse(REWRITE_DONE, t);
      case kind::FINITE_FIELD_ADD:
        return RewriteResponse(REWRITE_DONE, postRewriteFfAdd(t));
      case kind::FINITE_FIELD_MULT:
        return RewriteResponse(REWRITE_DONE, postRewriteFfMult(t));
      case kind::EQUAL:
        return RewriteResponse(REWRITE_DONE, postRewriteFfEq(t));
      case kind::NOT:
        return RewriteResponse(REWRITE_DONE, postRewriteFfNotEq(t));
      default: Unhandled() << k;
    }
  }
}

// static
RewriteResponse TheoryFiniteFieldsRewriter::preRewrite(TNode t)
{
  Trace("ff::rw::pre") << "ff::preRewrite: " << t << std::endl;
  if (t.isConst())
  {
    return RewriteResponse(REWRITE_DONE, t);
  }
  else if (t.isVar())
  {
    return RewriteResponse(REWRITE_DONE, t);
  }
  else
  {
    switch (Kind k = t.getKind())
    {
      case kind::FINITE_FIELD_NEG:
        return RewriteResponse(REWRITE_DONE, preRewriteFfNeg(t));
      case kind::FINITE_FIELD_ADD:
        return RewriteResponse(REWRITE_DONE, preRewriteFfAdd(t));
      case kind::FINITE_FIELD_MULT:
        return RewriteResponse(REWRITE_DONE, preRewriteFfMult(t));
      case kind::EQUAL: return RewriteResponse(REWRITE_DONE, t);
      case kind::NOT: return RewriteResponse(REWRITE_DONE, t);
      default: Unhandled() << k;
    }
  }
}

/** preRewrite negation */
Node preRewriteFfNeg(TNode t)
{
  Assert(t.getKind() == Kind::FINITE_FIELD_NEG);
  NodeManager* const nm = NodeManager::currentNM();
  const Node negOne = nm->mkConstFiniteFieldElem(Integer(-1), t.getType());
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

  FiniteField one = FiniteField::mkOne(field.getFiniteFieldSize());

  FiniteField constantTerm = FiniteField::mkZero(field.getFiniteFieldSize());
  std::map<Node, FiniteField> scalarTerms;

  std::vector<TNode> children;
  expr::algorithm::flatten(t, children);

  for (const auto& child : children)
  {
    if (child.isConst())
    {
      constantTerm = constantTerm + child.getConst<FiniteField>();
    }
    else
    {
      std::optional<std::pair<Node, FiniteField>> parsed = parseScalar(child);
      std::pair<Node, FiniteField> pair =
          parsed.value_or(std::make_pair(child, one));
      const auto entry = scalarTerms.find(pair.first);
      if (entry == scalarTerms.end())
      {
        scalarTerms.insert(pair);
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
    return nm->mkConst(FiniteField::mkZero(field.getFiniteFieldSize()));
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

  FiniteField one = FiniteField::mkOne(field.getFiniteFieldSize());

  FiniteField constantTerm = FiniteField::mkOne(field.getFiniteFieldSize());
  std::vector<Node> summands;

  std::vector<TNode> children;
  expr::algorithm::flatten(t, children);

  for (const auto& child : children)
  {
    if (child.isConst())
    {
      constantTerm = constantTerm * child.getConst<FiniteField>();
    }
    else
    {
      summands.push_back(child);
    }
  }
  NodeManager* const nm = NodeManager::currentNM();
  if (constantTerm.getValue().isZero())
  {
    summands.clear();
  }
  if (!constantTerm.getValue().isOne() || summands.empty())
  {
    summands.insert(summands.begin(), nm->mkConst(constantTerm));
  }
  return mkNary(Kind::FINITE_FIELD_MULT, std::move(summands));
}

/** postRewrite equality */
Node postRewriteFfEq(TNode t)
{
  Assert(t.getKind() == Kind::EQUAL);
  if (t[0].isConst() && t[1].isConst())
  {
    FiniteField l = t[0].getConst<FiniteField>();
    FiniteField r = t[1].getConst<FiniteField>();
    return NodeManager::currentNM()->mkConst<bool>(l == r);
  }
  else if (t[0] == t[1])
  {
    return NodeManager::currentNM()->mkConst<bool>(true);
  }
  else
  {
    return t;
  }
}

/** postRewrite disequality */
Node postRewriteFfNotEq(TNode t)
{
  Assert(t.getKind() == Kind::NOT);
  Assert(t[0].getKind() == Kind::EQUAL);
  if (t[0][0].isConst() && t[0][1].isConst())
  {
    FiniteField l = t[0][0].getConst<FiniteField>();
    FiniteField r = t[0][1].getConst<FiniteField>();
    return NodeManager::currentNM()->mkConst<bool>(l != r);
  }
  else if (t[0] == t[1])
  {
    return NodeManager::currentNM()->mkConst<bool>(false);
  }
  else
  {
    return t;
  }
}

/** Parse as a product with a constant scalar */
std::optional<std::pair<Node, FiniteField>> parseScalar(TNode t)
{
  if (t.getKind() == Kind::FINITE_FIELD_MULT && t[0].isConst())
  {
    std::vector<Node> restChildren(std::next(t.begin()), t.end());
    const Node rest = mkNary(Kind::FINITE_FIELD_MULT, std::move(restChildren));
    return {{rest, t[0].getConst<FiniteField>()}};
  }
  else
  {
    return {};
  }
}

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

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
