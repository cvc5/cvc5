/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bags theory rewriter.
 */

#include "theory/bags/bags_rewriter.h"

#include "expr/emptybag.h"
#include "theory/bags/bags_utils.h"
#include "theory/datatypes/project_op.h"
#include "theory/rewriter.h"
#include "util/rational.h"
#include "util/statistics_registry.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

BagsRewriteResponse::BagsRewriteResponse()
    : d_node(Node::null()), d_rewrite(Rewrite::NONE)
{
}

BagsRewriteResponse::BagsRewriteResponse(Node n, Rewrite rewrite)
    : d_node(n), d_rewrite(rewrite)
{
}

BagsRewriter::BagsRewriter(NodeManager* nm,
                           Rewriter* r,
                           HistogramStat<Rewrite>* statistics)
    : TheoryRewriter(nm), d_rewriter(r), d_statistics(statistics)
{
  d_zero = d_nm->mkConstInt(Rational(0));
  d_one = d_nm->mkConstInt(Rational(1));
}

RewriteResponse BagsRewriter::postRewrite(TNode n)
{
  BagsRewriteResponse response;
  if (n.isConst())
  {
    // no need to rewrite n if it is already in a normal form
    response = BagsRewriteResponse(n, Rewrite::NONE);
  }
  else if (n.getKind() == Kind::EQUAL)
  {
    response = postRewriteEqual(n);
  }
  else if (n.getKind() == Kind::BAG_CHOOSE)
  {
    response = rewriteChoose(n);
  }
  else if (BagsUtils::areChildrenConstants(n))
  {
    Node value = BagsUtils::evaluate(d_rewriter, n);
    response = BagsRewriteResponse(value, Rewrite::CONSTANT_EVALUATION);
  }
  else
  {
    Kind k = n.getKind();
    switch (k)
    {
      case Kind::BAG_MAKE: response = rewriteMakeBag(n); break;
      case Kind::BAG_COUNT: response = rewriteBagCount(n); break;
      case Kind::BAG_SETOF: response = rewriteSetof(n); break;
      case Kind::BAG_UNION_MAX: response = rewriteUnionMax(n); break;
      case Kind::BAG_UNION_DISJOINT: response = rewriteUnionDisjoint(n); break;
      case Kind::BAG_INTER_MIN: response = rewriteIntersectionMin(n); break;
      case Kind::BAG_DIFFERENCE_SUBTRACT:
        response = rewriteDifferenceSubtract(n);
        break;
      case Kind::BAG_DIFFERENCE_REMOVE:
        response = rewriteDifferenceRemove(n);
        break;
      case Kind::BAG_CARD: response = rewriteCard(n); break;
      case Kind::BAG_MAP: response = postRewriteMap(n); break;
      case Kind::BAG_FILTER: response = postRewriteFilter(n); break;
      case Kind::BAG_ALL: response = postRewriteAll(n); break;
      case Kind::BAG_SOME: response = postRewriteSome(n); break;
      case Kind::BAG_FOLD: response = postRewriteFold(n); break;
      case Kind::BAG_PARTITION: response = postRewritePartition(n); break;
      case Kind::TABLE_PRODUCT: response = postRewriteProduct(n); break;
      case Kind::TABLE_AGGREGATE: response = postRewriteAggregate(n); break;
      default: response = BagsRewriteResponse(n, Rewrite::NONE); break;
    }
  }

  Trace("bags-rewrite") << "postRewrite " << n << " to " << response.d_node
                        << " by " << response.d_rewrite << "." << std::endl;

  if (d_statistics != nullptr)
  {
    (*d_statistics) << response.d_rewrite;
  }
  if (response.d_node != n)
  {
    return RewriteResponse(RewriteStatus::REWRITE_AGAIN_FULL, response.d_node);
  }
  return RewriteResponse(RewriteStatus::REWRITE_DONE, n);
}

RewriteResponse BagsRewriter::preRewrite(TNode n)
{
  BagsRewriteResponse response;
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::EQUAL: response = preRewriteEqual(n); break;
    case Kind::BAG_SUBBAG: response = rewriteSubBag(n); break;
    case Kind::BAG_MEMBER: response = rewriteMember(n); break;
    default: response = BagsRewriteResponse(n, Rewrite::NONE);
  }

  Trace("bags-rewrite") << "preRewrite " << n << " to " << response.d_node
                        << " by " << response.d_rewrite << "." << std::endl;

  if (d_statistics != nullptr)
  {
    (*d_statistics) << response.d_rewrite;
  }
  if (response.d_node != n)
  {
    return RewriteResponse(RewriteStatus::REWRITE_AGAIN_FULL, response.d_node);
  }
  return RewriteResponse(RewriteStatus::REWRITE_DONE, n);
}

BagsRewriteResponse BagsRewriter::preRewriteEqual(const TNode& n) const
{
  Assert(n.getKind() == Kind::EQUAL);
  if (n[0] == n[1])
  {
    // (= A A) = true where A is a bag
    return BagsRewriteResponse(d_nm->mkConst(true), Rewrite::IDENTICAL_NODES);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteSubBag(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_SUBBAG);

  // (bag.subbag A B) = ((bag.difference_subtract A B) == bag.empty)
  Node emptybag = d_nm->mkConst(EmptyBag(n[0].getType()));
  Node subtract = d_nm->mkNode(Kind::BAG_DIFFERENCE_SUBTRACT, n[0], n[1]);
  Node equal = subtract.eqNode(emptybag);
  return BagsRewriteResponse(equal, Rewrite::SUB_BAG);
}

BagsRewriteResponse BagsRewriter::rewriteMember(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_MEMBER);

  // - (bag.member x A) = (>= (bag.count x A) 1)
  Node count = d_nm->mkNode(Kind::BAG_COUNT, n[0], n[1]);
  Node geq = d_nm->mkNode(Kind::GEQ, count, d_one);
  return BagsRewriteResponse(geq, Rewrite::MEMBER);
}

BagsRewriteResponse BagsRewriter::rewriteMakeBag(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_MAKE);
  // return bag.empty for negative or zero multiplicity
  if (n[1].isConst() && n[1].getConst<Rational>().sgn() != 1)
  {
    // (bag x c) = bag.empty where c <= 0
    Node emptybag = d_nm->mkConst(EmptyBag(n.getType()));
    return BagsRewriteResponse(emptybag, Rewrite::BAG_MAKE_COUNT_NEGATIVE);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteBagCount(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_COUNT);
  if (n[1].isConst() && n[1].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.count x bag.empty) = 0
    return BagsRewriteResponse(d_zero, Rewrite::COUNT_EMPTY);
  }
  if (n[1].getKind() == Kind::BAG_MAKE && n[0] == n[1][0] && n[1][1].isConst()
      && n[1][1].getConst<Rational>() > Rational(0))
  {
    // (bag.count x (bag x c)) = c, c > 0 is a constant
    Node c = n[1][1];
    return BagsRewriteResponse(c, Rewrite::COUNT_BAG_MAKE);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteSetof(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_SETOF);
  if (n[0].getKind() == Kind::BAG_MAKE && n[0][1].isConst()
      && n[0][1].getConst<Rational>().sgn() == 1)
  {
    // (bag.setof (bag x n)) = (bag x 1)
    //  where n is a positive constant
    Node bag = d_nm->mkNode(Kind::BAG_MAKE, n[0][0], d_one);
    return BagsRewriteResponse(bag, Rewrite::SETOF_BAG_MAKE);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteUnionMax(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_UNION_MAX);
  if (n[1].getKind() == Kind::BAG_EMPTY || n[0] == n[1])
  {
    // (bag.union_max A A) = A
    // (bag.union_max A bag.empty) = A
    return BagsRewriteResponse(n[0], Rewrite::UNION_MAX_SAME_OR_EMPTY);
  }
  if (n[0].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.union_max bag.empty A) = A
    return BagsRewriteResponse(n[1], Rewrite::UNION_MAX_EMPTY);
  }

  if ((n[1].getKind() == Kind::BAG_UNION_MAX
       || n[1].getKind() == Kind::BAG_UNION_DISJOINT)
      && (n[0] == n[1][0] || n[0] == n[1][1]))
  {
    // (bag.union_max A (bag.union_max A B)) = (bag.union_max A B)
    // (bag.union_max A (bag.union_max B A)) = (bag.union_max B A)
    // (bag.union_max A (bag.union_disjoint A B)) = (bag.union_disjoint A B)
    // (bag.union_max A (bag.union_disjoint B A)) = (bag.union_disjoint B A)
    return BagsRewriteResponse(n[1], Rewrite::UNION_MAX_UNION_LEFT);
  }

  if ((n[0].getKind() == Kind::BAG_UNION_MAX
       || n[0].getKind() == Kind::BAG_UNION_DISJOINT)
      && (n[0][0] == n[1] || n[0][1] == n[1]))
  {
    // (bag.union_max (bag.union_max A B) A)) = (bag.union_max A B)
    // (bag.union_max (bag.union_max B A) A)) = (bag.union_max B A)
    // (bag.union_max (bag.union_disjoint A B) A)) = (bag.union_disjoint A B)
    // (bag.union_max (bag.union_disjoint B A) A)) = (bag.union_disjoint B A)
    return BagsRewriteResponse(n[0], Rewrite::UNION_MAX_UNION_RIGHT);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteUnionDisjoint(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_UNION_DISJOINT);
  if (n[1].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.union_disjoint A bag.empty) = A
    return BagsRewriteResponse(n[0], Rewrite::UNION_DISJOINT_EMPTY_RIGHT);
  }
  if (n[0].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.union_disjoint bag.empty A) = A
    return BagsRewriteResponse(n[1], Rewrite::UNION_DISJOINT_EMPTY_LEFT);
  }
  if ((n[0].getKind() == Kind::BAG_UNION_MAX
       && n[1].getKind() == Kind::BAG_INTER_MIN)
      || (n[1].getKind() == Kind::BAG_UNION_MAX
          && n[0].getKind() == Kind::BAG_INTER_MIN))

  {
    // (bag.union_disjoint (bag.union_max A B) (bag.inter_min A B)) =
    //         (bag.union_disjoint A B) // sum(a,b) = max(a,b) + min(a,b)
    // check if the operands of bag.union_max and bag.inter_min are the
    // same
    std::set<Node> left(n[0].begin(), n[0].end());
    std::set<Node> right(n[1].begin(), n[1].end());
    if (left == right)
    {
      Node rewritten = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, n[0][0], n[0][1]);
      return BagsRewriteResponse(rewritten, Rewrite::UNION_DISJOINT_MAX_MIN);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteIntersectionMin(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_INTER_MIN);
  if (n[0].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.inter_min bag.empty A) = bag.empty
    return BagsRewriteResponse(n[0], Rewrite::INTERSECTION_EMPTY_LEFT);
  }
  if (n[1].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.inter_min A bag.empty) = bag.empty
    return BagsRewriteResponse(n[1], Rewrite::INTERSECTION_EMPTY_RIGHT);
  }
  if (n[0] == n[1])
  {
    // (bag.inter_min A A) = A
    return BagsRewriteResponse(n[0], Rewrite::INTERSECTION_SAME);
  }
  if (n[1].getKind() == Kind::BAG_UNION_DISJOINT
      || n[1].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (bag.inter_min A (bag.union_disjoint A B)) = A
      // (bag.inter_min A (bag.union_disjoint B A)) = A
      // (bag.inter_min A (bag.union_max A B)) = A
      // (bag.inter_min A (bag.union_max B A)) = A
      return BagsRewriteResponse(n[0], Rewrite::INTERSECTION_SHARED_LEFT);
    }
  }

  if (n[0].getKind() == Kind::BAG_UNION_DISJOINT
      || n[0].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (bag.inter_min (bag.union_disjoint A B) A) = A
      // (bag.inter_min (bag.union_disjoint B A) A) = A
      // (bag.inter_min (bag.union_max A B) A) = A
      // (bag.inter_min (bag.union_max B A) A) = A
      return BagsRewriteResponse(n[1], Rewrite::INTERSECTION_SHARED_RIGHT);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteDifferenceSubtract(
    const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_DIFFERENCE_SUBTRACT);
  if (n[0].getKind() == Kind::BAG_EMPTY || n[1].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.difference_subtract A bag.empty) = A
    // (bag.difference_subtract bag.empty A) = bag.empty
    return BagsRewriteResponse(n[0], Rewrite::SUBTRACT_RETURN_LEFT);
  }
  if (n[0] == n[1])
  {
    // (bag.difference_subtract A A) = bag.empty
    Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
    return BagsRewriteResponse(emptyBag, Rewrite::SUBTRACT_SAME);
  }

  if (n[0].getKind() == Kind::BAG_UNION_DISJOINT)
  {
    if (n[1] == n[0][0])
    {
      // (bag.difference_subtract (bag.union_disjoint A B) A) = B
      return BagsRewriteResponse(n[0][1],
                                 Rewrite::SUBTRACT_DISJOINT_SHARED_LEFT);
    }
    if (n[1] == n[0][1])
    {
      // (bag.difference_subtract (bag.union_disjoint B A) A) = B
      return BagsRewriteResponse(n[0][0],
                                 Rewrite::SUBTRACT_DISJOINT_SHARED_RIGHT);
    }
  }

  if (n[1].getKind() == Kind::BAG_UNION_DISJOINT
      || n[1].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (bag.difference_subtract A (bag.union_disjoint A B)) = bag.empty
      // (bag.difference_subtract A (bag.union_disjoint B A)) = bag.empty
      // (bag.difference_subtract A (bag.union_max A B)) = bag.empty
      // (bag.difference_subtract A (bag.union_max B A)) = bag.empty
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::SUBTRACT_FROM_UNION);
    }
  }

  if (n[0].getKind() == Kind::BAG_INTER_MIN)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (bag.difference_subtract (bag.inter_min A B) A) = bag.empty
      // (bag.difference_subtract (bag.inter_min B A) A) = bag.empty
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::SUBTRACT_MIN);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteDifferenceRemove(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_DIFFERENCE_REMOVE);

  if (n[0].getKind() == Kind::BAG_EMPTY || n[1].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.difference_remove A bag.empty) = A
    // (bag.difference_remove bag.empty B) = bag.empty
    return BagsRewriteResponse(n[0], Rewrite::REMOVE_RETURN_LEFT);
  }

  if (n[0] == n[1])
  {
    // (bag.difference_remove A A) = bag.empty
    Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
    return BagsRewriteResponse(emptyBag, Rewrite::REMOVE_SAME);
  }

  if (n[1].getKind() == Kind::BAG_UNION_DISJOINT
      || n[1].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (bag.difference_remove A (bag.union_disjoint A B)) = bag.empty
      // (bag.difference_remove A (bag.union_disjoint B A)) = bag.empty
      // (bag.difference_remove A (bag.union_max A B)) = bag.empty
      // (bag.difference_remove A (bag.union_max B A)) = bag.empty
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::REMOVE_FROM_UNION);
    }
  }

  if (n[0].getKind() == Kind::BAG_INTER_MIN)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (bag.difference_remove (bag.inter_min A B) A) = bag.empty
      // (bag.difference_remove (bag.inter_min B A) A) = bag.empty
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::REMOVE_MIN);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteChoose(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_CHOOSE);
  if (n[0].getKind() == Kind::BAG_MAKE && n[0][1].isConst()
      && n[0][1].getConst<Rational>() > 0)
  {
    // (bag.choose (bag x c)) = x where c is a constant > 0
    return BagsRewriteResponse(n[0][0], Rewrite::CHOOSE_BAG_MAKE);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteCard(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_CARD);
  if (n[0].getKind() == Kind::BAG_MAKE && n[0][1].isConst())
  {
    // (bag.card (bag x c)) = c where c is a constant > 0
    return BagsRewriteResponse(n[0][1], Rewrite::CARD_BAG_MAKE);
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::postRewriteEqual(const TNode& n) const
{
  Assert(n.getKind() == Kind::EQUAL);
  if (n[0] == n[1])
  {
    Node ret = d_nm->mkConst(true);
    return BagsRewriteResponse(ret, Rewrite::EQ_REFL);
  }

  if (n[0].isConst() && n[1].isConst())
  {
    Node ret = d_nm->mkConst(false);
    return BagsRewriteResponse(ret, Rewrite::EQ_CONST_FALSE);
  }

  // standard ordering
  if (n[0] > n[1])
  {
    Node ret = d_nm->mkNode(Kind::EQUAL, n[1], n[0]);
    return BagsRewriteResponse(ret, Rewrite::EQ_SYM);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::postRewriteMap(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_MAP);
  if (n[1].isConst())
  {
    // (bag.map f (as bag.empty (Bag T1)) = (as bag.empty (Bag T2))
    // (bag.map f (bag "a" 3)) = (bag (f "a") 3)
    std::map<Node, Rational> elements = BagsUtils::getBagElements(n[1]);
    std::map<Node, Rational> mappedElements;
    std::map<Node, Rational>::iterator it = elements.begin();
    while (it != elements.end())
    {
      Node mappedElement = d_nm->mkNode(Kind::APPLY_UF, n[0], it->first);
      mappedElements[mappedElement] = it->second;
      ++it;
    }
    TypeNode t = d_nm->mkBagType(n[0].getType().getRangeType());
    Node ret = BagsUtils::constructConstantBagFromElements(t, mappedElements);
    return BagsRewriteResponse(ret, Rewrite::MAP_CONST);
  }
  Kind k = n[1].getKind();
  switch (k)
  {
    case Kind::BAG_MAKE:
    {
      // (bag.map f (bag x y)) = (bag (apply f x) y)
      Node mappedElement = d_nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      Node ret = d_nm->mkNode(Kind::BAG_MAKE, mappedElement, n[1][1]);
      return BagsRewriteResponse(ret, Rewrite::MAP_BAG_MAKE);
    }

    case Kind::BAG_UNION_DISJOINT:
    {
      // (bag.map f (bag.union_disjoint A B)) =
      //    (bag.union_disjoint (bag.map f A) (bag.map f B))
      Node a = d_nm->mkNode(Kind::BAG_MAP, n[0], n[1][0]);
      Node b = d_nm->mkNode(Kind::BAG_MAP, n[0], n[1][1]);
      Node ret = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, a, b);
      return BagsRewriteResponse(ret, Rewrite::MAP_UNION_DISJOINT);
    }

    default: return BagsRewriteResponse(n, Rewrite::NONE);
  }
}

BagsRewriteResponse BagsRewriter::postRewriteFilter(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_FILTER);
  Node P = n[0];
  Node A = n[1];
  TypeNode t = A.getType();
  if (A.isConst())
  {
    // (bag.filter p (as bag.empty (Bag T)) = (as bag.empty (Bag T))
    // (bag.filter p (bag "a" 3) ((bag "b" 2))) =
    //   (bag.union_disjoint
    //     (ite (p "a") (bag "a" 3) (as bag.empty (Bag T)))
    //     (ite (p "b") (bag "b" 2) (as bag.empty (Bag T)))

    Node ret = BagsUtils::evaluateBagFilter(n);
    return BagsRewriteResponse(ret, Rewrite::FILTER_CONST);
  }
  Kind k = A.getKind();
  switch (k)
  {
    case Kind::BAG_MAKE:
    {
      // (bag.filter p (bag x y)) = (ite (p x) (bag x y) (as bag.empty (Bag T)))
      Node empty = d_nm->mkConst(EmptyBag(t));
      Node pOfe = d_nm->mkNode(Kind::APPLY_UF, P, A[0]);
      Node ret = d_nm->mkNode(Kind::ITE, pOfe, A, empty);
      return BagsRewriteResponse(ret, Rewrite::FILTER_BAG_MAKE);
    }

    case Kind::BAG_UNION_DISJOINT:
    {
      // (bag.filter p (bag.union_disjoint A B)) =
      //    (bag.union_disjoint (bag.filter p A) (bag.filter p B))
      Node a = d_nm->mkNode(Kind::BAG_FILTER, n[0], n[1][0]);
      Node b = d_nm->mkNode(Kind::BAG_FILTER, n[0], n[1][1]);
      Node ret = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, a, b);
      return BagsRewriteResponse(ret, Rewrite::FILTER_UNION_DISJOINT);
    }

    default: return BagsRewriteResponse(n, Rewrite::NONE);
  }
}

BagsRewriteResponse BagsRewriter::postRewriteAll(TNode n)
{
  Assert(n.getKind() == Kind::BAG_ALL);
  NodeManager* nm = nodeManager();
  Kind k = n[1].getKind();
  switch (k)
  {
    case Kind::BAG_EMPTY:
    {
      // (bag.all p (as bag.empty (Bag T)) = true)
      return BagsRewriteResponse(nm->mkConst(true), Rewrite::ALL_EMPTY);
    }
    case Kind::BAG_MAKE:
    {
      // (bag.all p (bag x n)) = (or (p x) (<= n 0)
      Node px = nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      Node leq = nm->mkNode(Kind::LEQ, n[1][1], d_zero);
      Node ret = px.orNode(leq);
      return BagsRewriteResponse(ret, Rewrite::ALL_BAG_MAKE);
    }
    case Kind::BAG_UNION_DISJOINT:
    {
      // (bag.all p (bag.union_disjoint A B)) =
      //   (and (bag.all p A) (bag.all p B))
      Node a = nm->mkNode(Kind::BAG_ALL, n[0], n[1][0]);
      Node b = nm->mkNode(Kind::BAG_ALL, n[0], n[1][1]);
      Node ret = a.andNode(b);
      return BagsRewriteResponse(ret, Rewrite::ALL_UNION_DISJOINT);
    }
    default:
    {
      // (bag.all p A) is rewritten as (bag.filter p A) = A
      Node filter = nm->mkNode(Kind::BAG_FILTER, n[0], n[1]);
      Node all = filter.eqNode(n[1]);
      return BagsRewriteResponse(all, Rewrite::ALL_FILTER);
    }
  }
}

BagsRewriteResponse BagsRewriter::postRewriteSome(TNode n)
{
  Assert(n.getKind() == Kind::BAG_SOME);
  NodeManager* nm = nodeManager();
  Kind k = n[1].getKind();
  switch (k)
  {
    case Kind::BAG_EMPTY:
    {
      // (bag.some p (as bag.empty (Set T)) = false)
      return BagsRewriteResponse(nm->mkConst(false), Rewrite::SOME_EMPTY);
    }
    case Kind::BAG_MAKE:
    {
      // (bag.some p (bag x n)) = (and (> n 0) (p x))
      Node px = nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      Node leq = nm->mkNode(Kind::GT, n[1][1], d_zero);
      Node ret = px.andNode(leq);
      return BagsRewriteResponse(ret, Rewrite::SOME_BAG_MAKE);
    }
    case Kind::BAG_UNION_DISJOINT:
    {
      // (bag.some p (bag.union_disjoint A B)) =
      //   (or (bag.some p A) (bag.union_disjoint p B))
      Node a = nm->mkNode(Kind::BAG_SOME, n[0], n[1][0]);
      Node b = nm->mkNode(Kind::BAG_SOME, n[0], n[1][1]);
      Node ret = a.orNode(b);
      return BagsRewriteResponse(ret, Rewrite::SOME_UNION_DISJOINT);
    }
    default:
    {
      // (bag.some p A) is rewritten as (distinct (bag.filter p A) bag.empty))
      Node filter = nm->mkNode(Kind::BAG_FILTER, n[0], n[1]);
      Node empty = nm->mkConst(EmptyBag(n[1].getType()));
      Node some = filter.eqNode(empty).notNode();
      return BagsRewriteResponse(some, Rewrite::SOME_FILTER);
    }
  }
}

BagsRewriteResponse BagsRewriter::postRewriteFold(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_FOLD);
  Node f = n[0];
  Node t = n[1];
  Node bag = n[2];
  if (bag.isConst())
  {
    Node value = BagsUtils::evaluateBagFold(n);
    return BagsRewriteResponse(value, Rewrite::FOLD_CONST);
  }
  Kind k = bag.getKind();
  switch (k)
  {
    case Kind::BAG_MAKE:
    {
      if (bag[1].isConst() && bag[1].getConst<Rational>() > Rational(0))
      {
        // (bag.fold f t (bag x n)) = (f t ... (f t (f t x))) n times, n > 0
        Node value = BagsUtils::evaluateBagFold(n);
        return BagsRewriteResponse(value, Rewrite::FOLD_BAG);
      }
      break;
    }
    case Kind::BAG_UNION_DISJOINT:
    {
      // (bag.fold f t (bag.union_disjoint A B)) =
      //       (bag.fold f (bag.fold f t A) B) where A < B to break symmetry
      Node A = bag[0] < bag[1] ? bag[0] : bag[1];
      Node B = bag[0] < bag[1] ? bag[1] : bag[0];
      Node foldA = d_nm->mkNode(Kind::BAG_FOLD, f, t, A);
      Node fold = d_nm->mkNode(Kind::BAG_FOLD, f, foldA, B);
      return BagsRewriteResponse(fold, Rewrite::FOLD_UNION_DISJOINT);
    }
    default: return BagsRewriteResponse(n, Rewrite::NONE);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::postRewritePartition(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_PARTITION);
  if (n[1].isConst())
  {
    Node ret = BagsUtils::evaluateBagPartition(d_rewriter, n);
    if (ret != n)
    {
      return BagsRewriteResponse(ret, Rewrite::PARTITION_CONST);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

bool BagsRewriter::collectElements(TNode A,
                                   Node cond,
                                   std::vector<GuardedElement>& elements) const
{
  switch (A.getKind())
  {
    // (as bag.empty (Bag T)) has no elements
    case Kind::BAG_EMPTY: return true;
    case Kind::BAG_MAKE:
    {
      if (!A[1].isConst())
      {
        // (bag y n) with n a variable: the number of copies is unknown
        return false;
      }
      const Rational& c = A[1].getConst<Rational>();
      if (c.sgn() <= 0)
      {
        // (bag x c) is empty for c <= 0
        return true;
      }
      if (!c.isIntegral() || !c.getNumerator().fitsUnsignedInt())
      {
        // c does not fit in d_count
        return false;
      }
      // (bag y 2) under cond gives {d_cond: cond, d_element: y, d_count: 2}
      elements.push_back({cond, A[0], c.getNumerator().toUnsignedInt()});
      return true;
    }
    case Kind::BAG_UNION_DISJOINT:
      // (bag.union_disjoint A1 A2): the elements of A1, then those of A2
      return collectElements(A[0], cond, elements)
             && collectElements(A[1], cond, elements);
    case Kind::ITE:
      // (ite b A1 A2): the elements of A1 under (and cond b), then those of A2
      // under (and cond (not b)). For example, with cond = true,
      //   (ite b (bag y 2) (as bag.empty (Table Int Int)))
      // gives {d_cond: (and true b), d_element: y, d_count: 2}.
      return collectElements(
                 A[1], d_nm->mkNode(Kind::AND, cond, A[0]), elements)
             && collectElements(
                 A[2], d_nm->mkNode(Kind::AND, cond, A[0].notNode()), elements);
    // any other term, for example a variable, has unknown elements
    default: return false;
  }
}

BagsRewriteResponse BagsRewriter::postRewriteAggregate(const TNode& n) const
{
  Assert(n.getKind() == Kind::TABLE_AGGREGATE);
  if (n[1].isConst() && n[2].isConst())
  {
    Node ret = BagsUtils::evaluateTableAggregate(n);
    if (ret != n)
    {
      return BagsRewriteResponse(ret, Rewrite::AGGREGATE_CONST);
    }
  }

  // AGGREGATE_BAG_MAKE: if the table is a union of known elements, see
  // collectElements, write the aggregate out, with one element per group.
  //
  // Running example:
  //   (declare-const x (Tuple Int Int))
  //   (declare-const y (Tuple Int Int))
  //   (declare-const t (Tuple Int Int))
  //   (declare-const b Bool)
  //   (declare-fun f ((Tuple Int Int) (Tuple Int Int)) (Tuple Int Int))
  //   ; kx is the key of x: the key columns of x, here column 0, as a tuple.
  //   ; For example, if x is (tuple 1 5), then kx is (tuple 1).
  //   (define-fun kx () (Tuple Int) ((_ tuple.project 0) x))
  //   (define-fun ky () (Tuple Int) ((_ tuple.project 0) y))
  // The aggregate
  //   ((_ table.aggr 0) f t
  //     (bag.union_disjoint
  //       (bag x 1)
  //       (ite b (bag y 2) (as bag.empty (Table Int Int)))))
  // is rewritten to
  //   (bag.union_disjoint
  //     (bag (ite (and b (= ky kx)) (f y (f y (f x t))) (f x t)) 1)
  //     (ite (and b (not (= kx ky)))
  //          (bag (f y (f y t)) 1)
  //          (as bag.empty (Table Int Int))))
  // which means:
  //   - b and (= kx ky): one group, x and two copies of y, with value
  //     (f y (f y (f x t)))
  //   - b and (distinct kx ky): two groups, with values (f x t) and
  //     (f y (f y t))
  //   - (not b): y is not in the table; one group, x, with value (f x t)
  // Here and below, we drop the conjuncts true from the conditions. The
  // rewriter removes them later.
  //
  // In general, the table has elements x_0, ..., x_{k-1}, and the result has
  // one element for each x_i:
  //   (ite first_i (bag v_i 1) empty)
  // where empty is the empty bag of the result.
  // - first_i: x_i is in the table and no x_j, j < i, of its group is. So each
  //   group is written out once, at its first element. The group of x_i is
  //   the x_j with the key of x_i.
  // - v_i: f folded over x_i and the x_j, j > i, of its group, in their order
  //   in the table, as FOLD_UNION_DISJOINT does. An element with c copies is
  //   folded c times.

  // elements, as {d_cond, d_element, d_count}: {true, x, 1} and {b, y, 2}
  std::vector<GuardedElement> elements;
  if (!collectElements(n[2], d_nm->mkConst(true), elements))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node f = n[0];
  // empty: (as bag.empty (Table Int Int))
  Node empty = d_nm->mkConst(EmptyBag(n.getType()));
  // the key columns of (_ table.aggr 0) as a projection: (_ tuple.project 0)
  ProjectOp op = n.getOperator().getConst<ProjectOp>();
  Node projectOp = d_nm->mkConst(Kind::TUPLE_PROJECT_OP, op);
  // keys[i] is the key of x_i: kx and ky, that is
  //   ((_ tuple.project 0) x) and ((_ tuple.project 0) y)
  // Without key columns, as in (table.aggr f t A), keys[i] is null.
  std::vector<Node> keys;
  for (const GuardedElement& e : elements)
  {
    keys.push_back(
        op.getIndices().empty()
            ? Node::null()
            : d_nm->mkNode(Kind::TUPLE_PROJECT, projectOp, e.d_element));
  }
  // inGroup(j, i): x_j is in the table and in the group of x_i
  //   inGroup(1, 0) = (and b (= ky kx))
  //   inGroup(0, 1) = (= kx ky)
  // Without key columns, every element is in one group, and inGroup(j, i) is
  // the condition of x_j.
  auto inGroup = [&](size_t j, size_t i) {
    if (op.getIndices().empty())
    {
      return elements[j].d_cond;
    }
    return d_nm->mkNode(Kind::AND, elements[j].d_cond, keys[j].eqNode(keys[i]));
  };
  // fold(j, v): f folded over the copies of x_j, starting with v
  //   fold(0, t) = (f x t)
  //   fold(1, t) = (f y (f y t))
  auto fold = [&](size_t j, Node value) {
    for (uint32_t c = 0; c < elements[j].d_count; ++c)
    {
      value = d_nm->mkNode(Kind::APPLY_UF, f, elements[j].d_element, value);
    }
    return value;
  };
  Node ret = empty;
  for (size_t i = 0, size = elements.size(); i < size; ++i)
  {
    // first: the conjuncts of first_i, x_i is in the table and no x_j, j < i,
    // of its group is
    //   i = 0: {true}
    //   i = 1: {b, (not (= kx ky))}
    std::vector<Node> first{elements[i].d_cond};
    for (size_t j = 0; j < i; ++j)
    {
      first.push_back(inGroup(j, i).notNode());
    }
    // value: v_i. Fold the copies of x_i into t, then each x_j, j > i, if it
    // is in the group of x_i.
    //   i = 0: (f x t), then
    //          (ite (and b (= ky kx)) (f y (f y (f x t))) (f x t))
    //   i = 1: (f y (f y t))
    Node value = fold(i, n[1]);
    for (size_t j = i + 1; j < size; ++j)
    {
      Node in = inGroup(j, i);
      Node folded = fold(j, value);
      value = d_nm->mkNode(Kind::ITE, in, folded, value);
    }
    // element: (ite first_i (bag v_i 1) (as bag.empty (Table Int Int)))
    //   i = 0: (ite true (bag v_0 1) (as bag.empty (Table Int Int)))
    //   i = 1: (ite (and b (not (= kx ky)))
    //               (bag (f y (f y t)) 1)
    //               (as bag.empty (Table Int Int)))
    Node isFirst = d_nm->mkAnd(first);
    Node bag = d_nm->mkNode(Kind::BAG_MAKE, value, d_one);
    Node element = d_nm->mkNode(Kind::ITE, isFirst, bag, empty);
    // ret: the union of the elements so far, nested to the left:
    //   (bag.union_disjoint (bag.union_disjoint element_0 element_1) ...)
    ret =
        i == 0 ? element : d_nm->mkNode(Kind::BAG_UNION_DISJOINT, ret, element);
  }
  return BagsRewriteResponse(ret, Rewrite::AGGREGATE_BAG_MAKE);
}

BagsRewriteResponse BagsRewriter::postRewriteProduct(const TNode& n) const
{
  Assert(n.getKind() == Kind::TABLE_PRODUCT);
  TypeNode tableType = n.getType();
  Node empty = d_nm->mkConst(EmptyBag(tableType));
  if (n[0].getKind() == Kind::BAG_EMPTY || n[1].getKind() == Kind::BAG_EMPTY)
  {
    return BagsRewriteResponse(empty, Rewrite::PRODUCT_EMPTY);
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
