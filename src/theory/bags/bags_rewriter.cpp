/*********************                                                        */
/*! \file bags_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory rewriter.
 **/

#include "theory/bags/bags_rewriter.h"

#include "theory/bags/normal_form.h"

using namespace CVC4::kind;

namespace CVC4 {
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

BagsRewriteResponse::BagsRewriteResponse(const BagsRewriteResponse& r)
    : d_node(r.d_node), d_rewrite(r.d_rewrite)
{
}

BagsRewriter::BagsRewriter(HistogramStat<Rewrite>* statistics)
    : d_statistics(statistics)
{
  d_nm = NodeManager::currentNM();
}

RewriteResponse BagsRewriter::postRewrite(TNode n)
{
  BagsRewriteResponse response;
  if (n.isConst())
  {
    // no need to rewrite n if it is already in a normal form
    response = BagsRewriteResponse(n, Rewrite::NONE);
  }
  else if (NormalForm::AreChildrenConstants(n))
  {
    Node value = NormalForm::evaluate(n);
    response = BagsRewriteResponse(value, Rewrite::CONSTANT_EVALUATION);
  }
  else
  {
    Kind k = n.getKind();
    switch (k)
    {
      case MK_BAG: response = rewriteMakeBag(n); break;
      case BAG_COUNT: response = rewriteBagCount(n); break;
      case UNION_MAX: response = rewriteUnionMax(n); break;
      case UNION_DISJOINT: response = rewriteUnionDisjoint(n); break;
      case INTERSECTION_MIN: response = rewriteIntersectionMin(n); break;
      case DIFFERENCE_SUBTRACT: response = rewriteDifferenceSubtract(n); break;
      case DIFFERENCE_REMOVE: response = rewriteDifferenceRemove(n); break;
      case BAG_CHOOSE: response = rewriteChoose(n); break;
      case BAG_CARD: response = rewriteCard(n); break;
      case BAG_IS_SINGLETON: response = rewriteIsSingleton(n); break;
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
    case EQUAL: response = rewriteEqual(n); break;
    case BAG_IS_INCLUDED: response = rewriteIsIncluded(n); break;
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

BagsRewriteResponse BagsRewriter::rewriteEqual(const TNode& n) const
{
  Assert(n.getKind() == EQUAL);
  if (n[0] == n[1])
  {
    // (= A A) = true where A is a bag
    return BagsRewriteResponse(d_nm->mkConst(true), Rewrite::IDENTICAL_NODES);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteIsIncluded(const TNode& n) const
{
  Assert(n.getKind() == BAG_IS_INCLUDED);

  // (bag.is_included A B) = ((difference_subtract A B) == emptybag)
  Node emptybag = d_nm->mkConst(EmptyBag(n[0].getType()));
  Node subtract = d_nm->mkNode(DIFFERENCE_SUBTRACT, n[0], n[1]);
  Node equal = subtract.eqNode(emptybag);
  return BagsRewriteResponse(equal, Rewrite::SUB_BAG);
}

BagsRewriteResponse BagsRewriter::rewriteMakeBag(const TNode& n) const
{
  Assert(n.getKind() == MK_BAG);
  // return emptybag for negative or zero multiplicity
  if (n[1].isConst() && n[1].getConst<Rational>().sgn() != 1)
  {
    // (mkBag x c) = emptybag where c <= 0
    Node emptybag = d_nm->mkConst(EmptyBag(n.getType()));
    return BagsRewriteResponse(emptybag, Rewrite::MK_BAG_COUNT_NEGATIVE);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteBagCount(const TNode& n) const
{
  Assert(n.getKind() == BAG_COUNT);
  if (n[1].isConst() && n[1].getKind() == EMPTYBAG)
  {
    // (bag.count x emptybag) = 0
    return BagsRewriteResponse(d_nm->mkConst(Rational(0)),
                               Rewrite::COUNT_EMPTY);
  }
  if (n[1].getKind() == MK_BAG && n[0] == n[1][0])
  {
    // (bag.count x (mkBag x c) = c where c > 0 is a constant
    return BagsRewriteResponse(n[1][1], Rewrite::COUNT_MK_BAG);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteUnionMax(const TNode& n) const
{
  Assert(n.getKind() == UNION_MAX);
  if (n[1].getKind() == EMPTYBAG || n[0] == n[1])
  {
    // (union_max A A) = A
    // (union_max A emptybag) = A
    return BagsRewriteResponse(n[0], Rewrite::UNION_MAX_SAME_OR_EMPTY);
  }
  if (n[0].getKind() == EMPTYBAG)
  {
    // (union_max emptybag A) = A
    return BagsRewriteResponse(n[1], Rewrite::UNION_MAX_EMPTY);
  }

  if ((n[1].getKind() == UNION_MAX || n[1].getKind() == UNION_DISJOINT)
      && (n[0] == n[1][0] || n[0] == n[1][1]))
  {
    // (union_max A (union_max A B)) = (union_max A B)
    // (union_max A (union_max B A)) = (union_max B A)
    // (union_max A (union_disjoint A B)) = (union_disjoint A B)
    // (union_max A (union_disjoint B A)) = (union_disjoint B A)
    return BagsRewriteResponse(n[1], Rewrite::UNION_MAX_UNION_LEFT);
  }

  if ((n[0].getKind() == UNION_MAX || n[0].getKind() == UNION_DISJOINT)
      && (n[0][0] == n[1] || n[0][1] == n[1]))
  {
    // (union_max (union_max A B) A)) = (union_max A B)
    // (union_max (union_max B A) A)) = (union_max B A)
    // (union_max (union_disjoint A B) A)) = (union_disjoint A B)
    // (union_max (union_disjoint B A) A)) = (union_disjoint B A)
    return BagsRewriteResponse(n[0], Rewrite::UNION_MAX_UNION_RIGHT);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteUnionDisjoint(const TNode& n) const
{
  Assert(n.getKind() == UNION_DISJOINT);
  if (n[1].getKind() == EMPTYBAG)
  {
    // (union_disjoint A emptybag) = A
    return BagsRewriteResponse(n[0], Rewrite::UNION_DISJOINT_EMPTY_RIGHT);
  }
  if (n[0].getKind() == EMPTYBAG)
  {
    // (union_disjoint emptybag A) = A
    return BagsRewriteResponse(n[1], Rewrite::UNION_DISJOINT_EMPTY_LEFT);
  }
  if ((n[0].getKind() == UNION_MAX && n[1].getKind() == INTERSECTION_MIN)
      || (n[1].getKind() == UNION_MAX && n[0].getKind() == INTERSECTION_MIN))

  {
    // (union_disjoint (union_max A B) (intersection_min A B)) =
    //         (union_disjoint A B) // sum(a,b) = max(a,b) + min(a,b)
    // check if the operands of union_max and intersection_min are the same
    std::set<Node> left(n[0].begin(), n[0].end());
    std::set<Node> right(n[0].begin(), n[0].end());
    if (left == right)
    {
      Node rewritten = d_nm->mkNode(UNION_DISJOINT, n[0][0], n[0][1]);
      return BagsRewriteResponse(rewritten, Rewrite::UNION_DISJOINT_MAX_MIN);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteIntersectionMin(const TNode& n) const
{
  Assert(n.getKind() == INTERSECTION_MIN);
  if (n[0].getKind() == EMPTYBAG)
  {
    // (intersection_min emptybag A) = emptybag
    return BagsRewriteResponse(n[0], Rewrite::INTERSECTION_EMPTY_LEFT);
  }
  if (n[1].getKind() == EMPTYBAG)
  {
    // (intersection_min A emptybag) = emptybag
    return BagsRewriteResponse(n[1], Rewrite::INTERSECTION_EMPTY_RIGHT);
  }
  if (n[0] == n[1])
  {
    // (intersection_min A A) = A
    return BagsRewriteResponse(n[0], Rewrite::INTERSECTION_SAME);
  }
  if (n[1].getKind() == UNION_DISJOINT || n[1].getKind() == UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (intersection_min A (union_disjoint A B)) = A
      // (intersection_min A (union_disjoint B A)) = A
      // (intersection_min A (union_max A B)) = A
      // (intersection_min A (union_max B A)) = A
      return BagsRewriteResponse(n[0], Rewrite::INTERSECTION_SHARED_LEFT);
    }
  }

  if (n[0].getKind() == UNION_DISJOINT || n[0].getKind() == UNION_MAX)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (intersection_min (union_disjoint A B) A) = A
      // (intersection_min (union_disjoint B A) A) = A
      // (intersection_min (union_max A B) A) = A
      // (intersection_min (union_max B A) A) = A
      return BagsRewriteResponse(n[1], Rewrite::INTERSECTION_SHARED_RIGHT);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteDifferenceSubtract(
    const TNode& n) const
{
  Assert(n.getKind() == DIFFERENCE_SUBTRACT);
  if (n[0].getKind() == EMPTYBAG || n[1].getKind() == EMPTYBAG)
  {
    // (difference_subtract A emptybag) = A
    // (difference_subtract emptybag A) = emptybag
    return BagsRewriteResponse(n[0], Rewrite::SUBTRACT_RETURN_LEFT);
  }
  if (n[0] == n[1])
  {
    // (difference_subtract A A) = emptybag
    Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
    return BagsRewriteResponse(emptyBag, Rewrite::SUBTRACT_SAME);
  }

  if (n[0].getKind() == UNION_DISJOINT)
  {
    if (n[1] == n[0][0])
    {
      // (difference_subtract (union_disjoint A B) A) = B
      return BagsRewriteResponse(n[0][1],
                                 Rewrite::SUBTRACT_DISJOINT_SHARED_LEFT);
    }
    if (n[1] == n[0][1])
    {
      // (difference_subtract (union_disjoint B A) A) = B
      return BagsRewriteResponse(n[0][0],
                                 Rewrite::SUBTRACT_DISJOINT_SHARED_RIGHT);
    }
  }

  if (n[1].getKind() == UNION_DISJOINT || n[1].getKind() == UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (difference_subtract A (union_disjoint A B)) = emptybag
      // (difference_subtract A (union_disjoint B A)) = emptybag
      // (difference_subtract A (union_max A B)) = emptybag
      // (difference_subtract A (union_max B A)) = emptybag
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::SUBTRACT_FROM_UNION);
    }
  }

  if (n[0].getKind() == INTERSECTION_MIN)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (difference_subtract (intersection_min A B) A) = emptybag
      // (difference_subtract (intersection_min B A) A) = emptybag
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::SUBTRACT_MIN);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteDifferenceRemove(const TNode& n) const
{
  Assert(n.getKind() == DIFFERENCE_REMOVE);

  if (n[0].getKind() == EMPTYBAG || n[1].getKind() == EMPTYBAG)
  {
    // (difference_remove A emptybag) = A
    // (difference_remove emptybag B) = emptybag
    return BagsRewriteResponse(n[0], Rewrite::REMOVE_RETURN_LEFT);
  }

  if (n[0] == n[1])
  {
    // (difference_remove A A) = emptybag
    Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
    return BagsRewriteResponse(emptyBag, Rewrite::REMOVE_SAME);
  }

  if (n[1].getKind() == UNION_DISJOINT || n[1].getKind() == UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (difference_remove A (union_disjoint A B)) = emptybag
      // (difference_remove A (union_disjoint B A)) = emptybag
      // (difference_remove A (union_max A B)) = emptybag
      // (difference_remove A (union_max B A)) = emptybag
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::REMOVE_FROM_UNION);
    }
  }

  if (n[0].getKind() == INTERSECTION_MIN)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (difference_remove (intersection_min A B) A) = emptybag
      // (difference_remove (intersection_min B A) A) = emptybag
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::REMOVE_MIN);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteChoose(const TNode& n) const
{
  Assert(n.getKind() == BAG_CHOOSE);
  if (n[0].getKind() == MK_BAG && n[0][1].isConst())
  {
    // (bag.choose (mkBag x c)) = x where c is a constant > 0
    return BagsRewriteResponse(n[0][0], Rewrite::CHOOSE_MK_BAG);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteCard(const TNode& n) const
{
  Assert(n.getKind() == BAG_CARD);
  if (n[0].getKind() == MK_BAG && n[0][1].isConst())
  {
    // (bag.card (mkBag x c)) = c where c is a constant > 0
    return BagsRewriteResponse(n[0][1], Rewrite::CARD_MK_BAG);
  }

  if (n[0].getKind() == UNION_DISJOINT)
  {
    // (bag.card (union-disjoint A B)) = (+ (bag.card A) (bag.card B))
    Node A = d_nm->mkNode(BAG_CARD, n[0][0]);
    Node B = d_nm->mkNode(BAG_CARD, n[0][1]);
    Node plus = d_nm->mkNode(PLUS, A, B);
    return BagsRewriteResponse(plus, Rewrite::CARD_DISJOINT);
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteIsSingleton(const TNode& n) const
{
  Assert(n.getKind() == BAG_IS_SINGLETON);
  if (n[0].getKind() == MK_BAG)
  {
    // (bag.is_singleton (mkBag x c)) = (c == 1)
    Node one = d_nm->mkConst(Rational(1));
    Node equal = n[0][1].eqNode(one);
    return BagsRewriteResponse(equal, Rewrite::IS_SINGLETON_MK_BAG);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
