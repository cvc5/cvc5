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

#include "normal_form.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

RewriteResponse BagsRewriter::postRewrite(TNode n)
{
  if (n.isConst())
  {
    // no need to rewrite n if it is already in a normal form
    return RewriteResponse(REWRITE_DONE, n);
  }
  if (NormalForm::AreChildrenConstants(n))
  {
    Node normal = NormalForm::getNormalForm(n);
    return RewriteResponse(REWRITE_DONE, n);
  }
  Kind k = n.getKind();
  switch (k)
  {
    case MK_BAG: return rewriteMakeBag(n);
    case BAG_COUNT: return rewriteBagCount(n);
    case UNION_MAX: return rewriteUnionMax(n);
    case UNION_DISJOINT: return rewriteUnionDisjoint(n);
    case INTERSECTION_MIN: return rewriteIntersectionMin(n);
    case DIFFERENCE_SUBTRACT: return rewriteDifferenceSubtract(n);
    case DIFFERENCE_REMOVE: return rewriteDifferenceRemove(n);
    case BAG_CHOOSE: return rewriteChoose(n);
    case BAG_CARD: return rewriteCard(n);
    case BAG_IS_SINGLETON: return rewriteIsSingleton(n);
    default: break;
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse BagsRewriter::preRewrite(TNode n)
{
  Kind k = n.getKind();
  switch (k)
  {
    case EQUAL: return rewriteEqual(n);
    case BAG_IS_INCLUDED: return rewriteIsIncluded(n);
    default: break;
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse BagsRewriter::rewriteEqual(const TNode& n) const
{
  Assert(n.getKind() == EQUAL);
  if (n[0] == n[1])
  {
    NodeManager* nm = NodeManager::currentNM();
    return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse BagsRewriter::rewriteIsIncluded(const TNode& n) const
{
  Assert(n.getKind() == BAG_IS_INCLUDED);
  // (bag.is_included A B) = ((difference_subtract A B) == emptybag)
  NodeManager* nm = NodeManager::currentNM();
  Node emptybag = nm->mkConst(EmptyBag(n[0].getType()));
  Node subtract = nm->mkNode(DIFFERENCE_SUBTRACT, n[0], n[1]);
  Node equal = subtract.eqNode(emptybag);
  return RewriteResponse(REWRITE_AGAIN, equal);
}

RewriteResponse BagsRewriter::rewriteMakeBag(const TNode& n) const
{
  Assert(n.getKind() == MK_BAG);
  // return emptybag for negative or zero multiplicity
  if (n[1].isConst() && n[1].getConst<Rational>().sgn() != 1)
  {
    // (mkBag x c) = emptybag where c <= 0
    NodeManager* nm = NodeManager::currentNM();
    Node emptybag = nm->mkConst(EmptyBag(n.getType()));
    return RewriteResponse(REWRITE_DONE, emptybag);
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse BagsRewriter::rewriteBagCount(const TNode& n) const
{
  Assert(n.getKind() == BAG_COUNT);
  if (n[1].isConst() && n[1].getKind() == EMPTYBAG)
  {
    // (bag.count x emptybag) = 0
    NodeManager* nm = NodeManager::currentNM();
    return RewriteResponse(REWRITE_DONE, nm->mkConst(Rational(0)));
  }
  if (n[1].getKind() == MK_BAG && n[0] == n[1][0])
  {
    // (bag.count x (mkBag x c) = c where c > 0 is a constant
    return RewriteResponse(REWRITE_DONE, n[1][1]);
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse BagsRewriter::rewriteUnionMax(const TNode& n) const
{
  Assert(n.getKind() == UNION_MAX);
  if (n[1].getKind() == EMPTYBAG || n[0] == n[1])
  {
    // (union_max A A) = A
    // (union_max A emptybag) = A
    return RewriteResponse(REWRITE_DONE, n[0]);
  }
  if (n[0].getKind() == EMPTYBAG)
  {
    // (union_max emptybag A) = A
    return RewriteResponse(REWRITE_DONE, n[1]);
  }
  if (n[1].getKind() == UNION_MAX && (n[0] == n[1][0] || n[0] == n[1][1]))
  {
    // (union_max A (union_max A B) = (union_max A B)
    // (union_max A (union_max B A) = (union_max B A)
    return RewriteResponse(REWRITE_DONE, n[1]);
  }
  if (n[0].getKind() == UNION_MAX && (n[0][0] == n[1] || n[0][1] == n[1]))
  {
    // (union_max (union_max A B) A) = (union_max A B)
    // (union_max (union_max B A) A) = (union_max B A)
    return RewriteResponse(REWRITE_DONE, n[0]);
  }

  if (n[1].getKind() == UNION_DISJOINT && (n[0] == n[1][0] || n[0] == n[1][1]))
  {
    // (union_max A (union_disjoint A B)) = (union_disjoint A B)
    // (union_max A (union_disjoint B A)) = (union_disjoint B A)
    return RewriteResponse(REWRITE_DONE, n[1]);
  }
  if (n[0].getKind() == UNION_DISJOINT && (n[0][0] == n[1] || n[0][1] == n[1]))
  {
    // (union_max (union_disjoint A B) A) = (union_disjoint A B)
    // (union_max (union_disjoint B A) A) = (union_disjoint B A)
    return RewriteResponse(REWRITE_DONE, n[0]);
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse BagsRewriter::rewriteUnionDisjoint(const TNode& n) const
{
  Assert(n.getKind() == UNION_DISJOINT);
  if (n[1].getKind() == EMPTYBAG)
  {
    // (union_disjoint A emptybag) = A
    return RewriteResponse(REWRITE_DONE, n[0]);
  }
  if (n[0].getKind() == EMPTYBAG)
  {
    // (union_disjoint emptybag A) = A
    return RewriteResponse(REWRITE_DONE, n[1]);
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
      NodeManager* nm = NodeManager::currentNM();
      Node rewritten = nm->mkNode(UNION_DISJOINT, n[0][0], n[0][1]);
      return RewriteResponse(REWRITE_AGAIN, rewritten);
    }
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse BagsRewriter::rewriteIntersectionMin(const TNode& n) const
{
  Assert(n.getKind() == INTERSECTION_MIN);
  if (n[0].getKind() == EMPTYBAG)
  {
    // (intersection_min emptybag A) = emptybag
    return RewriteResponse(REWRITE_DONE, n[0]);
  }
  if (n[1].getKind() == EMPTYBAG)
  {
    // (intersection_min A emptybag) = emptybag
    return RewriteResponse(REWRITE_DONE, n[1]);
  }
  if (n[0] == n[1])
  {
    // (intersection_min A A) = A
    return RewriteResponse(REWRITE_DONE, n[0]);
  }
  if (n[1].getKind() == UNION_DISJOINT || n[1].getKind() == UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (intersection_min A (union_disjoint A B)) = A
      // (intersection_min A (union_disjoint B A)) = A
      // (intersection_min A (union_max A B)) = A
      // (intersection_min A (union_max B A)) = A
      return RewriteResponse(REWRITE_DONE, n[0]);
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
      return RewriteResponse(REWRITE_DONE, n[1]);
    }
  }

  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse BagsRewriter::rewriteDifferenceSubtract(const TNode& n) const
{
  Assert(n.getKind() == DIFFERENCE_SUBTRACT);
  if (n[0].getKind() == EMPTYBAG || n[1].getKind() == EMPTYBAG)
  {
    // (difference_subtract A emptybag) = A
    // (difference_subtract emptybag B) = emptybag
    return RewriteResponse(REWRITE_DONE, n[0]);
  }
  if (n[0] == n[1])
  {
    // (difference_subtract A A) = emptybag
    NodeManager* nm = NodeManager::currentNM();
    Node emptyBag = nm->mkConst(EmptyBag(n.getType()));
    return RewriteResponse(REWRITE_DONE, emptyBag);
  }

  if (n[0].getKind() == UNION_DISJOINT)
  {
    if (n[1] == n[0][0])
    {
      // (difference_subtract (union_disjoint A B) A) = B
      return RewriteResponse(REWRITE_DONE, n[0][1]);
    }
    if (n[1] == n[0][1])
    {
      // (difference_subtract (union_disjoint B A) A) = B
      return RewriteResponse(REWRITE_DONE, n[0][0]);
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
      NodeManager* nm = NodeManager::currentNM();
      Node emptyBag = nm->mkConst(EmptyBag(n.getType()));
      return RewriteResponse(REWRITE_DONE, emptyBag);
    }
  }

  if (n[0].getKind() == INTERSECTION_MIN)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (difference_subtract (intersection_min A B) A) = emptybag
      // (difference_subtract (intersection_min B A) A) = emptybag
      NodeManager* nm = NodeManager::currentNM();
      Node emptyBag = nm->mkConst(EmptyBag(n.getType()));
      return RewriteResponse(REWRITE_DONE, emptyBag);
    }
  }

  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse BagsRewriter::rewriteDifferenceRemove(const TNode& n) const
{
  Assert(n.getKind() == DIFFERENCE_REMOVE);

  if (n[0].getKind() == EMPTYBAG || n[1].getKind() == EMPTYBAG)
  {
    // (difference_remove A emptybag) = A
    // (difference_remove emptybag B) = emptybag
    return RewriteResponse(REWRITE_DONE, n[0]);
  }

  if (n[0] == n[1])
  {
    // (difference_remove A A) = emptybag
    NodeManager* nm = NodeManager::currentNM();
    Node emptyBag = nm->mkConst(EmptyBag(n.getType()));
    return RewriteResponse(REWRITE_DONE, emptyBag);
  }

  if (n[1].getKind() == UNION_DISJOINT || n[1].getKind() == UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (difference_remove A (union_disjoint A B)) = emptybag
      // (difference_remove A (union_disjoint B A)) = emptybag
      // (difference_remove A (union_max A B)) = emptybag
      // (difference_remove A (union_max B A)) = emptybag
      NodeManager* nm = NodeManager::currentNM();
      Node emptyBag = nm->mkConst(EmptyBag(n.getType()));
      return RewriteResponse(REWRITE_DONE, emptyBag);
    }
  }

  if (n[0].getKind() == INTERSECTION_MIN)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (difference_remove (intersection_min A B) A) = emptybag
      // (difference_remove (intersection_min B A) A) = emptybag
      NodeManager* nm = NodeManager::currentNM();
      Node emptyBag = nm->mkConst(EmptyBag(n.getType()));
      return RewriteResponse(REWRITE_DONE, emptyBag);
    }
  }

  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse BagsRewriter::rewriteChoose(const TNode& n) const
{
  Assert(n.getKind() == BAG_CHOOSE);
  if (n[0].getKind() == MK_BAG && n[0][1].isConst())
  {
    // (bag.choose (mkBag x c)) = x where c is a constant > 0
    return RewriteResponse(REWRITE_DONE, n[0][0]);
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse BagsRewriter::rewriteCard(const TNode& n) const
{
  Assert(n.getKind() == BAG_CARD);
  if (n[0].getKind() == EMPTYBAG)
  {
    // (bag.card emptybag) = 0
    Node zero = NodeManager::currentNM()->mkConst(Rational(0));
    return RewriteResponse(REWRITE_DONE, zero);
  }
  if (n[0].getKind() == MK_BAG && n[0][1].isConst())
  {
    // (bag.card (mkBag x c)) = c where c is a constant > 0
    return RewriteResponse(REWRITE_DONE, n[0][1]);
  }

  if (n[0].getKind() == UNION_DISJOINT)
  {
    NodeManager* nm = NodeManager::currentNM();

    // (bag.card (union-disjoint A B)) = (+ (bag.card A) (bag.card B))
    Node A = nm->mkNode(BAG_CARD, n[0][0]);
    Node B = nm->mkNode(BAG_CARD, n[0][1]);
    Node plus = nm->mkNode(PLUS, A, B);
    return RewriteResponse(REWRITE_AGAIN_FULL, plus);
  }

  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse BagsRewriter::rewriteIsSingleton(const TNode& n) const
{
  Assert(n.getKind() == BAG_IS_SINGLETON);
  NodeManager* nm = NodeManager::currentNM();
  if (n[0].getKind() == EMPTYBAG)
  {
    // (bag.is_singleton emptybag) = false
    return RewriteResponse(REWRITE_DONE, nm->mkConst(false));
  }
  if (n[0].getKind() == MK_BAG)
  {
    // (bag.is_singleton (mkBag x c) = (c == 1)
    Node one = nm->mkConst(Rational(1));
    Node equal = n[0][1].eqNode(one);
    return RewriteResponse(REWRITE_AGAIN, equal);
  }
  return RewriteResponse(REWRITE_DONE, n);
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
