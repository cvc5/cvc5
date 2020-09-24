/*********************                                                        */
/*! \file theory_bags_rewriter.cpp
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

#include "theory/bags/theory_bags_rewriter.h"

#include "normal_form.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

RewriteResponse TheoryBagsRewriter::postRewrite(TNode n)
{
  if (n.isConst())
  {
    // no need to rewrite n if it is already in a normal form
    return RewriteResponse(REWRITE_DONE, n);
  }
  Kind k = n.getKind();
  switch (k)
  {
    case kind::MK_BAG: return rewriteMakeBag(n);
    case kind::BAG_COUNT: return rewriteBagCount(n);
    case kind::UNION_MAX: return rewriteUnionMax(n);
    case kind::UNION_DISJOINT: return rewriteUnionDisjoint(n);
    case kind::INTERSECTION_MIN: return rewriteIntersectionMin(n);
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse TheoryBagsRewriter::preRewrite(TNode n)
{
  if (n.getKind() == EQUAL)
  {
    if (n[0] == n[1])
    {
      NodeManager* nm = NodeManager::currentNM();
      return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
    }
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse TheoryBagsRewriter::rewriteMakeBag(const TNode& n) const
{
  Assert(n.getKind() == MK_BAG);
  // return emptybag for negative or zero multiplicity
  if (n[1].isConst() && n[1].getConst<Rational>().sgn() != 1)
  {
    // (mkBag x -1) = emptybag
    NodeManager* nm = NodeManager::currentNM();
    Node emptybag = nm->mkConst(EmptyBag(n.getType()));
    return RewriteResponse(REWRITE_AGAIN, emptybag);
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse TheoryBagsRewriter::rewriteBagCount(const TNode& n) const
{
  Assert(n.getKind() == BAG_COUNT);
  if (n[1].isConst() && n[1].getKind() == EMPTYBAG)
  {
    // (bag.count x emptybag) = 0
    NodeManager* nm = NodeManager::currentNM();
    return RewriteResponse(REWRITE_AGAIN, nm->mkConst(Rational(0)));
  }
  if (n[1].getKind() == MK_BAG && n[0] == n[1][0])
  {
    // (bag.count x (mkBag x c) = c where c > 0 is a constant
    return RewriteResponse(REWRITE_AGAIN, n[1][1]);
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse TheoryBagsRewriter::rewriteUnionMax(const TNode& n) const
{
  Assert(n.getKind() == UNION_MAX);
  if (n[1].getKind() == EMPTYBAG || n[0] == n[1])
  {
    // (union_max A A) = A
    // (union_max A emptybag) = A
    return RewriteResponse(REWRITE_AGAIN, n[0]);
  }
  if (n[0].getKind() == EMPTYBAG)
  {
    // (union_max emptybag A) = A
    return RewriteResponse(REWRITE_AGAIN, n[1]);
  }
  if (n[1].getKind() == UNION_MAX && (n[0] == n[1][0] || n[0] == n[1][1]))
  {
    // (union_max A (union_max A B) = (union_max A B)
    // (union_max A (union_max B A) = (union_max B A)
    return RewriteResponse(REWRITE_AGAIN, n[1]);
  }
  if (n[0].getKind() == UNION_MAX && (n[0][0] == n[1] || n[0][1] == n[1]))
  {
    // (union_max (union_max A B) A) = (union_max A B)
    // (union_max (union_max B A) A) = (union_max B A)
    return RewriteResponse(REWRITE_AGAIN, n[0]);
  }

  if (n[1].getKind() == UNION_DISJOINT && (n[0] == n[1][0] || n[0] == n[1][1]))
  {
    // (union_max A (union_disjoint A B)) = (union_disjoint A B)
    // (union_max A (union_disjoint B A)) = (union_disjoint B A)
    return RewriteResponse(REWRITE_AGAIN, n[1]);
  }
  if (n[0].getKind() == UNION_DISJOINT && (n[0][0] == n[1] || n[0][1] == n[1]))
  {
    // (union_max (union_disjoint A B) A) = (union_disjoint A B)
    // (union_max (union_disjoint B A) A) = (union_disjoint B A)
    return RewriteResponse(REWRITE_AGAIN, n[0]);
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse TheoryBagsRewriter::rewriteUnionDisjoint(const TNode& n) const
{
  Assert(n.getKind() == UNION_DISJOINT);
  if (n[1].getKind() == EMPTYBAG)
  {
    // (union_disjoint A emptybag) = A
    return RewriteResponse(REWRITE_AGAIN, n[0]);
  }
  if (n[0].getKind() == EMPTYBAG)
  {
    // (union_disjoint emptybag A) = A
    return RewriteResponse(REWRITE_AGAIN, n[1]);
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

RewriteResponse TheoryBagsRewriter::rewriteIntersectionMin(const TNode& n) const
{
  Assert(n.getKind() == INTERSECTION_MIN);
  if (n[1].getKind() == EMPTYBAG)
  {
    // (intersection_min A emptybag) = emptybag
    return RewriteResponse(REWRITE_AGAIN, n[0]);
  }
  if (n[0].getKind() == EMPTYBAG)
  {
    // (intersection_min emptybag A) = emptybag
    return RewriteResponse(REWRITE_AGAIN, n[1]);
  }
  if (n[0] == n[1])
  {
    // (intersection_min A A) = A
    return RewriteResponse(REWRITE_AGAIN, n[0]);
  }
  if (n[1].getKind() == UNION_DISJOINT || n[1].getKind() == UNION_MAX)
  {
    std::set<Node> bags(n[1].begin(), n[1].end());
    if (bags.find(n[0]) != bags.end())
    {
      // (intersection_min A (union_disjoint A B)) = A
      // (intersection_min A (union_disjoint B A)) = A
      // (intersection_min A (union_max A B)) = A
      // (intersection_min A (union_max B A)) = A
      return RewriteResponse(REWRITE_AGAIN, n[0]);
    }
  }

  if (n[0].getKind() == UNION_DISJOINT || n[0].getKind() == UNION_MAX)
  {
    std::set<Node> bags(n[0].begin(), n[0].end());
    if (bags.find(n[1]) != bags.end())
    {
      // (intersection_min (union_disjoint A B) A) = A
      // (intersection_min (union_disjoint B A) A) = A
      // (intersection_min (union_max A B) A) = A
      // (intersection_min (union_max B A) A) = A
      return RewriteResponse(REWRITE_AGAIN, n[1]);
    }
  }

  return RewriteResponse(REWRITE_DONE, n);
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
