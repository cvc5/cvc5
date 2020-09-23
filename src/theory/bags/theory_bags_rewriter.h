/*********************                                                        */
/*! \file theory_bags_rewriter.h
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

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__THEORY_BAGS_REWRITER_H
#define CVC4__THEORY__BAGS__THEORY_BAGS_REWRITER_H

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace bags {

class TheoryBagsRewriter : public TheoryRewriter
{
 public:
  /**
   * Rewrite rules:
   * - node is a constant in normal form
   *   node = node // return the same node
   * - node is not in a normal form, but its children are
   *   node = normal_form_node
   * - union_max
   *   (union_max A emptybag) = A
   *   (union_max emptybag B) =>B
   *   (union_max A A) = A
   *   (union_max A (union_max A B) = (union_max A B)
   *   (union_max A (union_max B A) = (union_max B A)
   *   (union_max A (union_disjoint A B) = (union_disjoint A B)
   *   (union_max A (union_disjoint B A) = (union_disjoint A B)
   * - union_disjoint
   *   (union_disjoint A emptybag) = A
   *   (union_disjoint emptybag B) = B
   *   (union_disjoint (A union_max B) (intersection_min A B)) =
   *        (union_disjoint A B) // sum(a,b) = max(a,b) + min(a,b)
   * - intersection_min
   *   (intersection_min A emptybag) = emptybag
   *   (intersection_min emptybag B) = emptybag
   *   (intersection_min A A) = A
   *   (intersection_min A (union_disjoint A B)) = A
   *   (intersection_min A (union_disjoint B A)) = A
   * - difference_subtract
   *   (difference_subtract A emptybag) = A
   *   (difference_subtract emptybag B) = emptybag
   *   (difference_subtract A A) = emptybag
   * - difference_remove
   *   (difference_remove A emptybag) = A
   *   (difference_remove emptybag B) = emptybag
   *   (difference_subtract A A) = emptybag
   * - bag.is_included
   *   (bag.is_included A B) = ((difference_subtract A B) == emptybag)
   * - bag.choose
   *   (bag.choose x (mkBag x c)) = x where c is a constant > 0
   * - bag.card
   *   (bag.card emptybag) = 0
   *   (bag.card (mkBag x c)) = c where c is a constant > 0
   * - bag.is_singleton
   *   (bag.is_singleton emptybag) = false
   *   (bag.is_singleton (mkBag x c) = (c == 1) where c is a constant > 0
   * @param n
   * @return
   */
  RewriteResponse postRewrite(TNode n) override;

  RewriteResponse preRewrite(TNode node) override;

 private:
  /**
   * patterns for mkBag:
   * - (mkBag x 0) = (emptybag T) where T is the type of x
   * - (mkBag x (-c)) = (emptybag T) where T is the type of x, and c > 0 is a
   *   constant
   * - otherwise = n
   */
  RewriteResponse rewriteMakeBag(const TNode& n) const;
  /**
   * patterns for bag.count
   * - (bag.count x emptybag) = 0
   * - (bag.count x (mkBag x c) = c where c > 0 is a constant
   * - otherwise = n
   */
  RewriteResponse rewriteBagCount(const TNode& n) const;
}; /* class TheoryBagsRewriter */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__THEORY_BAGS_REWRITER_H */
