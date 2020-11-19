/*********************                                                        */
/*! \file nested_qe.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Methods for counterexample-guided quantifier instantiation
 ** based on nested quantifier elimination.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CEQGI__NESTED_QE_H
#define CVC4__THEORY__QUANTIFIERS__CEQGI__NESTED_QE_H

#include <unordered_set>

#include "context/cdhashmap.h"
#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class NestedQe
{
  using NodeNodeMap = context::CDHashMap<Node, Node, NodeHashFunction>;

 public:
  NestedQe(context::UserContext* u);
  ~NestedQe() {}
  /**
   * Process quantified formula. If this returns true, then q was processed
   * via nested quantifier elimination (either during this call or previously
   * in this user context). If q was processed in this call, the lemma:
   *   (= q qqe)
   * is added to lem, where qqe is the result of nested quantifier elimination
   * on q.
   */
  bool process(Node q, std::vector<Node>& lems);
  /**
   * Have we processed q using the above method?
   */
  bool hasProcessed(Node q) const;

  /**
   * Get nested quantification. Returns true if q has nested quantifiers.
   * Adds each nested quantifier in the body of q to nqs.
   */
  static bool getNestedQuantification(
      Node q, std::unordered_set<Node, NodeHashFunction>& nqs);
  /**
   * Does quantified formula q have nested quantification?
   */
  static bool hasNestedQuantification(Node q);
  /**
   * Do nested quantifier elimination. Returns a formula that is equivalent to
   * q and has no nested quantification. If keepTopLevel is false, then the
   * returned formula is quantifier-free. Otherwise, it is a quantified formula
   * with no nested quantification.
   */
  static Node doNestedQe(Node q, bool keepTopLevel = false);
  /**
   * Run quantifier elimination on quantified formula q, where q has no nested
   * quantification. This method invokes a subsolver for performing quantifier
   * elimination.
   */
  static Node doQe(Node q);

 private:
  /**
   * Mapping from quantified formulas q to the result of doNestedQe(q, true).
   */
  NodeNodeMap d_qnqe;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
