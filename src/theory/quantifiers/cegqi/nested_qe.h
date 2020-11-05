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
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;

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

  /** Get nested quantification */
  static bool getNestedQuantification(
      Node q, std::unordered_set<Node, NodeHashFunction>& nqs);
  /** 
   * Does quantified formula q have nested quantification?
   */
  static bool hasNestedQuantification(Node q);
  /**
   * Does q have nested quantification?
   */
  /**
   * Do nested quantifier elimination.
   */
  static Node doNestedQe(Node q, bool keepTopLevel = false);
  /**
   * Run quantifier free formula for quantified formula q with no nested
   * quantification.
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
