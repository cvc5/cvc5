/*********************                                                        */
/*! \file solver_state.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags state object
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__THEORY_SOLVER_STATE_H
#define CVC4__THEORY__BAGS__THEORY_SOLVER_STATE_H

#include <map>
#include <vector>

#include "theory/theory_state.h"

namespace CVC4 {
namespace theory {
namespace bags {

class SolverState : public TheoryState
{
 public:
  SolverState(context::Context* c, context::UserContext* u, Valuation val);

  void registerBag(TNode n);

  /**
   * @param n has the form (bag.count e A)
   * @pre bag A needs is already registered using registerBag(A)
   * @return a unique skolem for (bag.count e A)
   */
  void registerCountTerm(TNode n);
  /** get all bag terms */
  const std::set<Node>& getBags();
  /**
   * @pre B is a registered bag
   * @return all elements associated with bag B so far
   * Note that associated elements are not necessarily elements in B
   * Example:
   * (assert (= 1 (bag.count x (difference_remove A B))))
   * element x is associated with bags A, B, (difference_remove A B)
   * albeit x is definitely not in B.
   */
  const std::set<Node>& getElements(Node B);
  /** clear all bags data structures */
  void reset();

  /** merge the elements of the two registered bags n1, n2 */
  void mergeBags(TNode n1, TNode n2);

 private:
  /** constants */
  Node d_true;
  Node d_false;
  std::set<Node> d_bags;
  /** bag -> associated elements */
  std::map<Node, std::set<Node>> d_bagElements;
}; /* class SolverState */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__THEORY_SOLVER_STATE_H */
