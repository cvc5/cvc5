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

  void registerClass(TNode n);

  std::map<TypeNode, std::vector<Node>> & getBags();

  std::vector<Node> & getBags(TypeNode t);

  std::vector<Node> & getElements(TypeNode t);

 private:
  /** constants */
  Node d_true;
  Node d_false;
  std::map<TypeNode, std::vector<Node>> d_bags;
  std::map<TypeNode, std::vector<Node>> d_elements;
  /** bag -> element -> multiplicity */
  std::map<Node, std::map<Node, Node>> d_count;
}; /* class SolverState */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__THEORY_SOLVER_STATE_H */
