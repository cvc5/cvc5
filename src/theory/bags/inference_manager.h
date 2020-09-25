/*********************                                                        */
/*! \file inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The inference manager for the theory of bags.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__INFERENCE_MANAGER_H
#define CVC4__THEORY__BAGS__INFERENCE_MANAGER_H

#include "theory/bags/solver_state.h"
#include "theory/inference_manager_buffered.h"

namespace CVC4 {
namespace theory {
namespace bags {

/** Inference manager
 *
 * This class manages inferences produced by the theory of bags. It manages
 * whether inferences are processed as external lemmas on the output channel
 * of theory of bags or internally as literals asserted to the equality engine
 * of theory of bags. The latter literals are referred to as "facts".
 */
class InferenceManager : public InferenceManagerBuffered
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  InferenceManager(Theory& t, SolverState& s, ProofNodeManager* pnm);

 private:
  /** constants */
  Node d_true;
  Node d_false;
  /**
   * Reference to the state object for the theory of bags. We store the
   * (derived) state here, since it has additional methods required in this
   * class.
   */
  SolverState& d_state;
};

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__INFERENCE_MANAGER_H */
