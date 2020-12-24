/*********************                                                        */
/*! \file core_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Core solver for the theory of bags.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAG__SOLVER_H
#define CVC4__THEORY__BAG__SOLVER_H

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "theory/bags/infer_info.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/normal_form.h"
#include "theory/bags/solver_state.h"
#include "theory/bags/term_registry.h"

namespace CVC4 {
namespace theory {
namespace bags {

/** The core solver for the theory of bags
 *
 * This implements techniques for handling (dis)equalities involving
 * bag terms.
 */
class BagSolver
{
  friend class InferenceManager;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;

 public:
  BagSolver(SolverState& s, InferenceManager& im, TermRegistry& tr);
  ~BagSolver();

  void postCheck();

 private:
  /** The solver state object */
  SolverState& d_state;
  /** The (custom) output channel of the theory of bags */
  InferenceManager& d_im;
  /** Reference to the term registry of theory of bags */
  TermRegistry& d_termReg;
  /** Commonly used constants */
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
}; /* class BagSolver */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAG__SOLVER_H */
