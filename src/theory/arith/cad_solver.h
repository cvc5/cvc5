/*********************                                                        */
/*! \file cad_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief New non-linear solver
 **/

#ifndef CVC4__THEORY__ARITH__CAD_SOLVER_H
#define CVC4__THEORY__ARITH__CAD_SOLVER_H

#include <map>
#include <vector>

#include "context/cdhashset.h"
#include "expr/node.h"
#include "theory/arith/nl_model.h"
#include "theory/arith/theory_arith.h"

namespace CVC4 {
namespace theory {
namespace arith {

/** Cylindrical algebraic decomposition (CAD) solver class
 *
 */
class CadSolver
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  CadSolver(TheoryArith& containing, NlModel& model);
  ~CadSolver();

  /** init last call
   *
   * This is called at the beginning of last call effort check, where
   * assertions are the set of assertions belonging to arithmetic,
   * false_asserts is the subset of assertions that are false in the current
   * model, and xts is the set of extended function terms that are active in
   * the current context.
   */
  void initLastCall(const std::vector<Node>& assertions,
                    const std::vector<Node>& false_asserts,
                    const std::vector<Node>& xts);
  /** check initial refine
   * 
   * This should be a heuristic incomplete check that only introduces a
   * small number of new terms in the lemmas it returns.
   */
  std::vector<Node> checkInitialRefine();
  /** check full refine
   *
   * This should be a complete check that returns at least one lemma to
   * rule out the current model.
   */
  std::vector<Node> checkFullRefine();
  /** preprocess assertions check model
   *
   * This modifies the given assertions in preparation for running a call
   * to NlModel::checkModel.
   *
   * This method returns false if NlModel::checkModel should not be run.
   */
  void preprocessAssertionsCheckModel(std::vector<Node>& assertions);
 private:
  // The theory of arithmetic containing this extension.
  TheoryArith& d_containing;
  /** Reference to the non-linear model object */
  NlModel& d_model;
  /** commonly used terms */
  Node d_zero;
  Node d_one;
  Node d_neg_one;
  Node d_true;
  Node d_false;
  
}; /* class CadSolver */

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__CAD_SOLVER_H */
