/*********************                                                        */
/*! \file cad_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief CAD-based solver based on https://arxiv.org/pdf/2003.05633.pdf.
 **/

#ifndef CVC4__THEORY__ARITH__CAD_SOLVER_H
#define CVC4__THEORY__ARITH__CAD_SOLVER_H

#include <vector>

#include "expr/node.h"
#include "theory/arith/nl/cad/cdcac.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/arith/theory_arith.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

/**
 * A solver for nonlinear arithmetic that implements the CAD-based method
 * described in https://arxiv.org/pdf/2003.05633.pdf.
 */
class CadSolver
{
 public:
  CadSolver(TheoryArith& containing, NlModel& model);
  ~CadSolver();

  /**
   * This is called at the beginning of last call effort check, where
   * assertions are the set of assertions belonging to arithmetic,
   * false_asserts is the subset of assertions that are false in the current
   * model, and xts is the set of extended function terms that are active in
   * the current context.
   */
  void initLastCall(const std::vector<Node>& assertions);

  /**
   * Perform a full check, returning either {} or a single lemma.
   * If the result is empty, the input is satisfiable and a model is available
   * for construct_model_if_available. Otherwise, the single lemma can be used
   * as an infeasible subset.
   */
  std::vector<NlLemma> checkFull();

  /**
   * Perform a partial check, returning either {} or a list of lemmas.
   * If the result is empty, the input is satisfiable and a model is available
   * for construct_model_if_available. Otherwise, the lemmas exclude some part
   * of the search space.
   */
  std::vector<NlLemma> checkPartial();

  /**
   * If a model is available (indicated by the last call to check_full() or
   * check_partial()) this method puts a satisfying assignment in d_model,
   * clears the list of assertions, and returns true.
   * Otherwise, this method returns false.
   */
  bool constructModelIfAvailable(std::vector<Node>& assertions);

 private:
  /**
   * The variable used to encode real algebraic numbers to nodes.
   */
  Node d_ranVariable;

#ifdef CVC4_POLY_IMP
  /**
   * The object implementing the actual decision procedure.
   */
  cad::CDCAC d_CAC;
#endif
  /**
   * Indicates whether we found satisfiability in the last call to
   * checkFullRefine.
   */
  bool d_foundSatisfiability = false;

  /** The theory of arithmetic containing this extension.*/
  TheoryArith& d_containing;
  /** Reference to the non-linear model object */
  NlModel& d_model;
}; /* class CadSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__CAD_SOLVER_H */
