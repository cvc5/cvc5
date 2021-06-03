/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * CAD-based solver based on https://arxiv.org/pdf/2003.05633.pdf.
 */

#ifndef CVC5__THEORY__ARITH__CAD_SOLVER_H
#define CVC5__THEORY__ARITH__CAD_SOLVER_H

#include <vector>

#include "context/context.h"
#include "expr/node.h"
#include "theory/arith/nl/cad/cdcac.h"
#include "theory/arith/nl/cad/proof_checker.h"

namespace cvc5 {

class ProofNodeManager;

namespace theory {
namespace arith {

class InferenceManager;

namespace nl {

class NlModel;

/**
 * A solver for nonlinear arithmetic that implements the CAD-based method
 * described in https://arxiv.org/pdf/2003.05633.pdf.
 */
class CadSolver
{
 public:
  CadSolver(InferenceManager& im,
            NlModel& model,
            context::Context* ctx,
            ProofNodeManager* pnm);
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
  void checkFull();

  /**
   * Perform a partial check, returning either {} or a list of lemmas.
   * If the result is empty, the input is satisfiable and a model is available
   * for construct_model_if_available. Otherwise, the lemmas exclude some part
   * of the search space.
   */
  void checkPartial();

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

#ifdef CVC5_POLY_IMP
  /**
   * The object implementing the actual decision procedure.
   */
  cad::CDCAC d_CAC;
  /** The proof checker for cad proofs */
  cad::CADProofRuleChecker d_proofChecker;
#endif
  /**
   * Indicates whether we found satisfiability in the last call to
   * checkFullRefine.
   */
  bool d_foundSatisfiability;

  /** The inference manager we are pushing conflicts and lemmas to. */
  InferenceManager& d_im;
  /** Reference to the non-linear model object */
  NlModel& d_model;
}; /* class CadSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ARITH__CAD_SOLVER_H */
