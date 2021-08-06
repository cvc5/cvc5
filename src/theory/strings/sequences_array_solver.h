/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sequences solver for seq.nth/seq.update.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__SEQ_ARRAY_SOLVER_H
#define CVC5__THEORY__STRINGS__SEQ_ARRAY_SOLVER_H

#include "theory/strings/core_solver.h"
#include "theory/strings/extf_solver.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/solver_state.h"
#include "theory/strings/term_registry.h"

namespace cvc5 {
namespace theory {
namespace strings {

class SequencesArraySolver
{
 public:
  SequencesArraySolver(SolverState& s,
                       InferenceManager& im,
                       TermRegistry& tr,
                       CoreSolver& cs,
                       ExtfSolver& es,
                       ExtTheory& extt);
  ~SequencesArraySolver();

  /**
   * Perform reasoning about seq.nth and seq.update operations.
   *
   * Can assume that seq.update / seq.nth terms only apply to concatenation-free
   * equivalence classes.
   */
  void check(const std::vector<Node>& nthTerms,
             const std::vector<Node>& updateTerms);
  
  /**
   * 
   * @param eqc The sequence equivalence class representative. We can assume
   * the equivalence class of eqc contains no concatenation terms.
   * @return the map corresponding to the model for eqc. The domain of
   * the returned map should be in distinct integer equivalence classes of the
   * equality engine of strings theory. The model assigned to eqc will be
   * a skeleton constructed via seq.++ where the components take values from
   * this map.
   */
  const std::map<Node, Node>& getWriteModel(Node eqc);
 private:
  /** The solver state object */
  SolverState& d_state;
  /** The (custom) output channel of the theory of strings */
  InferenceManager& d_im;
  /** Reference to the term registry of theory of strings */
  TermRegistry& d_termReg;
  /** reference to the core solver, used for certain queries */
  CoreSolver& d_csolver;
  /** reference to the extended solver, used for certain queries */
  ExtfSolver& d_esolver;
  /** the extended theory object for the theory of strings */
  ExtTheory& d_extt;
  /** The write model */
  std::map< Node, std::map< Node, Node > > d_writeModel;
  context::CDHashSet<Node> d_lem;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5

#endif
