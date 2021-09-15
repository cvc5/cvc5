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

#ifndef CVC5__THEORY__STRINGS__SEQ_UPDATE_SOLVER_H
#define CVC5__THEORY__STRINGS__SEQ_UPDATE_SOLVER_H

#include "context/cdhashset.h"
#include "theory/strings/core_solver.h"
#include "theory/strings/extf_solver.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/solver_state.h"
#include "theory/strings/term_registry.h"
#include "theory/strings/sequences_array_solver.h"

namespace cvc5 {
namespace theory {
namespace strings {

/**
  * This is a prototype solver for reasoning about seq.update and seq.nth
  * natively. This class specifically addresses the combination of this
  * operators with concatenation. It relies on a subsolver for doing array
  * like reasoning (sequences_array_solver.h).
  */
class SequencesUpdateSolver : protected EnvObj
{
  typedef context::CDHashSet<Node> NodeSet;
 public:
  SequencesUpdateSolver(Env& env,
                        SolverState& s,
                        InferenceManager& im,
                        TermRegistry& tr,
                        CoreSolver& cs,
                        ExtfSolver& es,
                        ExtTheory& extt);
  ~SequencesUpdateSolver();

  /**
   * Perform reasoning about seq.nth and seq.update operations, in particular,
   * their application to concatenation terms.
   */
  void checkArrayConcat();
  /**
   * Perform reasoning about seq.nth and seq.update operations.
   */
  void checkArray();
  void checkArrayEager();

  /** is handled update */
  static bool isHandledUpdate(Node n);
  /** get base */
  static Node getUpdateBase(Node n);
  
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
  /** check terms of given kind */
  void checkTerms(Kind k);
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
  /** Current terms */
  std::map<Kind, std::vector<Node> > d_currTerms;
  /** Common constants */
  Node d_zero;
  /** The write model */
  SequencesArraySolver d_sasolver;
  /** (TODO: eliminate this) equalities in the current context */
  NodeSet d_eqProc;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5

#endif
