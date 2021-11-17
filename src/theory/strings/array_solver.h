/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
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

#ifndef CVC5__THEORY__STRINGS__ARRAY_SOLVER_H
#define CVC5__THEORY__STRINGS__ARRAY_SOLVER_H

#include "context/cdhashset.h"
#include "theory/strings/core_solver.h"
#include "theory/strings/extf_solver.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/solver_state.h"
#include "theory/strings/term_registry.h"

namespace cvc5 {
namespace theory {
namespace strings {

/**
 * This is a solver for reasoning about seq.update and seq.nth
 * natively. This class specifically addresses the combination of this
 * operators with concatenation. It relies on a subsolver for doing array
 * like reasoning (sequences_array_solver.h).
 */
class ArraySolver : protected EnvObj
{
  typedef context::CDHashSet<Node> NodeSet;

 public:
  ArraySolver(Env& env,
              SolverState& s,
              InferenceManager& im,
              TermRegistry& tr,
              CoreSolver& cs,
              ExtfSolver& es,
              ExtTheory& extt);
  ~ArraySolver();

  /**
   * Perform reasoning about seq.nth and seq.update operations, in particular,
   * their application to concatenation terms.
   */
  void checkArrayConcat();

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
  /** Equalities we have processed in the current context */
  NodeSet d_eqProc;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5

#endif
