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

#include "theory/strings/sequences_update_solver.h"

namespace cvc5 {
namespace theory {
namespace strings {

SequencesUpdateSolver::SequencesUpdateSolver(SolverState& s,
                                             InferenceManager& im,
                                             TermRegistry& tr,
                                             CoreSolver& cs)
    : d_state(s), d_im(im), d_termReg(tr), d_csolver(cs)
{
}

SequencesUpdateSolver::~SequencesUpdateSolver() {}

void SequencesUpdateSolver::check()
{
  if (!d_termReg.hasSeqUpdate())
  {
    Trace("seq-update") << "No seq.update/seq.nth terms, skipping check..."
                        << std::endl;
    return;
  }

  Trace("seq-update") << "check..." << std::endl;

  // Inferences:
  //
  // n=0 => (seq.update (seq.unit m) n z) = z
  //
  // z = (seq.update (seq.++ x y) n 1) => z = (seq.update x n 1)  ++ (seq.update
  // y (n - len(x)) 1)
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5
