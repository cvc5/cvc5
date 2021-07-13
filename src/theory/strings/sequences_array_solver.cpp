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

#include "theory/strings/sequences_array_solver.h"

#include "util/rational.h"
#include "theory/strings/theory_strings_utils.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace strings {

SequencesArraySolver::SequencesArraySolver(SolverState& s,
                                             InferenceManager& im,
                                             TermRegistry& tr,
                                             ExtfSolver& es)
    : d_state(s), d_im(im), d_termReg(tr), d_esolver(es)
{
}

SequencesArraySolver::~SequencesArraySolver() {}

void SequencesArraySolver::check(const std::vector<Node>& nthTerms,
             const std::vector<Node>& updateTerms)
{
  Trace("seq-update") << "SequencesArraySolver::check..." << std::endl;
  d_writeModel.clear();
  for (const Node& n : nthTerms)
  {
    Node r = d_state.getRepresentative(n[0]);
    Trace("seq-update") << "- " << r << ": " << n[1] << " -> " << n << std::endl;
    d_writeModel[r][n[1]] = n;
  }
}

const std::map<Node, Node>& SequencesArraySolver::getWriteModel(Node eqc)
{
  return d_writeModel[eqc];
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5
