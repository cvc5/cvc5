/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for find-synth queries.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__FIND_SYNTH_SOLVER_H
#define CVC5__SMT__FIND_SYNTH_SOLVER_H

#include "smt/env_obj.h"
#include "theory/quantifiers/sygus/synth_finder.h"

namespace cvc5::internal {
namespace smt {

/**
 * Find synthesis solver, which is responsible for implementing find-synth.
 * It initializes (possibly mulitiple) sygus enumerators and runs them in
 * an interleaved fashion until one returns a solution.
 */
class FindSynthSolver : protected EnvObj
{
 public:
  FindSynthSolver(Env& env);
  ~FindSynthSolver() {}
  /**
   * Find synth for the given target and (possibly multiple) grammars. Returns
   * the result of the find-synth query.
   */
  Node findSynth(modes::FindSynthTarget fst, const std::vector<TypeNode>& gtns);
  /**
   * Find synth next, which gets the next solution after a successful call to
   * findSynth above.
   */
  Node findSynthNext();

 private:
  /**
   * The synthesis finder utilities that are active. These are initialized
   * for each type node in gtns called by findSynth above.
   */
  std::vector<std::unique_ptr<theory::quantifiers::SynthFinder>> d_sfinders;
  /**  Current index in d_sfinders we are looking at.*/
  size_t d_currIndex;
  /** The current target we are given as input */
  modes::FindSynthTarget d_fst;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__FIND_SYNTH_SOLVER_H */
