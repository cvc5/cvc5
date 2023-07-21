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

#include "smt/find_synth_solver.h"

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/candidate_rewrite_database.h"
#include "theory/quantifiers/query_generator.h"
#include "theory/quantifiers/rewrite_verifier.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace cvc5::internal {
namespace smt {

FindSynthSolver::FindSynthSolver(Env& env) : EnvObj(env) {}

Node FindSynthSolver::findSynth(modes::FindSynthTarget fst,
                                const std::vector<TypeNode>& gtns)
{
  d_fst = fst;
  // initialize the synthesis finders
  d_sfinders.clear();
  for (const TypeNode& gtn : gtns)
  {
    d_sfinders.emplace_back(new theory::quantifiers::SynthFinder(d_env));
    d_sfinders.back()->initialize(fst, gtn);
  }
  d_currIndex = 0;
  return findSynthNext();
}

Node FindSynthSolver::findSynthNext()
{
  // cycle through each until one returns a solution
  Node ret;
  std::vector<size_t> toErase;
  while (!d_sfinders.empty())
  {
    Assert(d_currIndex < d_sfinders.size());
    for (size_t i = d_currIndex, nfinders = d_sfinders.size(); i < nfinders;
         i++)
    {
      theory::quantifiers::SynthFinder* curr = d_sfinders[i].get();
      if (!curr->increment())
      {
        toErase.push_back(i - toErase.size());
        continue;
      }
      ret = curr->getCurrent();
      if (!ret.isNull())
      {
        // found a return
        d_currIndex = i - toErase.size();
        break;
      }
    }
    for (size_t i : toErase)
    {
      d_sfinders.erase(d_sfinders.begin() + i);
    }
    // if we terminated
    if (!ret.isNull())
    {
      if (d_currIndex >= d_sfinders.size())
      {
        d_currIndex = 0;
      }
      if (options().quantifiers.sygusStream)
      {
        std::ostream& out = options().base.out;
        out << "(" << d_fst << " " << ret << ")" << std::endl;
      }
      else
      {
        return ret;
      }
    }
  }
  return Node::null();
}

}  // namespace smt
}  // namespace cvc5::internal
