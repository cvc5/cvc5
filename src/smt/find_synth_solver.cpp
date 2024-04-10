/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for find-synth queries.
 */

#include "smt/find_synth_solver.h"

#include "expr/sygus_term_enumerator.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/candidate_rewrite_database.h"
#include "theory/quantifiers/query_generator.h"
#include "theory/quantifiers/rewrite_verifier.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus_sampler.h"
#include "util/resource_manager.h"

namespace cvc5::internal {
namespace smt {

FindSynthSolver::FindSynthSolver(Env& env) : EnvObj(env) {}

Node FindSynthSolver::findSynth(modes::FindSynthTarget fst,
                                const std::vector<TypeNode>& gtns)
{
  d_fst = fst;
  // initialize the synthesis finders
  d_sfinders.clear();
  d_finished.clear();
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
  ResourceManager* rm = resourceManager();
  while (d_finished.size() < d_sfinders.size() && !rm->out())
  {
    rm->spendResource(Resource::FindSynthStep);
    if (d_currIndex == d_sfinders.size())
    {
      d_currIndex = 0;
    }
    if (d_finished.find(d_currIndex) == d_finished.end())
    {
      theory::quantifiers::SynthFinder* curr = d_sfinders[d_currIndex].get();
      ret = curr->getCurrent();
      if (!curr->increment())
      {
        d_finished.insert(d_currIndex);
      }
    }
    d_currIndex++;
    // if we terminated
    if (!ret.isNull())
    {
      if (options().quantifiers.sygusStream)
      {
        std::ostream& out = options().base.out;
        out << "(" << d_fst << " " << ret << ")" << std::endl;
        ret = Node::null();
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
