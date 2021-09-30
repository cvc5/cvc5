/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of query cache
 */

#include "theory/quantifiers/query_cache.h"

#include "options/smt_options.h"
#include "smt/env.h"
#include "theory/smt_engine_subsolver.h"

using namespace std;
using namespace cvc5::kind;
using namespace cvc5::context;

namespace cvc5 {
namespace theory {
namespace quantifiers {

QueryCache::QueryCache(Env& env, bool checkUnsat, const Options* optr)
    : ExprMiner(env), d_checkUnsat(checkUnsat), d_sampler(env)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  if (optr != nullptr)
  {
    d_subOptions.copyValues(*optr);
  }
  // disable proofs no matter what
  d_subOptions.smt.produceProofs = false;
  d_subOptions.smt.checkProofs = false;
  d_subOptions.smt.unsatCores = false;
  d_subOptions.smt.checkUnsatCores = false;
}

void QueryCache::initialize(const std::vector<Node>& vars, SygusSampler* ss)
{
  NodeManager* nm = NodeManager::currentNM();
  TypeNode boolType = nm->booleanType();
  d_sampler.initialize(boolType, vars, 0);
}

bool QueryCache::addTerm(Node sol, std::ostream& out) { return false; }

bool QueryCache::addTerm(Node sol)
{
  bool isSat = false;
  sol = extendedRewrite(sol);
  if (sol.isConst())
  {
    isSat = sol.getConst<bool>();
  }
  else
  {
    // FIXME
    return false;
    size_t npoints = d_sampler.getNumSamplePoints();
    for (size_t i = 0; i < npoints; i++)
    {
      Node ev = d_sampler.evaluate(sol, i);
      if (ev == d_true)
      {
        // already satisfied by a point
        isSat = true;
        break;
      }
    }
    if (!isSat)
    {
      sol = convertToSkolem(sol);
      std::vector<Node> modelVals;
      Result r = checkWithSubsolver(
          sol, d_skolems, modelVals, d_subOptions, d_env.getLogicInfo());
      if (r.asSatisfiabilityResult().isSat() != Result::UNSAT)
      {
        // check the sample point
        d_sampler.addSamplePoint(modelVals);
        if (r.asSatisfiabilityResult().isSat() == Result::SAT_UNKNOWN)
        {
          // always a failure if unknown
          return false;
        }
        isSat = true;
      }
    }
  }
  return isSat != d_checkUnsat;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
