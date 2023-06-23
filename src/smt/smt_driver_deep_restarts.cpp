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
 * The solver for SMT queries in an SolverEngine.
 */

#include "smt/smt_driver_deep_restarts.h"

#include <cvc5/cvc5_types.h>

#include "options/base_options.h"
#include "prop/prop_engine.h"
#include "smt/env.h"
#include "smt/smt_solver.h"

namespace cvc5::internal {
namespace smt {

SmtDriverDeepRestarts::SmtDriverDeepRestarts(Env& env,
                                             SmtSolver& smt,
                                             ContextManager* ctx)
    : SmtDriver(env, smt, ctx), d_firstTime(true)
{
}

Result SmtDriverDeepRestarts::checkSatNext(preprocessing::AssertionPipeline& ap)
{
  d_zll.clear();
  d_smt.preprocess(ap);
  d_smt.assertToInternal(ap);
  Result result = d_smt.checkSatInternal();
  // check again if we didn't solve and there are learned literals
  if (result.getStatus() == Result::UNKNOWN)
  {
    // get the learned literals immediately
    d_zll = d_smt.getPropEngine()->getLearnedZeroLevelLiteralsForRestart();
    // check again if there are any
    if (!d_zll.empty())
    {
      return Result(Result::UNKNOWN, REQUIRES_CHECK_AGAIN);
    }
  }
  return result;
}

void SmtDriverDeepRestarts::getNextAssertions(
    preprocessing::AssertionPipeline& ap)
{
  if (d_firstTime)
  {
    // On the first time, we take all assertions. Notice that this driver
    // does not handle incremental mode yet, so we always take all assertions
    // here.
    Assertions& as = d_smt.getAssertions();
    const context::CDList<Node>& al = as.getAssertionList();
    for (const Node& a : al)
    {
      ap.push_back(a, true);
    }
    d_firstTime = false;
    return;
  }
  Trace("deep-restart") << "Have " << d_zll.size()
                        << " zero level learned literals" << std::endl;
  // Copy the preprocessed assertions and skolem map information directly
  const context::CDList<Node>& ppAssertions = d_smt.getPreprocessedAssertions();
  for (const Node& a : ppAssertions)
  {
    ap.push_back(a);
  }
  preprocessing::IteSkolemMap& ismr = ap.getIteSkolemMap();
  const context::CDHashMap<size_t, Node>& ppSkolemMap =
      d_smt.getPreprocessedSkolemMap();
  for (const auto& k : ppSkolemMap)
  {
    // carry the entire skolem map, which should align with the order of
    // assertions passed into the new assertions pipeline
    ismr[k.first] = k.second;
  }
  if (isOutputOn(OutputTag::DEEP_RESTART))
  {
    output(OutputTag::DEEP_RESTART) << "(deep-restart (";
    bool firstTime = true;
    for (TNode lit : d_zll)
    {
      output(OutputTag::DEEP_RESTART) << (firstTime ? "" : " ") << lit;
      firstTime = false;
    }
    output(OutputTag::DEEP_RESTART) << "))" << std::endl;
  }
  for (TNode lit : d_zll)
  {
    Trace("deep-restart-lit") << "Restart learned lit: " << lit << std::endl;
    ap.push_back(lit);
    if (Configuration::isAssertionBuild())
    {
      Assert(d_allLearnedLits.find(lit) == d_allLearnedLits.end())
          << "Relearned: " << lit << std::endl;
      d_allLearnedLits.insert(lit);
    }
  }
  Trace("deep-restart") << "Finished compute deep restart" << std::endl;
  // Note that the environment may contain top-level substitutions derived
  // on the previous check-sat. Since the context does not change, these
  // are preserved for the next check-sat, which ensures models involving
  // variables appearing in top-level substitutions are correct.
}

}  // namespace smt
}  // namespace cvc5::internal
