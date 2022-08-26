/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for SMT queries in an SolverEngine.
 */

#include "smt/smt_driver.h"

#include "options/base_options.h"
#include "options/main_options.h"
#include "options/smt_options.h"
#include "prop/prop_engine.h"
#include "smt/context_manager.h"
#include "smt/env.h"
#include "smt/logic_exception.h"
#include "smt/smt_solver.h"

namespace cvc5::internal {
namespace smt {

SmtDriver::SmtDriver(Env& env, SmtSolver& smt, ContextManager* ctx)
    : EnvObj(env), d_smt(smt), d_ctx(ctx)
{
}

Result SmtDriver::checkSat(const std::vector<Node>& assumptions)
{
  Assertions& as = d_smt.getAssertions();
  Result result;
  try
  {
    // then, initialize the assertions
    as.setAssumptions(assumptions);

    // make the check, where notice smt engine should be fully inited by now

    Trace("smt") << "SmtSolver::check()" << std::endl;

    ResourceManager* rm = d_env.getResourceManager();
    if (rm->out())
    {
      UnknownExplanation why = rm->outOfResources()
                                   ? UnknownExplanation::RESOURCEOUT
                                   : UnknownExplanation::TIMEOUT;
      result = Result(Result::UNKNOWN, why);
    }
    else
    {
      rm->beginCall();

      bool checkAgain = true;
      while (checkAgain)
      {
        checkAgain = false;
        // check sat based on the driver strategy
        result = checkSatNext(checkAgain);
        // if we were asked to check again
        if (checkAgain)
        {
          Assert(d_ctx != nullptr);
          as.clearCurrent();
          d_ctx->notifyResetAssertions();
          // get the next assertions based on the driver strategy
          getNextAssertions(as);
          // finish init to construct new theory/prop engine
          d_smt.finishInit();
          // setup
          d_ctx->setup();
        }
      }

      rm->endCall();
      Trace("limit") << "SmtSolver::check(): cumulative millis "
                     << rm->getTimeUsage() << ", resources "
                     << rm->getResourceUsage() << std::endl;
    }
  }
  catch (const LogicException& e)
  {
    // The exception may have been throw during solving, backtrack to reset the
    // decision level to the level expected after this method finishes
    d_smt.getPropEngine()->resetTrail();
    throw;
  }

  return result;
}

SmtDriverSingleCall::SmtDriverSingleCall(Env& env, SmtSolver& smt)
    : SmtDriver(env, smt, nullptr)
{
}

Result SmtDriverSingleCall::checkSatNext(bool& checkAgain)
{
  Assertions& as = d_smt.getAssertions();
  d_smt.preprocess(as);
  d_smt.assertToInternal(as);
  Result result = d_smt.checkSatInternal();
  return result;
}

void SmtDriverSingleCall::getNextAssertions(Assertions& as) { Unreachable(); }

}  // namespace smt
}  // namespace cvc5::internal
