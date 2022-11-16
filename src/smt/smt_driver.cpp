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
      do
      {
        // check sat based on the driver strategy
        result = checkSatNext();
        // if we were asked to check again
        if (result.getStatus() == Result::UNKNOWN
            && result.getUnknownExplanation() == REQUIRES_CHECK_AGAIN)
        {
          Assert(d_ctx != nullptr);
          as.getAssertionPipeline().clear();
          d_ctx->notifyResetAssertions();
          // get the next assertions based on the driver strategy
          getNextAssertions(as);
          // finish init to construct new theory/prop engine
          d_smt.finishInit();
          // setup
          d_ctx->setup(this);
        }
        else
        {
          checkAgain = false;
        }
      } while (checkAgain);

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
  catch (const TypeCheckingExceptionPrivate& e)
  {
    // The exception has been throw during solving, backtrack to reset the
    // decision level to the level expected after this method finishes. Note
    // that we do not expect type checking exceptions to occur during solving.
    // However, if they occur due to a bug, we don't want to additionally cause
    // an assertion failure.
    d_smt.getPropEngine()->resetTrail();
    throw;
  }

  return result;
}

void SmtDriver::refreshAssertions()
{
  d_smt.refreshAssertions();
}

void SmtDriver::notifyPushPre()
{
  // must preprocess the assertions and push them to the SAT solver, to make
  // the state accurate prior to pushing
  d_smt.refreshAssertions();
}

void SmtDriver::notifyPushPost() { d_smt.pushPropContext(); }

void SmtDriver::notifyPopPre() { d_smt.popPropContext(); }

void SmtDriver::notifyPostSolve() { d_smt.postsolve(); }

SmtDriverSingleCall::SmtDriverSingleCall(Env& env, SmtSolver& smt)
    : SmtDriver(env, smt, nullptr)
{
}

Result SmtDriverSingleCall::checkSatNext()
{
  preprocessing::AssertionPipeline& ap =
      d_smt.getAssertions().getAssertionPipeline();
  d_smt.preprocess(ap);
  d_smt.assertToInternal(ap);
  return d_smt.checkSatInternal();
}

void SmtDriverSingleCall::getNextAssertions(Assertions& as) { Unreachable(); }


}  // namespace smt
}  // namespace cvc5::internal
