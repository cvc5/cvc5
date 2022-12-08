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
    : EnvObj(env), d_smt(smt), d_ctx(ctx), d_ap(env)
{
  // set up proofs, this is done after options are finalized, so the
  // preprocess proof has been setup
  PreprocessProofGenerator* pppg =
      d_smt.getPreprocessor()->getPreprocessProofGenerator();
  if (pppg != nullptr)
  {
    d_ap.enableProofs(pppg);
  }
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
        // get the next assertions, store in d_ap
        getNextAssertionsInternal(d_ap);
        // check sat based on the driver strategy
        result = checkSatNext(d_ap);
        // if we were asked to check again
        if (result.getStatus() == Result::UNKNOWN
            && result.getUnknownExplanation() == REQUIRES_CHECK_AGAIN)
        {
          // finish init to construct new theory/prop engine
          d_smt.finishInit();
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

void SmtDriver::getNextAssertionsInternal(preprocessing::AssertionPipeline& ap)
{
  ap.clear();
  // must first refresh the assertions, in the case global declarations is true
  d_smt.getAssertions().refresh();
  // get the next assertions based on the implementation of this driver
  getNextAssertions(ap);
}

void SmtDriver::refreshAssertions()
{
  // get the next assertions, store in d_ap
  getNextAssertionsInternal(d_ap);
  // preprocess
  d_smt.preprocess(d_ap);
  // assert to internal
  d_smt.assertToInternal(d_ap);
}

void SmtDriver::notifyPushPre()
{
  // must preprocess the assertions and push them to the SAT solver, to make
  // the state accurate prior to pushing
  refreshAssertions();
}

void SmtDriver::notifyPushPost() { d_smt.pushPropContext(); }

void SmtDriver::notifyPopPre() { d_smt.popPropContext(); }

void SmtDriver::notifyPostSolve() { d_smt.postsolve(); }

SmtDriverSingleCall::SmtDriverSingleCall(Env& env, SmtSolver& smt)
    : SmtDriver(env, smt, nullptr), d_assertionListIndex(userContext(), 0)
{
}

Result SmtDriverSingleCall::checkSatNext(preprocessing::AssertionPipeline& ap)
{
  d_smt.preprocess(ap);
  d_smt.assertToInternal(ap);
  return d_smt.checkSatInternal();
}

void SmtDriverSingleCall::getNextAssertions(
    preprocessing::AssertionPipeline& ap)
{
  Assertions& as = d_smt.getAssertions();
  const context::CDList<Node>& al = as.getAssertionList();
  size_t alsize = al.size();
  for (size_t i = d_assertionListIndex.get(); i < alsize; ++i)
  {
    ap.push_back(al[i], true);
  }
  d_assertionListIndex = alsize;
}


}  // namespace smt
}  // namespace cvc5::internal
