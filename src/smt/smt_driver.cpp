/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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
#include "options/theory_options.h"
#include "prop/prop_engine.h"
#include "smt/context_manager.h"
#include "smt/env.h"
#include "smt/logic_exception.h"
#include "smt/smt_solver.h"
#include "theory/theory_engine.h"

namespace cvc5::internal {
namespace smt {

SmtDriver::SmtDriver(Env& env, SmtSolver& smt, ContextManager* ctx)
    : EnvObj(env),
      d_smt(smt),
      d_ctx(ctx),
      d_ap(env),
      d_illegalChecker(env),
      d_modelVerifier(env)
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
  bool hasAssumptions = !assumptions.empty();
  if (d_ctx)
  {
    d_ctx->notifyCheckSat(hasAssumptions);
  }
  Assertions& as = d_smt.getAssertions();
  Result result;
  try
  {
    // then, initialize the assertions
    as.setAssumptions(assumptions);

    // the assertions are now finalized, we call the illegal checker to
    // verify that any new assertions are legal
    d_illegalChecker.checkAssertions(as);

    // make the check, where notice smt engine should be fully inited by now

    Trace("smt") << "SmtSolver::check()" << std::endl;

    ResourceManager* rm = d_env.getResourceManager();
    // if we are already out of (cumulative) resources
    if (rm->out())
    {
      UnknownExplanation why = rm->outOfResources()
                                   ? UnknownExplanation::RESOURCEOUT
                                   : UnknownExplanation::TIMEOUT;
      result = Result(Result::UNKNOWN, why);
    }
    else
    {
      bool checkAgain = true;
      do
      {
        // get the next assertions, store in d_ap
        getNextAssertionsInternal(d_ap);
        // check sat based on the driver strategy
        result = checkSatNext(d_ap);
        // if we were asked to check again
        if (result.getStatus() == Result::UNKNOWN
            && result.getUnknownExplanation()
                   == UnknownExplanation::REQUIRES_CHECK_AGAIN)
        {
          // finish init to construct new theory/prop engine
          d_smt.finishInit();
        }
        else
        {
          checkAgain = false;
        }
      } while (checkAgain);
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
  // Check whether an unknown result can be strengthened to "sat", which is the
  // case if the candidate model can be verified to satisfy the input
  // assertions. Note this is done before the context is popped below, so that
  // the assumptions of this call are taken into account.
  if (options().smt.modelVerify)
  {
    if (result.getStatus() == Result::UNKNOWN && verifyUnknownModel(result))
    {
      Trace("smt") << "SmtDriver::checkSat: strengthen unknown to sat, based "
                      "on verifying the candidate model"
                   << std::endl;
      result = Result(Result::SAT);
    }
  }
  if (d_ctx)
  {
    d_ctx->notifyCheckSatResult(hasAssumptions);
  }
  return result;
}

bool SmtDriver::verifyUnknownModel(const Result& r)
{
  Assert(r.getStatus() == Result::UNKNOWN);
  // We require having a model, which additionally requires that functions are
  // assigned values.
  if (!options().smt.produceModels || !options().theory.assignFunctionValues)
  {
    return false;
  }
  // Do not attempt this if we were interrupted or ran out of resources, since
  // in this case the user asked us to stop spending resources on this query.
  UnknownExplanation uexp = r.getUnknownExplanation();
  if (uexp != UnknownExplanation::INCOMPLETE
      && uexp != UnknownExplanation::UNKNOWN_REASON
      && uexp != UnknownExplanation::OTHER)
  {
    return false;
  }
  // This is the candidate model that would be returned by a call to get-model
  // if we responded unknown for this query.
  theory::TheoryModel* m = d_smt.getTheoryEngine()->getModel();
  const context::CDList<Node>& al = d_smt.getAssertions().getAssertionList();
  // We disable the resource manager while verifying the model, similar to what
  // is done when building or getting models.
  ResourceManager* rm = d_env.getResourceManager();
  rm->setEnabled(false);
  bool ret = d_modelVerifier.verify(m, al);
  rm->setEnabled(true);
  return ret;
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

void SmtDriver::notifyPostSolve() { d_smt.resetTrail(); }

SmtDriverSingleCall::SmtDriverSingleCall(Env& env,
                                         SmtSolver& smt,
                                         ContextManager* ctx)
    : SmtDriver(env, smt, ctx), d_assertionListIndex(userContext(), 0)
{
}

Result SmtDriverSingleCall::checkSatNext(preprocessing::AssertionPipeline& ap)
{
  // preprocess
  d_smt.preprocess(ap);

  if (options().base.preprocessOnly)
  {
    return Result(Result::UNKNOWN, UnknownExplanation::REQUIRES_FULL_CHECK);
  }

  // assert to internal
  d_smt.assertToInternal(ap);
  // get result
  Result result = d_smt.checkSatInternal();
  // handle preprocessing-specific modifications to result
  if (ap.isNegated())
  {
    Trace("smt") << "SmtSolver::process global negate " << result << std::endl;
    if (result.getStatus() == Result::UNSAT)
    {
      result = Result(Result::SAT);
    }
    else if (result.getStatus() == Result::SAT)
    {
      // Only can answer unsat if the theory is satisfaction complete. In
      // other words, a "sat" result for a closed formula indicates that the
      // formula is true in *all* models.
      // This includes linear arithmetic and bitvectors, which are the primary
      // targets for the global negate option. Other logics are possible
      // here but not considered.
      LogicInfo logic = logicInfo();
      if ((logic.isPure(theory::THEORY_ARITH) && logic.isLinear())
          || logic.isPure(theory::THEORY_BV))
      {
        result = Result(Result::UNSAT);
      }
      else
      {
        result = Result(Result::UNKNOWN, UnknownExplanation::UNKNOWN_REASON);
      }
    }
    Trace("smt") << "SmtSolver::global negate returned " << result << std::endl;
  }
  return result;
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
