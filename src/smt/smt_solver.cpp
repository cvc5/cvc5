/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for SMT queries in an SolverEngine.
 */

#include "smt/smt_solver.h"

#include "options/main_options.h"
#include "options/smt_options.h"
#include "prop/prop_engine.h"
#include "smt/assertions.h"
#include "smt/env.h"
#include "smt/logic_exception.h"
#include "smt/preprocessor.h"
#include "smt/solver_engine.h"
#include "smt/solver_engine_state.h"
#include "smt/solver_engine_stats.h"
#include "theory/logic_info.h"
#include "theory/theory_engine.h"
#include "theory/theory_traits.h"

using namespace std;

namespace cvc5::internal {
namespace smt {

SmtSolver::SmtSolver(Env& env,
                     SolverEngineState& state,
                     AbstractValues& abs,
                     SolverEngineStatistics& stats)
    : d_env(env),
      d_state(state),
      d_pp(env, abs, stats),
      d_stats(stats),
      d_theoryEngine(nullptr),
      d_propEngine(nullptr)
{
}

SmtSolver::~SmtSolver() {}

void SmtSolver::finishInit()
{
  // We have mutual dependency here, so we add the prop engine to the theory
  // engine later (it is non-essential there)
  d_theoryEngine.reset(new TheoryEngine(d_env));

  // Add the theories
  for (theory::TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST;
       ++id)
  {
    theory::TheoryConstructor::addTheory(d_theoryEngine.get(), id);
  }
  // Add the proof checkers for each theory
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  if (pnm)
  {
    d_theoryEngine->initializeProofChecker(pnm->getChecker());
  }
  Trace("smt-debug") << "Making prop engine..." << std::endl;
  /* force destruction of referenced PropEngine to enforce that statistics
   * are unregistered by the obsolete PropEngine object before registered
   * again by the new PropEngine object */
  d_propEngine.reset(nullptr);
  d_propEngine.reset(new prop::PropEngine(d_env, d_theoryEngine.get()));

  Trace("smt-debug") << "Setting up theory engine..." << std::endl;
  d_theoryEngine->setPropEngine(getPropEngine());
  Trace("smt-debug") << "Finishing init for theory engine..." << std::endl;
  d_theoryEngine->finishInit();
  d_propEngine->finishInit();

  d_pp.finishInit(d_theoryEngine.get(), d_propEngine.get());
}

void SmtSolver::resetAssertions()
{
  /* Create new PropEngine.
   * First force destruction of referenced PropEngine to enforce that
   * statistics are unregistered by the obsolete PropEngine object before
   * registered again by the new PropEngine object */
  d_propEngine.reset(nullptr);
  d_propEngine.reset(new prop::PropEngine(d_env, d_theoryEngine.get()));
  d_theoryEngine->setPropEngine(getPropEngine());
  // Notice that we do not reset TheoryEngine, nor does it require calling
  // finishInit again. In particular, TheoryEngine::finishInit does not
  // depend on knowing the associated PropEngine.
  d_propEngine->finishInit();
  // must reset the preprocessor as well
  d_pp.finishInit(d_theoryEngine.get(), d_propEngine.get());
}

void SmtSolver::interrupt()
{
  if (d_propEngine != nullptr)
  {
    d_propEngine->interrupt();
  }
  if (d_theoryEngine != nullptr)
  {
    d_theoryEngine->interrupt();
  }
}

Result SmtSolver::checkSatisfiability(Assertions& as,
                                      const std::vector<Node>& assumptions)
{
  Result result;

  bool hasAssumptions = !assumptions.empty();

  try
  {
    // update the state to indicate we are about to run a check-sat
    d_state.notifyCheckSat(hasAssumptions);

    // then, initialize the assertions
    as.initializeCheckSat(assumptions);

    // make the check, where notice smt engine should be fully inited by now

    Trace("smt") << "SmtSolver::check()" << endl;

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

      // Make sure the prop layer has all of the assertions
      Trace("smt") << "SmtSolver::check(): processing assertions" << endl;
      processAssertions(as);
      Trace("smt") << "SmtSolver::check(): done processing assertions" << endl;

      TimerStat::CodeTimer solveTimer(d_stats.d_solveTime);

      d_env.verbose(2) << "solving..." << std::endl;
      Trace("smt") << "SmtSolver::check(): running check" << endl;
      result = d_propEngine->checkSat();
      Trace("smt") << "SmtSolver::check(): result " << result << std::endl;

      rm->endCall();
      Trace("limit") << "SmtSolver::check(): cumulative millis "
                     << rm->getTimeUsage() << ", resources "
                     << rm->getResourceUsage() << endl;

      if ((d_env.getOptions().smt.solveRealAsInt
           || d_env.getOptions().smt.solveIntAsBV > 0)
          && result.getStatus() == Result::UNSAT)
      {
        result = Result(Result::UNKNOWN, UnknownExplanation::UNKNOWN_REASON);
      }
      // flipped if we did a global negation
      if (as.isGlobalNegated())
      {
        Trace("smt") << "SmtSolver::process global negate " << result
                     << std::endl;
        if (result.getStatus() == Result::UNSAT)
        {
          result = Result(Result::SAT);
        }
        else if (result.getStatus() == Result::SAT)
        {
          // Only can answer unsat if the theory is satisfaction complete. This
          // includes linear arithmetic and bitvectors, which are the primary
          // targets for the global negate option. Other logics are possible
          // here but not considered.
          LogicInfo logic = d_env.getLogicInfo();
          if ((logic.isPure(theory::THEORY_ARITH) && logic.isLinear())
              || logic.isPure(theory::THEORY_BV))
          {
            result = Result(Result::UNSAT);
          }
          else
          {
            result =
                Result(Result::UNKNOWN, UnknownExplanation::UNKNOWN_REASON);
          }
        }
        Trace("smt") << "SmtSolver::global negate returned " << result
                     << std::endl;
      }
    }
  }
  catch (const LogicException& e)
  {
    // The exception may have been throw during solving, backtrack to reset the
    // decision level to the level expected after this method finishes
    getPropEngine()->resetTrail();
    throw;
  }

  // set the filename on the result
  const std::string& filename = d_env.getOptions().driver.filename;
  result = Result(result, filename);

  // notify our state of the check-sat result
  d_state.notifyCheckSatResult(hasAssumptions, result);

  return result;
}

void SmtSolver::processAssertions(Assertions& as)
{
  TimerStat::CodeTimer paTimer(d_stats.d_processAssertionsTime);
  d_env.getResourceManager()->spendResource(Resource::PreprocessStep);
  Assert(d_state.isFullyReady());

  preprocessing::AssertionPipeline& ap = as.getAssertionPipeline();

  if (ap.size() == 0)
  {
    // nothing to do
    return;
  }

  // process the assertions with the preprocessor
  d_pp.process(as);

  // end: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones

  // Push the formula to SAT
  {
    d_env.verbose(2) << "converting to CNF..." << endl;
    const std::vector<Node>& assertions = ap.ref();
    // It is important to distinguish the input assertions from the skolem
    // definitions, as the decision justification heuristic treates the latter
    // specially. Note that we don't pass the preprocess learned literals
    // d_pp.getLearnedLiterals() here, since they may not exactly correspond
    // to the actual preprocessed learned literals, as the input may have
    // undergone further preprocessing.
    preprocessing::IteSkolemMap& ism = ap.getIteSkolemMap();
    d_propEngine->assertInputFormulas(assertions, ism);
  }

  // clear the current assertions
  as.clearCurrent();
}

TheoryEngine* SmtSolver::getTheoryEngine() { return d_theoryEngine.get(); }

prop::PropEngine* SmtSolver::getPropEngine() { return d_propEngine.get(); }

theory::QuantifiersEngine* SmtSolver::getQuantifiersEngine()
{
  Assert(d_theoryEngine != nullptr);
  return d_theoryEngine->getQuantifiersEngine();
}

Preprocessor* SmtSolver::getPreprocessor() { return &d_pp; }

}  // namespace smt
}  // namespace cvc5::internal
