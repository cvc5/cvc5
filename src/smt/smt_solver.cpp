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
 * The solver for SMT queries in an SmtEngine.
 */

#include "smt/smt_solver.h"

#include "options/smt_options.h"
#include "prop/prop_engine.h"
#include "smt/assertions.h"
#include "smt/env.h"
#include "smt/preprocessor.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_state.h"
#include "smt/smt_engine_stats.h"
#include "theory/logic_info.h"
#include "theory/theory_engine.h"
#include "theory/theory_traits.h"

using namespace std;

namespace cvc5 {
namespace smt {

SmtSolver::SmtSolver(SmtEngine& smt,
                     Env& env,
                     SmtEngineState& state,
                     Preprocessor& pp,
                     SmtEngineStatistics& stats)
    : d_smt(smt),
      d_env(env),
      d_state(state),
      d_pp(pp),
      d_stats(stats),
      d_pnm(nullptr),
      d_theoryEngine(nullptr),
      d_propEngine(nullptr)
{
}

SmtSolver::~SmtSolver() {}

void SmtSolver::finishInit(const LogicInfo& logicInfo)
{
  // We have mutual dependency here, so we add the prop engine to the theory
  // engine later (it is non-essential there)
  d_theoryEngine.reset(new TheoryEngine(
      d_env,
      d_smt.getOutputManager(),
      // Other than whether d_pm is set, theory engine proofs are conditioned on
      // the relationshup between proofs and unsat cores: the unsat cores are in
      // FULL_PROOF mode, no proofs are generated on theory engine.
      (options::unsatCores()
       && options::unsatCoresMode() != options::UnsatCoresMode::FULL_PROOF)
          ? nullptr
          : d_pnm));

  // Add the theories
  for (theory::TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST;
       ++id)
  {
    theory::TheoryConstructor::addTheory(d_theoryEngine.get(), id);
  }
  // Add the proof checkers for each theory
  if (d_pnm)
  {
    d_theoryEngine->initializeProofChecker(d_pnm->getChecker());
  }
  Trace("smt-debug") << "Making prop engine..." << std::endl;
  /* force destruction of referenced PropEngine to enforce that statistics
   * are unregistered by the obsolete PropEngine object before registered
   * again by the new PropEngine object */
  d_propEngine.reset(nullptr);
  d_propEngine.reset(new prop::PropEngine(
      d_theoryEngine.get(), d_env, d_smt.getOutputManager(), d_pnm));

  Trace("smt-debug") << "Setting up theory engine..." << std::endl;
  d_theoryEngine->setPropEngine(getPropEngine());
  Trace("smt-debug") << "Finishing init for theory engine..." << std::endl;
  d_theoryEngine->finishInit();
  d_propEngine->finishInit();
}

void SmtSolver::resetAssertions()
{
  /* Create new PropEngine.
   * First force destruction of referenced PropEngine to enforce that
   * statistics are unregistered by the obsolete PropEngine object before
   * registered again by the new PropEngine object */
  d_propEngine.reset(nullptr);
  d_propEngine.reset(new prop::PropEngine(
      d_theoryEngine.get(), d_env, d_smt.getOutputManager(), d_pnm));
  d_theoryEngine->setPropEngine(getPropEngine());
  // Notice that we do not reset TheoryEngine, nor does it require calling
  // finishInit again. In particular, TheoryEngine::finishInit does not
  // depend on knowing the associated PropEngine.
  d_propEngine->finishInit();
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

void SmtSolver::shutdown()
{
  if (d_propEngine != nullptr)
  {
    d_propEngine->shutdown();
  }
  if (d_theoryEngine != nullptr)
  {
    d_theoryEngine->shutdown();
  }
}

Result SmtSolver::checkSatisfiability(Assertions& as,
                                      const std::vector<Node>& assumptions,
                                      bool inUnsatCore,
                                      bool isEntailmentCheck)
{
  // update the state to indicate we are about to run a check-sat
  bool hasAssumptions = !assumptions.empty();
  d_state.notifyCheckSat(hasAssumptions);

  // then, initialize the assertions
  as.initializeCheckSat(assumptions, inUnsatCore, isEntailmentCheck);

  // make the check
  Assert(d_smt.isFullyInited());

  Trace("smt") << "SmtSolver::check()" << endl;

  const std::string& filename = d_state.getFilename();
  ResourceManager* rm = d_env.getResourceManager();
  if (rm->out())
  {
    Result::UnknownExplanation why =
        rm->outOfResources() ? Result::RESOURCEOUT : Result::TIMEOUT;
    return Result(Result::ENTAILMENT_UNKNOWN, why, filename);
  }
  rm->beginCall();

  // Make sure the prop layer has all of the assertions
  Trace("smt") << "SmtSolver::check(): processing assertions" << endl;
  processAssertions(as);
  Trace("smt") << "SmtSolver::check(): done processing assertions" << endl;

  TimerStat::CodeTimer solveTimer(d_stats.d_solveTime);

  Chat() << "solving..." << endl;
  Trace("smt") << "SmtSolver::check(): running check" << endl;
  Result result = d_propEngine->checkSat();

  rm->endCall();
  Trace("limit") << "SmtSolver::check(): cumulative millis "
                 << rm->getTimeUsage() << ", resources "
                 << rm->getResourceUsage() << endl;

  if ((options::solveRealAsInt() || options::solveIntAsBV() > 0)
      && result.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    result = Result(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
  }
  // flipped if we did a global negation
  if (as.isGlobalNegated())
  {
    Trace("smt") << "SmtSolver::process global negate " << result << std::endl;
    if (result.asSatisfiabilityResult().isSat() == Result::UNSAT)
    {
      result = Result(Result::SAT);
    }
    else if (result.asSatisfiabilityResult().isSat() == Result::SAT)
    {
      // Only can answer unsat if the theory is satisfaction complete. This
      // includes linear arithmetic and bitvectors, which are the primary
      // targets for the global negate option. Other logics are possible here
      // but not considered.
      LogicInfo logic = d_env.getLogicInfo();
      if ((logic.isPure(theory::THEORY_ARITH) && logic.isLinear()) ||
          logic.isPure(theory::THEORY_BV))
      {
        result = Result(Result::UNSAT);
      }
      else
      {
        result = Result(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
      }
    }
    Trace("smt") << "SmtSolver::global negate returned " << result << std::endl;
  }

  // set the filename on the result
  Result r = Result(result, filename);

  // notify our state of the check-sat result
  d_state.notifyCheckSatResult(hasAssumptions, r);

  return r;
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
    Chat() << "converting to CNF..." << endl;
    const std::vector<Node>& assertions = ap.ref();
    // It is important to distinguish the input assertions from the skolem
    // definitions, as the decision justification heuristic treates the latter
    // specially.
    preprocessing::IteSkolemMap& ism = ap.getIteSkolemMap();
    d_propEngine->assertInputFormulas(assertions, ism);
  }

  // clear the current assertions
  as.clearCurrent();
}

void SmtSolver::setProofNodeManager(ProofNodeManager* pnm) { d_pnm = pnm; }

TheoryEngine* SmtSolver::getTheoryEngine() { return d_theoryEngine.get(); }

prop::PropEngine* SmtSolver::getPropEngine() { return d_propEngine.get(); }

theory::QuantifiersEngine* SmtSolver::getQuantifiersEngine()
{
  Assert(d_theoryEngine != nullptr);
  return d_theoryEngine->getQuantifiersEngine();
}

Preprocessor* SmtSolver::getPreprocessor() { return &d_pp; }

}  // namespace smt
}  // namespace cvc5
