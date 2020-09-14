/*********************                                                        */
/*! \file smt_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The solver for SMT queries in an SmtEngine.
 **/

#include "smt/smt_solver.h"

#include "prop/prop_engine.h"
#include "smt/assertions.h"
#include "smt/preprocessor.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_state.h"
#include "theory/theory_engine.h"
#include "theory/theory_traits.h"

namespace CVC4 {
namespace smt {

SmtSolver::SmtSolver(SmtEngine& smt,
                     SmtEngineState& state,
                     ResourceManager* rm,
                     Preprocessor& pp,
                     SmtEngineStatistics& stats)
    : d_smt(smt),
      d_state(state),
      d_rm(rm),
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
  d_theoryEngine.reset(new TheoryEngine(d_smt.getContext(),
                                        d_smt.getUserContext(),
                                        d_rm,
                                        d_pp.getTermFormulaRemover(),
                                        logicInfo));

  // Add the theories
  for (theory::TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST;
       ++id)
  {
    theory::TheoryConstructor::addTheory(d_theoryEngine.get(), id);
  }

  Trace("smt-debug") << "Making prop engine..." << std::endl;
  /* force destruction of referenced PropEngine to enforce that statistics
   * are unregistered by the obsolete PropEngine object before registered
   * again by the new PropEngine object */
  d_propEngine.reset(nullptr);
  d_propEngine.reset(new PropEngine(
      d_theoryEngine.get(), d_smt.getContext(), d_smt.getUserContext(), d_rm));

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
  d_propEngine.reset(new PropEngine(
      d_theoryEngine.get(), d_smt.getContext(), d_smt.getUserContext(), d_rm));
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
  if (d_rm->out())
  {
    Result::UnknownExplanation why =
        d_rm->outOfResources() ? Result::RESOURCEOUT : Result::TIMEOUT;
    return Result(Result::ENTAILMENT_UNKNOWN, why, filename);
  }
  d_rm->beginCall();

  // Make sure the prop layer has all of the assertions
  Trace("smt") << "SmtSolver::check(): processing assertions" << endl;
  processAssertions(as);
  Trace("smt") << "SmtSolver::check(): done processing assertions" << endl;

  TimerStat::CodeTimer solveTimer(d_stats.d_solveTime);

  Chat() << "solving..." << endl;
  Trace("smt") << "SmtSolver::check(): running check" << endl;
  Result result = d_propEngine->checkSat();

  d_rm->endCall();
  Trace("limit") << "SmtSolver::check(): cumulative millis "
                 << d_rm->getTimeUsage() << ", resources "
                 << d_rm->getResourceUsage() << endl;

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
      LogicInfo logic = d_smt.getLogicInfo();
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
  d_rm->spendResource(ResourceManager::Resource::PreprocessStep);
  Assert(d_state.isFullyReady());

  preprocessing::AssertionPipeline& ap = as.getAssertionPipeline();

  if (ap.size() == 0)
  {
    // nothing to do
    return;
  }

  // process the assertions with the preprocessor
  bool noConflict = d_pp.process(as);

  // notify theory engine new preprocessed assertions
  d_theoryEngine->notifyPreprocessedAssertions(ap.ref());

  // Push the formula to decision engine
  if (noConflict)
  {
    Chat() << "pushing to decision engine..." << endl;
    d_propEngine->addAssertionsToDecisionEngine(ap);
  }

  // end: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones

  d_pp.postprocess(as);

  // Push the formula to SAT
  {
    Chat() << "converting to CNF..." << endl;
    TimerStat::CodeTimer codeTimer(d_stats.d_cnfConversionTime);
    for (const Node& assertion : ap.ref())
    {
      Chat() << "+ " << assertion << std::endl;
      d_propEngine->assertFormula(assertion);
    }
  }

  // clear the current assertions
  as.clearCurrent();
}

void SmtSolver::setProofNodeManager(ProofNodeManager* pnm) { d_pnm = pnm; }

TheoryEngine* SmtSolver::getTheoryEngine() { return d_theoryEngine.get(); }

prop::PropEngine* SmtSolver::getPropEngine() { return d_propEngine.get(); }

}  // namespace smt
}  // namespace CVC4
