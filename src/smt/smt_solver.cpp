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

#include "theory/theory_engine.h"
#include "prop/prop_engine.h"

namespace CVC4 {
namespace smt {

SmtSolver::SmtSolver(SmtEngine& smt, ResourceManager* rm, Preprocessor& pp, SmtEngineStatistics& stats) : d_smt(smt), d_state(state), d_rm(rm), d_pp(pp), d_stats(stats), d_theoryEngine(nullptr), d_propEngine(nullptr)
{
}

SmtSolver::~SmtSolver()
{
}

void SmtSolver::finishInit()
{
  // We have mutual dependency here, so we add the prop engine to the theory
  // engine later (it is non-essential there)
  d_theoryEngine.reset(new TheoryEngine(d_smt.getContext(),
                                        d_smt.getUserContext(),
                                        d_rm,
                                        d_smt.getTermFormulaRemover(),
                                        const_cast<const LogicInfo&>(d_smt.getLogicInfo())));

  // Add the theories
  for(TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST; ++id) {
    TheoryConstructor::addTheory(d_theoryEngine.get(), id);
    //register with proof engine if applicable
#ifdef CVC4_PROOF
    ProofManager::currentPM()->getTheoryProofEngine()->registerTheory(d_theoryEngine->theoryOf(id));
#endif
  }

  Trace("smt-debug") << "Making decision engine..." << std::endl;

  Trace("smt-debug") << "Making prop engine..." << std::endl;
  /* force destruction of referenced PropEngine to enforce that statistics
   * are unregistered by the obsolete PropEngine object before registered
   * again by the new PropEngine object */
  d_propEngine.reset(nullptr);
  d_propEngine.reset(new PropEngine(d_theoryEngine.get(),
                                    d_smt.getContext(),
                                    d_smt.getUserContext(),
                                    d_rm));

  Trace("smt-debug") << "Setting up theory engine..." << std::endl;
  d_theoryEngine->setPropEngine(getPropEngine());
  Trace("smt-debug") << "Finishing init for theory engine..." << std::endl;
  d_theoryEngine->finishInit();
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
}

void SmtSolver::interrupt()
{
  d_propEngine->interrupt();
  d_theoryEngine->interrupt();
}

void SmtSolver::cleanup()
{
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
                            const Node& assumption,
                            bool inUnsatCore,
                            bool isEntailmentCheck)
{
  return checkSatisfiability(as,
      node.isNull() ? std::vector<Node>() : std::vector<Node>{node},
      inUnsatCore,
      isEntailmentCheck);
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
  Result r = check();

  if ((options::solveRealAsInt() || options::solveIntAsBV() > 0)
      && r.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    r = Result(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
  }
  // flipped if we did a global negation
  if (as.isGlobalNegated())
  {
    Trace("smt") << "SmtEngine::process global negate " << r << std::endl;
    if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
    {
      r = Result(Result::SAT);
    }
    else if (r.asSatisfiabilityResult().isSat() == Result::SAT)
    {
      // only if satisfaction complete
      if (d_logic.isPure(THEORY_ARITH) || d_logic.isPure(THEORY_BV))
      {
        r = Result(Result::UNSAT);
      }
      else
      {
        r = Result(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
      }
    }
    Trace("smt") << "SmtEngine::global negate returned " << r << std::endl;
  }

  // notify our state of the check-sat result
  d_state.notifyCheckSatResult(hasAssumptions, r);

  return r;
}


Result SmtEngine::check(Assertions& as) 
{
  Assert(d_smt.isFullyInited());

  Trace("smt") << "SmtEngine::check()" << endl;

  const std::string& filename = d_state.getFilename();
  if (d_rm->out())
  {
    Result::UnknownExplanation why = d_rm->outOfResources()
                                         ? Result::RESOURCEOUT
                                         : Result::TIMEOUT;
    return Result(Result::ENTAILMENT_UNKNOWN, why, filename);
  }
  d_rm->beginCall();

  // Make sure the prop layer has all of the assertions
  Trace("smt") << "SmtEngine::check(): processing assertions" << endl;
  processAssertionsInternal(as);
  Trace("smt") << "SmtEngine::check(): done processing assertions" << endl;

  TimerStat::CodeTimer solveTimer(d_stats->d_solveTime);

  Chat() << "solving..." << endl;
  Trace("smt") << "SmtEngine::check(): running check" << endl;
  Result result = d_propEngine->checkSat();

  d_rm->endCall();
  Trace("limit") << "SmtEngine::check(): cumulative millis "
                 << d_rm->getTimeUsage() << ", resources "
                 << d_rm->getResourceUsage() << endl;

  return Result(result, d_state.getFilename());
}


void SmtEngine::processAssertionsInternal(Assertions& as)
{
  TimerStat::CodeTimer paTimer(d_stats->d_processAssertionsTime);
  d_rm->spendResource(ResourceManager::Resource::PreprocessStep);
  Assert(d_state.isFullyReady());

  AssertionPipeline& ap = as.getAssertionPipeline();

  if (ap.size() == 0)
  {
    // nothing to do
    return;
  }

  // process the assertions with the preprocessor
  bool noConflict = d_pp.process(*d_asserts);

  //notify theory engine new preprocessed assertions
  d_theoryEngine->notifyPreprocessedAssertions(ap.ref());

  // Push the formula to decision engine
  if (noConflict)
  {
    Chat() << "pushing to decision engine..." << endl;
    d_propEngine->addAssertionsToDecisionEngine(ap);
  }

  // end: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones

  d_pp.postprocess(*d_asserts);

  // Push the formula to SAT
  {
    Chat() << "converting to CNF..." << endl;
    TimerStat::CodeTimer codeTimer(d_stats->d_cnfConversionTime);
    for (const Node& assertion : ap.ref())
    {
      Chat() << "+ " << assertion << std::endl;
      d_propEngine->assertFormula(assertion);
    }
  }

  // clear the current assertions
  as.clearCurrent();
}

TheoryEngine* SmtSolver::getTheoryEngine() { return d_theoryEngine.get(); }

prop::PropEngine* SmtSolver::getPropEngine() { return d_propEngine.get(); }

}  // namespace smt
}  // namespace CVC4

