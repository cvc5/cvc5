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

namespace CVC4 {
namespace smt {

SmtSolver::SmtSolver(SmtEngine& smt, ResourceManager* rm, Preprocessor& pp, SmtEngineStatistics& stats) : d_smt(smt), d_rm(rm), d_pp(pp), d_stats(stats), d_theoryEngine(nullptr), d_propEngine(nullptr)
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

void SmtSolver::push()
{
  d_propEngine->push();
}

void SmtSolver::pop()
{
  d_propEngine->pop();
}

void SmtSolver::processAssertions(Assertions& as)
{
  // process the assertions with the preprocessor
  bool noConflict = d_pp->process(*d_asserts);

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

  d_pp->postprocess(*d_asserts);

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
  d_asserts->clearCurrent();
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

  try
  {
    SmtScope smts(this);
    finalOptionsAreSet();
    doPendingPops();

    Trace("smt") << "SmtEngine::"
                 << (isEntailmentCheck ? "checkEntailed" : "checkSat") << "("
                 << assumptions << ")" << endl;

    if(d_queryMade && !options::incrementalSolving()) {
      throw ModalException("Cannot make multiple queries unless "
                           "incremental solving is enabled "
                           "(try --incremental)");
    }

    // Note that a query has been made and we are in assert mode
    d_queryMade = true;
    d_smtMode = SMT_MODE_ASSERT;

    // push if there are assumptions
    bool didInternalPush = false;
    if (!assumptions.empty())
    {
      internalPush();
      didInternalPush = true;
    }

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

    d_needPostsolve = true;

    // Pop the context
    if (didInternalPush)
    {
      internalPop();
    }

    // Remember the status
    d_status = r;
    // Check against expected status
    if (!d_expectedStatus.isUnknown() && !d_status.isUnknown()
        && d_status != d_expectedStatus)
    {
      CVC4_FATAL() << "Expected result " << d_expectedStatus << " but got "
                   << d_status;
    }
    d_expectedStatus = Result();
    // Update the SMT mode
    if (d_status.asSatisfiabilityResult().isSat() == Result::UNSAT)
    {
      d_smtMode = SMT_MODE_UNSAT;
    }
    else if (d_status.asSatisfiabilityResult().isSat() == Result::SAT)
    {
      d_smtMode = SMT_MODE_SAT;
    }
    else
    {
      d_smtMode = SMT_MODE_SAT_UNKNOWN;
    }

    Trace("smt") << "SmtEngine::" << (isEntailmentCheck ? "query" : "checkSat")
                 << "(" << assumptions << ") => " << r << endl;

    // Check that SAT results generate a model correctly.
    if(options::checkModels()) {
      if (r.asSatisfiabilityResult().isSat() == Result::SAT)
      {
        checkModel();
      }
    }
    // Check that UNSAT results generate a proof correctly.
    if(options::checkProofs()) {
      if(r.asSatisfiabilityResult().isSat() == Result::UNSAT) {
        checkProof();
      }
    }
    // Check that UNSAT results generate an unsat core correctly.
    if(options::checkUnsatCores()) {
      if(r.asSatisfiabilityResult().isSat() == Result::UNSAT) {
        TimerStat::CodeTimer checkUnsatCoreTimer(d_stats->d_checkUnsatCoreTime);
        checkUnsatCore();
      }
    }

    return r;
  } catch (UnsafeInterruptException& e) {
    AlwaysAssert(d_resourceManager->out());
    Result::UnknownExplanation why = d_resourceManager->outOfResources()
                                         ? Result::RESOURCEOUT
                                         : Result::TIMEOUT;
    return Result(Result::SAT_UNKNOWN, why, d_filename);
  }
}


Result SmtEngine::check() 
{
  Assert(d_fullyInited);
  Assert(d_pendingPops == 0);

  Trace("smt") << "SmtEngine::check()" << endl;


  if (d_rm->out())
  {
    Result::UnknownExplanation why = d_rm->outOfResources()
                                         ? Result::RESOURCEOUT
                                         : Result::TIMEOUT;
    return Result(Result::ENTAILMENT_UNKNOWN, why, d_filename);
  }
  d_rm->beginCall();

  // Make sure the prop layer has all of the assertions
  Trace("smt") << "SmtEngine::check(): processing assertions" << endl;
  processAssertionsInternal();
  Trace("smt") << "SmtEngine::check(): done processing assertions" << endl;

  TimerStat::CodeTimer solveTimer(d_stats->d_solveTime);

  Chat() << "solving..." << endl;
  Trace("smt") << "SmtEngine::check(): running check" << endl;
  Result result = d_propEngine->checkSat();

  d_rm->endCall();
  Trace("limit") << "SmtEngine::check(): cumulative millis "
                 << d_rm->getTimeUsage() << ", resources "
                 << d_rm->getResourceUsage() << endl;

  //FIXME return Result(result, d_filename);
  return result;
}

TheoryEngine* SmtSolver::getTheoryEngine() { return d_theoryEngine.get(); }
prop::PropEngine* SmtSolver::getPropEngine() { return d_propEngine.get(); }
}  // namespace smt
}  // namespace CVC4

