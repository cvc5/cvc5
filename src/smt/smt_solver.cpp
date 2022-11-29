/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
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

#include "smt/smt_solver.h"

#include "options/base_options.h"
#include "options/main_options.h"
#include "options/smt_options.h"
#include "prop/prop_engine.h"
#include "smt/assertions.h"
#include "smt/env.h"
#include "smt/logic_exception.h"
#include "smt/preprocessor.h"
#include "smt/solver_engine_stats.h"
#include "theory/logic_info.h"
#include "theory/theory_engine.h"
#include "theory/theory_traits.h"

using namespace std;

namespace cvc5::internal {
namespace smt {

SmtSolver::SmtSolver(Env& env,
                     AbstractValues& abs,
                     SolverEngineStatistics& stats)
    : EnvObj(env),
      d_pp(env, stats),
      d_asserts(env, abs),
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
    // reset the rule checkers
    pnm->getChecker()->reset();
    // add rule checkers from the theory engine
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
  if (options().smt.produceProofs)
  {
    d_asserts.enableProofs(d_pp.getPreprocessProofGenerator());
  }
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
  if (options().smt.produceProofs)
  {
    d_asserts.enableProofs(d_pp.getPreprocessProofGenerator());
  }
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

Result SmtSolver::checkSatInternal()
{
  // call the prop engine to check sat
  Result result = d_propEngine->checkSat();
  // handle options-specific modifications to result
  if ((options().smt.solveRealAsInt || options().smt.solveIntAsBV > 0)
      && result.getStatus() == Result::UNSAT)
  {
    result = Result(Result::UNKNOWN, UnknownExplanation::UNKNOWN_REASON);
  }
  // handle preprocessing-specific modifications to result
  if (options().quantifiers.globalNegate)
  {
    Trace("smt") << "SmtSolver::process global negate " << result << std::endl;
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

void SmtSolver::refreshAssertions()
{
  // preprocess
  preprocessing::AssertionPipeline& ap = d_asserts.getAssertionPipeline();
  preprocess(ap);
  // assert to internal
  assertToInternal(ap);
}

void SmtSolver::preprocess(preprocessing::AssertionPipeline& ap)
{
  TimerStat::CodeTimer paTimer(d_stats.d_processAssertionsTime);
  d_env.getResourceManager()->spendResource(Resource::PreprocessStep);

  // must first refresh the assertions, in the case global declarations is true
  d_asserts.refresh();
  // process the assertions with the preprocessor
  d_pp.process(ap);

  // end: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones

  const std::vector<Node>& assertions = ap.ref();
  // It is important to distinguish the input assertions from the skolem
  // definitions, as the decision justification heuristic treates the latter
  // specially. Note that we don't pass the preprocess learned literals
  // d_pp.getLearnedLiterals() here, since they may not exactly correspond
  // to the actual preprocessed learned literals, as the input may have
  // undergone further preprocessing.
  preprocessing::IteSkolemMap& ism = ap.getIteSkolemMap();
  // if we can deep restart, we always remember the preprocessed formulas,
  // which are the basis for the next check-sat.
  if (trackPreprocessedAssertions())
  {
    // incompatible with global negation
    Assert(!options().quantifiers.globalNegate);
    theory::SubstitutionMap& sm = d_env.getTopLevelSubstitutions().get();
    // note that if a skolem is eliminated in preprocessing, we remove it
    // from the preprocessed skolem map
    std::vector<size_t> elimSkolems;
    for (const std::pair<const size_t, Node>& k : d_ppSkolemMap)
    {
      if (sm.hasSubstitution(k.second))
      {
        Trace("deep-restart-ism")
            << "SKOLEM:" << k.second << " was eliminated during preprocessing"
            << std::endl;
        elimSkolems.push_back(k.first);
        continue;
      }
      Trace("deep-restart-ism") << "SKOLEM:" << k.second << " is skolem for "
                                << assertions[k.first] << std::endl;
    }
    for (size_t i : elimSkolems)
    {
      ism.erase(i);
    }
    // remember the assertions and Skolem mapping
    d_ppAssertions = assertions;
    d_ppSkolemMap = ism;
  }
}

void SmtSolver::assertToInternal(preprocessing::AssertionPipeline& ap)
{
  // get the assertions
  const std::vector<Node>& assertions = ap.ref();
  preprocessing::IteSkolemMap& ism = ap.getIteSkolemMap();
  // assert to prop engine, which will convert to CNF
  d_env.verbose(2) << "converting to CNF..." << endl;
  d_propEngine->assertInputFormulas(assertions, ism);
  // clear the current assertions
  ap.clear();
}

const std::vector<Node>& SmtSolver::getPreprocessedAssertions() const
{
  return d_ppAssertions;
}

const std::unordered_map<size_t, Node>& SmtSolver::getPreprocessedSkolemMap()
    const
{
  return d_ppSkolemMap;
}

bool SmtSolver::trackPreprocessedAssertions() const
{
  return options().smt.deepRestartMode != options::DeepRestartMode::NONE
         || options().smt.produceProofs;
}

TheoryEngine* SmtSolver::getTheoryEngine() { return d_theoryEngine.get(); }

prop::PropEngine* SmtSolver::getPropEngine() { return d_propEngine.get(); }

theory::QuantifiersEngine* SmtSolver::getQuantifiersEngine()
{
  Assert(d_theoryEngine != nullptr);
  return d_theoryEngine->getQuantifiersEngine();
}

Preprocessor* SmtSolver::getPreprocessor() { return &d_pp; }

Assertions& SmtSolver::getAssertions() { return d_asserts; }

void SmtSolver::pushPropContext()
{
  TimerStat::CodeTimer pushPopTimer(d_stats.d_pushPopTime);
  Assert(d_propEngine != nullptr);
  d_propEngine->push();
}

void SmtSolver::popPropContext()
{
  TimerStat::CodeTimer pushPopTimer(d_stats.d_pushPopTime);
  Assert(d_propEngine != nullptr);
  d_propEngine->pop();
}

void SmtSolver::postsolve()
{
  Assert(d_propEngine != nullptr);
  d_propEngine->resetTrail();

  Assert(d_theoryEngine != nullptr);
  d_theoryEngine->postsolve();
}

}  // namespace smt
}  // namespace cvc5::internal
