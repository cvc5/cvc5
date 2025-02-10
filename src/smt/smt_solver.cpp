/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for SMT queries in an SolverEngine.
 */

#include "smt/smt_solver.h"

#include "options/arrays_options.h"
#include "options/base_options.h"
#include "options/main_options.h"
#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "prop/prop_engine.h"
#include "smt/assertions.h"
#include "smt/env.h"
#include "smt/logic_exception.h"
#include "smt/preprocessor.h"
#include "smt/proof_manager.h"
#include "smt/solver_engine_stats.h"
#include "theory/logic_info.h"
#include "theory/theory_engine.h"
#include "theory/theory_traits.h"

using namespace std;

namespace cvc5::internal {
namespace smt {

SmtSolver::SmtSolver(Env& env, SolverEngineStatistics& stats)
    : EnvObj(env),
      d_pp(env, stats),
      d_asserts(env),
      d_stats(stats),
      d_theoryEngine(nullptr),
      d_propEngine(nullptr),
      d_ppAssertions(userContext()),
      d_ppSkolemMap(userContext())
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
  finishInitPreprocessor();

  if (options().proof.proofLog)
  {
    smt::PfManager* pm = d_env.getProofManager();
    if (pm != nullptr)
    {
      // Logs proofs on the base output stream of the solver
      pm->startProofLogging(options().base.out, d_asserts);
    }
  }

  // Determine any illegal kinds that are dependent on options that need to be
  // guarded here. Note that nearly all illegal kinds should be properly guarded
  // by either the theory engine, theory solvers, or by theory rewriters. We
  // only require special handling for rare cases, including array constants,
  // where array constants *must* be rewritten by the rewriter for the purposes
  // of model verification, but we do not want array constants to appear in
  // assertions unless --arrays-exp is enabled.

  // Array constants are not supported unless arraysExp is enabled
  if (logicInfo().isTheoryEnabled(internal::theory::THEORY_ARRAYS)
      && !options().arrays.arraysExp)
  {
    d_illegalKinds.insert(Kind::STORE_ALL);
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
  finishInitPreprocessor();
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
  return d_propEngine->checkSat();
}

void SmtSolver::preprocess(preprocessing::AssertionPipeline& ap)
{
  TimerStat::CodeTimer paTimer(d_stats.d_processAssertionsTime);
  d_env.getResourceManager()->spendResource(Resource::PreprocessStep);

  // check illegal kinds here
  if (!d_illegalKinds.empty())
  {
    const std::vector<Node>& assertions = ap.ref();
    std::unordered_set<TNode> visited;
    for (const Node& a : assertions)
    {
      Kind k = expr::hasSubtermKinds(d_illegalKinds, a, visited);
      if (k != Kind::UNDEFINED_KIND)
      {
        std::stringstream ss;
        ss << "ERROR: cannot handle assertion with term of kind " << k
           << " in this configuration";
        if (k == Kind::STORE_ALL)
        {
          ss << ", unless --arrays-exp is enabled";
        }
        throw LogicException(ss.str());
      }
    }
  }

  // process the assertions with the preprocessor
  d_pp.process(ap);

  // end: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones
}

void SmtSolver::assertToInternal(preprocessing::AssertionPipeline& ap)
{
  // carry information about soundness to the theory engine we are sending to
  if (ap.isRefutationUnsound())
  {
    d_theoryEngine->setRefutationUnsound(theory::IncompleteId::PREPROCESSING);
  }
  if (ap.isModelUnsound())
  {
    d_theoryEngine->setModelUnsound(theory::IncompleteId::PREPROCESSING);
  }
  // get the assertions
  const std::vector<Node>& assertions = ap.ref();
  preprocessing::IteSkolemMap& ism = ap.getIteSkolemMap();
  // assert to prop engine, which will convert to CNF
  d_env.verbose(2) << "converting to CNF..." << endl;
  d_propEngine->assertInputFormulas(assertions, ism);

  // It is important to distinguish the input assertions from the skolem
  // definitions, as the decision justification heuristic treates the latter
  // specially. Note that we don't pass the preprocess learned literals
  // d_pp.getLearnedLiterals() here, since they may not exactly correspond
  // to the actual preprocessed learned literals, as the input may have
  // undergone further preprocessing.
  // if we can deep restart, we always remember the preprocessed formulas,
  // which are the basis for the next check-sat.
  if (trackPreprocessedAssertions())
  {
    // incompatible with global negation
    Assert(!options().quantifiers.globalNegate);
    theory::SubstitutionMap& sm = d_env.getTopLevelSubstitutions().get();
    size_t startIndex = d_ppAssertions.size();
    // remember the assertions and Skolem mapping
    for (const Node& a : assertions)
    {
      d_ppAssertions.push_back(a);
    }
    for (const std::pair<const size_t, Node>& k : ism)
    {
      // optimization: skip skolems that were eliminated in preprocessing
      if (sm.hasSubstitution(k.second))
      {
        continue;
      }
      size_t newIndex = k.first + startIndex;
      d_ppSkolemMap[newIndex] = k.second;
    }
  }
}

const context::CDList<Node>& SmtSolver::getPreprocessedAssertions() const
{
  return d_ppAssertions;
}

const context::CDHashMap<size_t, Node>& SmtSolver::getPreprocessedSkolemMap()
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

void SmtSolver::resetTrail()
{
  Assert(d_propEngine != nullptr);
  d_propEngine->resetTrail();
}

void SmtSolver::finishInitPreprocessor()
{
  // determine if we are assigning a preprocess proof generator here
  smt::PfManager* pm = d_env.getProofManager();
  smt::PreprocessProofGenerator* pppg = nullptr;
  if (pm != nullptr)
  {
    pppg = pm->getPreprocessProofGenerator();
  }
  d_pp.finishInit(d_theoryEngine.get(), d_propEngine.get(), pppg);
}

}  // namespace smt
}  // namespace cvc5::internal
