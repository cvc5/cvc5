/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Management of a care graph based approach for theory combination.
 */

#include "theory/combination_engine.h"

#include "expr/node_visitor.h"
#include "proof/eager_proof_generator.h"
#include "theory/care_graph.h"
#include "theory/ee_manager_central.h"
#include "theory/ee_manager_distributed.h"
#include "theory/model_manager.h"
#include "theory/model_manager_distributed.h"
#include "theory/shared_solver_distributed.h"
#include "theory/theory_engine.h"

namespace cvc5::internal {
namespace theory {

CombinationEngine::CombinationEngine(Env& env,
                                     TheoryEngine& te,
                                     const std::vector<Theory*>& paraTheories)
    : EnvObj(env),
      d_te(te),
      d_valuation(&te),
      d_logicInfo(env.getLogicInfo()),
      d_paraTheories(paraTheories),
      d_eemanager(nullptr),
      d_mmanager(nullptr),
      d_sharedSolver(nullptr),
      d_cmbsPg(env.isTheoryProofProducing()
                   ? new EagerProofGenerator(env, env.getUserContext())
                   : nullptr)
{
  // create the equality engine, model manager, and shared solver
  if (options().theory.eeMode == options::EqEngineMode::DISTRIBUTED)
  {
    // use the distributed shared solver
    d_sharedSolver.reset(new SharedSolverDistributed(env, d_te));
    // make the distributed equality engine manager
    d_eemanager.reset(
        new EqEngineManagerDistributed(env, d_te, *d_sharedSolver.get()));
    // make the distributed model manager
    d_mmanager.reset(
        new ModelManagerDistributed(env, d_te, *d_eemanager.get()));
  }
  else if (options().theory.eeMode == options::EqEngineMode::CENTRAL)
  {
    // for now, the shared solver is the same in both approaches; use the
    // distributed one for now
    d_sharedSolver.reset(new SharedSolverDistributed(env, d_te));
    // make the central equality engine manager
    d_eemanager.reset(
        new EqEngineManagerCentral(env, d_te, *d_sharedSolver.get()));
    // make the distributed model manager
    d_mmanager.reset(
        new ModelManagerDistributed(env, d_te, *d_eemanager.get()));
  }
  else
  {
    Unhandled() << "CombinationEngine::finishInit: equality engine mode "
                << options().theory.eeMode << " not supported";
  }
}

CombinationEngine::~CombinationEngine() {}

void CombinationEngine::finishInit()
{
  Assert(d_eemanager != nullptr);

  // initialize equality engines in all theories, including quantifiers engine
  // and the (provided) shared solver
  d_eemanager->initializeTheories();

  Assert(d_mmanager != nullptr);
  // initialize the model manager, based on the notify object of this class
  eq::EqualityEngineNotify* meen = getModelEqualityEngineNotify();
  d_mmanager->finishInit(meen);
}

const EeTheoryInfo* CombinationEngine::getEeTheoryInfo(TheoryId tid) const
{
  return d_eemanager->getEeTheoryInfo(tid);
}

void CombinationEngine::resetModel() { d_mmanager->resetModel(); }

void CombinationEngine::postProcessModel(bool incomplete)
{
  d_eemanager->notifyModel(incomplete);
  // postprocess with the model
  d_mmanager->postProcessModel(incomplete);
}

theory::TheoryModel* CombinationEngine::getModel()
{
  return d_mmanager->getModel();
}

SharedSolver* CombinationEngine::getSharedSolver()
{
  return d_sharedSolver.get();
}
bool CombinationEngine::isProofEnabled() const { return d_cmbsPg != nullptr; }

eq::EqualityEngineNotify* CombinationEngine::getModelEqualityEngineNotify()
{
  // by default, no notifications from model's equality engine
  return nullptr;
}

void CombinationEngine::resetRound()
{
  // compute the relevant terms?
}

}  // namespace theory
}  // namespace cvc5::internal
