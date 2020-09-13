/*********************                                                        */
/*! \file combination_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a care graph based approach for theory combination.
 **/

#include "theory/combination_engine.h"

#include "expr/node_visitor.h"
#include "theory/care_graph.h"
#include "theory/ee_manager_distributed.h"
#include "theory/model_manager_distributed.h"
#include "theory/shared_terms_database.h"
#include "theory/term_registration_visitor.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

CombinationEngine::CombinationEngine(TheoryEngine& te,
                                     const std::vector<Theory*>& paraTheories,
                                     ProofNodeManager* pnm)
    : d_te(te),
      d_logicInfo(te.getLogicInfo()),
      d_paraTheories(paraTheories),
      d_eemanager(nullptr),
      d_mmanager(nullptr),
      d_cmbsPg(pnm ? new EagerProofGenerator(pnm, te.getUserContext())
                   : nullptr)
{
}

CombinationEngine::~CombinationEngine() {}

void CombinationEngine::finishInit()
{
  // create the equality engine, model manager, and shared solver
  if (options::eeMode() == options::EqEngineMode::DISTRIBUTED)
  {
    // make the distributed equality engine manager
    std::unique_ptr<EqEngineManagerDistributed> eeDistributed(
        new EqEngineManagerDistributed(d_te));
    // make the distributed model manager
    d_mmanager.reset(new ModelManagerDistributed(d_te, *eeDistributed.get()));
    d_eemanager = std::move(eeDistributed);
  }
  else
  {
    Unhandled() << "CombinationEngine::finishInit: equality engine mode "
                << options::eeMode() << " not supported";
  }

  Assert(d_eemanager != nullptr);

  // initialize equality engines in all theories, including quantifiers engine
  // and the (provided) shared solver
  d_eemanager->initializeTheories();

  Assert(d_mmanager != nullptr);
  // initialize the model manager
  d_mmanager->finishInit();

  // initialize equality engine of the model using the equality engine manager
  TheoryModel* m = d_mmanager->getModel();
  eq::EqualityEngineNotify* meen = getModelEqualityEngineNotify();
  d_eemanager->initializeModel(m, meen);
}

const EeTheoryInfo* CombinationEngine::getEeTheoryInfo(TheoryId tid) const
{
  return d_eemanager->getEeTheoryInfo(tid);
}

eq::EqualityEngine* CombinationEngine::getCoreEqualityEngine()
{
  return d_eemanager->getCoreEqualityEngine();
}

void CombinationEngine::resetModel() { d_mmanager->resetModel(); }

void CombinationEngine::postProcessModel(bool incomplete)
{
  // should have a consistent core equality engine
  eq::EqualityEngine* mee = d_eemanager->getCoreEqualityEngine();
  if (mee != nullptr)
  {
    AlwaysAssert(mee->consistent());
  }
  // postprocess with the model
  d_mmanager->postProcessModel(incomplete);
}

theory::TheoryModel* CombinationEngine::getModel()
{
  return d_mmanager->getModel();
}

bool CombinationEngine::isProofEnabled() const { return d_cmbsPg != nullptr; }

eq::EqualityEngineNotify* CombinationEngine::getModelEqualityEngineNotify()
{
  // by default, no notifications from model's equality engine
  return nullptr;
}

void CombinationEngine::sendLemma(TrustNode trn, TheoryId atomsTo)
{
  d_te.lemma(trn, LemmaProperty::NONE, atomsTo);
}

void CombinationEngine::resetRound()
{
  // do nothing
}

}  // namespace theory
}  // namespace CVC4
