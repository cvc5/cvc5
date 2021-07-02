/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Equality engine manager for central equality engine architecture
 */

#include "theory/ee_manager_central.h"

#include "theory/quantifiers_engine.h"
#include "theory/shared_solver.h"
#include "theory/theory_engine.h"
#include "theory/theory_state.h"

namespace cvc5 {
namespace theory {

EqEngineManagerCentral::EqEngineManagerCentral(TheoryEngine& te,
                                               SharedSolver& shs,
                                               ProofNodeManager* pnm)
    : EqEngineManager(te, shs),
      d_masterEENotify(nullptr),
      d_masterEqualityEngine(nullptr),
      d_centralEENotify(*this),
      d_centralEqualityEngine(
          d_centralEENotify, te.getSatContext(), "centralEE", true),
      d_buildingModel(te.getSatContext(), false)
{
  for (TheoryId theoryId = theory::THEORY_FIRST;
       theoryId != theory::THEORY_LAST;
       ++theoryId)
  {
    d_theoryNotify[theoryId] = nullptr;
  }
  if (pnm != nullptr)
  {
    d_centralPfee.reset(new eq::ProofEqEngine(d_te.getSatContext(),
                                              d_te.getUserContext(),
                                              d_centralEqualityEngine,
                                              pnm));
    d_centralEqualityEngine.setProofEqualityEngine(d_centralPfee.get());
  }
}

EqEngineManagerCentral::~EqEngineManagerCentral() {}

void EqEngineManagerCentral::initializeTheories()
{
  context::Context* c = d_te.getSatContext();
  // initialize the shared solver
  EeSetupInfo esis;
  if (d_sharedSolver.needsEqualityEngine(esis))
  {
    // the shared solver uses central equality engine
    d_sharedSolver.setEqualityEngine(&d_centralEqualityEngine);
  }
  else
  {
    AlwaysAssert(false) << "Expected shared solver to use equality engine";
  }
  // whether to use master equality engine as central
  bool masterEqToCentral = true;

  const LogicInfo& logicInfo = d_te.getLogicInfo();
  for (TheoryId theoryId = theory::THEORY_FIRST;
       theoryId != theory::THEORY_LAST;
       ++theoryId)
  {
    // if the logic has a theory that does not use central equality engine,
    // we can't use the central equality engine for the master equality
    // engine
    if (logicInfo.isTheoryEnabled(theoryId)
        && !Theory::usesCentralEqualityEngine(theoryId))
    {
      masterEqToCentral = false;
      break;
    }
  }

  // initialize the master equality engine, which may be the central equality
  // engine
  if (logicInfo.isQuantified())
  {
    // construct the master equality engine
    Assert(d_masterEqualityEngine == nullptr);
    QuantifiersEngine* qe = d_te.getQuantifiersEngine();
    Assert(qe != nullptr);
    d_masterEENotify.reset(new MasterNotifyClass(qe));
    if (!masterEqToCentral)
    {
      d_masterEqualityEngineAlloc.reset(
          new eq::EqualityEngine(*d_masterEENotify.get(),
                                 d_te.getSatContext(),
                                 "theory::master",
                                 false));
      d_masterEqualityEngine = d_masterEqualityEngineAlloc.get();
    }
    else
    {
      d_masterEqualityEngine = &d_centralEqualityEngine;
      d_centralEENotify.d_newClassNotify.push_back(d_masterEENotify.get());
    }
  }

  // allocate equality engines per theory
  for (TheoryId theoryId = theory::THEORY_FIRST;
       theoryId != theory::THEORY_LAST;
       ++theoryId)
  {
    Theory* t = d_te.theoryOf(theoryId);
    if (t == nullptr)
    {
      // theory not active, skip
      continue;
    }
    Trace("ee-central") << "Setup equality engine for " << theoryId
                        << std::endl;
    // always allocate an object in d_einfo here
    EeTheoryInfo& eet = d_einfo[theoryId];
    EeSetupInfo esi;
    if (!t->needsEqualityEngine(esi))
    {
      Trace("ee-central") << "...does not need ee" << std::endl;
      // theory said it doesn't need an equality engine, skip
      continue;
    }
    if (esi.d_useMaster)
    {
      Trace("ee-central") << "...uses master" << std::endl;
      // the theory said it wants to use the master equality engine
      eet.d_usedEe = d_masterEqualityEngine;
      continue;
    }
    // set the notify
    eq::EqualityEngineNotify* notify = esi.d_notify;
    d_theoryNotify[theoryId] = notify;
    // split on whether integrated, or whether asked for master
    if (t->usesCentralEqualityEngine())
    {
      Trace("ee-central") << "...uses central" << std::endl;
      // the theory uses the central equality engine
      eet.d_usedEe = &d_centralEqualityEngine;
      // add to vectors for the kinds of notifications
      if (esi.needsNotifyNewClass())
      {
        d_centralEENotify.d_newClassNotify.push_back(notify);
      }
      if (esi.needsNotifyMerge())
      {
        d_centralEENotify.d_mergeNotify.push_back(notify);
      }
      if (esi.needsNotifyDisequal())
      {
        d_centralEENotify.d_disequalNotify.push_back(notify);
      }
      // remember the list of central theories
      d_centralThs.push_back(t);
      continue;
    }
    Trace("ee-central") << "...uses new" << std::endl;
    eet.d_allocEe.reset(allocateEqualityEngine(esi, c));
    // the theory uses the equality engine
    eet.d_usedEe = eet.d_allocEe.get();
    if (d_masterEqualityEngine != nullptr)
    {
      // set the master equality engine of the theory's equality engine
      eet.d_allocEe->setMasterEqualityEngine(d_masterEqualityEngine);
    }
  }

  // set the master equality engine of the theory's equality engine
  if (d_masterEqualityEngine != nullptr
      && d_masterEqualityEngine != &d_centralEqualityEngine)
  {
    d_centralEqualityEngine.setMasterEqualityEngine(d_masterEqualityEngine);
  }
}

void EqEngineManagerCentral::MasterNotifyClass::eqNotifyNewClass(TNode t)
{
  // adds t to the quantifiers term database
  d_quantEngine->eqNotifyNewClass(t);
}

//================================================ central

void EqEngineManagerCentral::notifyBuildingModel() {}

EqEngineManagerCentral::CentralNotifyClass::CentralNotifyClass(
    EqEngineManagerCentral& eemc)
    : d_eemc(eemc), d_mNotify(nullptr), d_quantEngine(nullptr)
{
}

bool EqEngineManagerCentral::CentralNotifyClass::eqNotifyTriggerPredicate(
    TNode predicate, bool value)
{
  Trace("eem-central") << "eqNotifyTriggerPredicate: " << predicate
                       << std::endl;
  return d_eemc.eqNotifyTriggerPredicate(predicate, value);
}

bool EqEngineManagerCentral::CentralNotifyClass::eqNotifyTriggerTermEquality(
    TheoryId tag, TNode t1, TNode t2, bool value)
{
  Trace("eem-central") << "eqNotifyTriggerTermEquality: " << t1 << " " << t2
                       << value << ", tag = " << tag << std::endl;
  return d_eemc.eqNotifyTriggerTermEquality(tag, t1, t2, value);
}

void EqEngineManagerCentral::CentralNotifyClass::eqNotifyConstantTermMerge(
    TNode t1, TNode t2)
{
  Trace("eem-central") << "eqNotifyConstantTermMerge: " << t1 << " " << t2
                       << std::endl;
  d_eemc.eqNotifyConstantTermMerge(t1, t2);
}

void EqEngineManagerCentral::CentralNotifyClass::eqNotifyNewClass(TNode t)
{
  Trace("eem-central") << "...eqNotifyNewClass " << t << std::endl;
  // notify all theories that have new equivalence class notifications
  for (eq::EqualityEngineNotify* notify : d_newClassNotify)
  {
    notify->eqNotifyNewClass(t);
  }
  // also always forward to quantifiers
  if (d_quantEngine != nullptr)
  {
    d_quantEngine->eqNotifyNewClass(t);
  }
}

void EqEngineManagerCentral::CentralNotifyClass::eqNotifyMerge(TNode t1,
                                                               TNode t2)
{
  Trace("eem-central") << "...eqNotifyMerge " << t1 << ", " << t2 << std::endl;
  // notify all theories that have merge notifications
  for (eq::EqualityEngineNotify* notify : d_mergeNotify)
  {
    notify->eqNotifyMerge(t1, t2);
  }
}

void EqEngineManagerCentral::CentralNotifyClass::eqNotifyDisequal(TNode t1,
                                                                  TNode t2,
                                                                  TNode reason)
{
  Trace("eem-central") << "...eqNotifyDisequal " << t1 << ", " << t2
                       << std::endl;
  // notify all theories that have disequal notifications
  for (eq::EqualityEngineNotify* notify : d_disequalNotify)
  {
    notify->eqNotifyDisequal(t1, t2, reason);
  }
}

bool EqEngineManagerCentral::eqNotifyTriggerPredicate(TNode predicate,
                                                      bool value)
{
  // if we're building model, ignore this propagation
  if (d_buildingModel.get())
  {
    return true;
  }
  // always propagate with the shared solver
  Trace("eem-central") << "...propagate " << predicate << ", " << value
                       << " with shared solver" << std::endl;
  bool ok = d_sharedSolver.propagateLit(predicate, value);
  if (!ok)
  {
    notifyInConflict();
  }
  return ok;
}

bool EqEngineManagerCentral::eqNotifyTriggerTermEquality(TheoryId tag,
                                                         TNode a,
                                                         TNode b,
                                                         bool value)
{
  // propagate to theory engine
  bool ok = d_sharedSolver.propagateLit(a.eqNode(b), value);
  if (!ok)
  {
    notifyInConflict();
    return false;
  }
  if (tag == THEORY_UF)
  {
    return true;
  }
  // propagate shared equality
  return d_sharedSolver.propagateSharedEquality(tag, a, b, value);
}

void EqEngineManagerCentral::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  Node lit = t1.eqNode(t2);
  Node conflict = d_centralEqualityEngine.mkExplainLit(lit);
  Trace("eem-central") << "...explained conflict of " << lit << " ... "
                       << conflict << std::endl;
  // notifyInConflict();
  d_sharedSolver.sendConflict(TrustNode::mkTrustConflict(conflict));
  return;
}

void EqEngineManagerCentral::notifyInConflict()
{
  // notify the states we are in conflict
  for (Theory* t : d_centralThs)
  {
    t->notifyInConflict();
  }
}

}  // namespace theory
}  // namespace cvc5
