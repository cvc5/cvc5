/*********************                                                        */
/*! \file ee_manager_distributed.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for equality sharing.
 **/

#include "theory/ee_manager_distributed.h"

#include "theory/quantifiers_engine.h"
#include "theory/shared_solver.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

EqEngineManagerDistributed::EqEngineManagerDistributed(TheoryEngine& te,
                                                       SharedSolver& shs)
    : EqEngineManager(te, shs), d_masterEENotify(nullptr)
{
}

EqEngineManagerDistributed::~EqEngineManagerDistributed()
{
}

void EqEngineManagerDistributed::initializeTheories()
{
  context::Context* c = d_te.getSatContext();
  // initialize the shared solver
  EeSetupInfo esis;
  if (d_sharedSolver.needsEqualityEngine(esis))
  {
    // allocate an equality engine for the shared terms database
    d_stbEqualityEngine.reset(allocateEqualityEngine(esis, c));
    d_sharedSolver.setEqualityEngine(d_stbEqualityEngine.get());
  }
  else
  {
    Unhandled() << "Expected shared solver to use equality engine";
  }

  const LogicInfo& logicInfo = d_te.getLogicInfo();
  if (logicInfo.isQuantified())
  {
    // construct the master equality engine
    Assert(d_masterEqualityEngine == nullptr);
    QuantifiersEngine* qe = d_te.getQuantifiersEngine();
    Assert(qe != nullptr);
    d_masterEENotify.reset(new MasterNotifyClass(qe));
    d_masterEqualityEngine.reset(new eq::EqualityEngine(*d_masterEENotify.get(),
                                                        d_te.getSatContext(),
                                                        "theory::master",
                                                        false));
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
    // always allocate an object in d_einfo here
    EeTheoryInfo& eet = d_einfo[theoryId];
    EeSetupInfo esi;
    if (!t->needsEqualityEngine(esi))
    {
      // the theory said it doesn't need an equality engine, skip
      continue;
    }
    if (esi.d_useMaster)
    {
      // the theory said it wants to use the master equality engine
      eet.d_usedEe = d_masterEqualityEngine.get();
      continue;
    }
    // allocate the equality engine
    eet.d_allocEe.reset(allocateEqualityEngine(esi, c));
    // the theory uses the equality engine
    eet.d_usedEe = eet.d_allocEe.get();
    // if there is a master equality engine
    if (d_masterEqualityEngine != nullptr)
    {
      // set the master equality engine of the theory's equality engine
      eet.d_allocEe->setMasterEqualityEngine(d_masterEqualityEngine.get());
    }
  }
}

void EqEngineManagerDistributed::notifyModel(bool incomplete)
{
  // should have a consistent master equality engine
  if (d_masterEqualityEngine.get() != nullptr)
  {
    AlwaysAssert(d_masterEqualityEngine->consistent());
  }
}

void EqEngineManagerDistributed::MasterNotifyClass::eqNotifyNewClass(TNode t)
{
  // adds t to the quantifiers term database
  d_quantEngine->eqNotifyNewClass(t);
}

}  // namespace theory
}  // namespace CVC4
