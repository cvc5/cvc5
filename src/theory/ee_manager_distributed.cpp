/*********************                                                        */
/*! \file ee_manager_distributed.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for equality sharing.
 **/

#include "theory/ee_manager_distributed.h"

#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

EqEngineManagerDistributed::EqEngineManagerDistributed(TheoryEngine& te)
    : d_te(te), d_masterEENotify(nullptr)
{
}

EqEngineManagerDistributed::~EqEngineManagerDistributed() {}

void EqEngineManagerDistributed::finishInit()
{
  context::Context* c = d_te.getSatContext();
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
    EeSetupInfo esi;
    if (!t->needsEqualityEngine(esi))
    {
      // theory said it doesn't need an equality engine, skip
      continue;
    }
    // allocate the equality engine
    EeTheoryInfo& eet = d_einfo[theoryId];
    if (esi.d_notify!=nullptr)
    {
      eet.d_allocEe.reset(
          new eq::EqualityEngine(*esi.d_notify, c, esi.d_name, esi.d_constantsAreTriggers));
    }
    else
    {
      // don't care about notifications
      eet.d_allocEe.reset(
          new eq::EqualityEngine(c, esi.d_name, esi.d_constantsAreTriggers));
    }
    // the theory uses this equality engine
    eq::EqualityEngine* eeAlloc = eet.d_allocEe.get();
    t->setEqualityEngine(eeAlloc);
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
      EeTheoryInfo& eet = d_einfo[theoryId];
      // Get the allocated equality engine, and connect it to the master
      // equality engine.
      eq::EqualityEngine* eeAlloc = eet.d_allocEe.get();
      if (eeAlloc != nullptr)
      {
        // set the master equality engine of the theory's equality engine
        eeAlloc->setMasterEqualityEngine(d_masterEqualityEngine.get());
      }
    }
  }
}

void EqEngineManagerDistributed::MasterNotifyClass::eqNotifyNewClass(TNode t)
{
  // adds t to the quantifiers term database
  d_quantEngine->eqNotifyNewClass(t);
}

eq::EqualityEngine* EqEngineManagerDistributed::getMasterEqualityEngine()
{
  return d_masterEqualityEngine.get();
}

}  // namespace theory
}  // namespace CVC4
