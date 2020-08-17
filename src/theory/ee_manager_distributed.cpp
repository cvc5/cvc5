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

const EeTheoryInfo* EqEngineManager::getEeTheoryInfo(TheoryId tid) const
{
  std::map<TheoryId, EeTheoryInfo>::const_iterator it = d_einfo.find(tid);
  if (it != d_einfo.end())
  {
    return &it->second;
  }
  return nullptr;
}

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
    // always allocate an object in d_einfo here
    EeTheoryInfo& eet = d_einfo[theoryId];
    EeSetupInfo esi;
    if (!t->needsEqualityEngine(esi))
    {
      // theory said it doesn't need an equality engine, skip
      continue;
    }
    // allocate the equality engine
    eet.d_allocEe.reset(allocateEqualityEngine(esi, c));
    eet.d_usedEe = eet.d_allocEe.get();
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

eq::EqualityEngine* EqEngineManagerDistributed::allocateEqualityEngine(
    EeSetupInfo& esi, context::Context* c)
{
  if (esi.d_notify != nullptr)
  {
    return new eq::EqualityEngine(
        *esi.d_notify, c, esi.d_name, esi.d_constantsAreTriggers);
  }
  // the theory doesn't care about explicit notifications
  return new eq::EqualityEngine(c, esi.d_name, esi.d_constantsAreTriggers);
}

}  // namespace theory
}  // namespace CVC4
