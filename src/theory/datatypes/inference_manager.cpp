/*********************                                                        */
/*! \file inference_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Datatypes inference manager
 **/

#include "theory/datatypes/inference_manager.h"

#include "expr/dtype.h"
#include "options/datatypes_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/theory.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace datatypes {

InferenceManager::InferenceManager(Theory& t,
                                   TheoryState& state,
                                   ProofNodeManager* pnm)
    : InferenceManagerBuffered(t, state, nullptr),
      d_inferenceLemmas("theory::datatypes::inferenceLemmas"),
      d_inferenceFacts("theory::datatypes::inferenceFacts")
{
  smtStatisticsRegistry()->registerStat(&d_inferenceLemmas);
  smtStatisticsRegistry()->registerStat(&d_inferenceFacts);
}

InferenceManager::~InferenceManager()
{
  smtStatisticsRegistry()->unregisterStat(&d_inferenceLemmas);
  smtStatisticsRegistry()->unregisterStat(&d_inferenceFacts);
}

void InferenceManager::addPendingInference(Node conc,
                                           Node exp,
                                           bool forceLemma,
                                           InferId i)
{
  if (forceLemma)
  {
    d_pendingLem.emplace_back(new DatatypesInference(this, conc, exp, i));
  }
  else
  {
    d_pendingFact.emplace_back(new DatatypesInference(this, conc, exp, i));
  }
}

void InferenceManager::process()
{
  // process pending lemmas, used infrequently, only for definitional lemmas
  doPendingLemmas();
  // now process the pending facts
  doPendingFacts();
}

bool InferenceManager::sendLemmas(const std::vector<Node>& lemmas)
{
  bool ret = false;
  for (const Node& lem : lemmas)
  {
    if (lemma(lem))
    {
      ret = true;
    }
  }
  return ret;
}

bool InferenceManager::processDtInference(Node conc,
                                          Node exp,
                                          InferId id,
                                          bool asLemma)
{
  Trace("dt-lemma-debug") << "processDtInference : " << conc << " via " << exp
                          << " by " << id << ", asLemma = " << asLemma
                          << std::endl;
  if (asLemma)
  {
    // send it as a lemma
    Node lem;
    if (!exp.isNull() && !exp.isConst())
    {
      lem = NodeManager::currentNM()->mkNode(kind::IMPLIES, exp, conc);
    }
    else
    {
      lem = conc;
    }
    if (!lemma(lem))
    {
      Trace("dt-lemma-debug") << "...duplicate lemma" << std::endl;
      return false;
    }
    d_inferenceLemmas << id;
  }
  else
  {
    // assert the internal fact, which has the same issue as above
    bool polarity = conc.getKind() != NOT;
    TNode atom = polarity ? conc : conc[0];
    assertInternalFact(atom, polarity, exp);
    d_inferenceFacts << id;
  }
  return true;
}

}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4
