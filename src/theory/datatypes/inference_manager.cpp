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
#include "theory/theory.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace datatypes {

InferenceManager::InferenceManager(Theory& t,
                                   TheoryState& state,
                                   ProofNodeManager* pnm)
    : InferenceManagerBuffered(t, state, nullptr)
{
}

void InferenceManager::addPendingInference(Node conc,
                                           Node exp,
                                           bool forceLemma, Inference i )
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

bool InferenceManager::processDtInference(DatatypesInference& di, bool asLemma)
{
  Trace("dt-lemma-debug")
      << "processDtInference : " << di.d_conc << " via " << di.d_exp << " by " << di.getInference() << ", asLemma = " << asLemma << std::endl;
  if (asLemma)
  {
    // send it as an (explained) lemma
    std::vector<Node> expv;
    if (!di.d_exp.isNull() && !di.d_exp.isConst())
    {
      expv.push_back(di.d_exp);
    }
    return lemmaExp(di.d_conc, expv, {});
  }
  // assert the internal fact
  bool polarity = di.d_conc.getKind() != NOT;
  TNode atom = polarity ? di.d_conc : di.d_conc[0];
  assertInternalFact(atom, polarity, di.d_exp);
  return true;
}

}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4
