/*********************                                                        */
/*! \file inference_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the inference manager for the theory of strings.
 **/

#include "theory/arith/inference_manager.h"

#include "theory/arith/theory_arith.h"

namespace CVC4 {
namespace theory {
namespace arith {

InferenceManager::InferenceManager(TheoryArith& ta,
                                   ArithState& astate,
                                   ProofNodeManager* pnm)
    : InferenceManagerBuffered(ta, astate, pnm)
{
}

void InferenceManager::addLemma(std::shared_ptr<ArithLemma> lemma)
{
  addPendingLemma(std::move(lemma));
}
void InferenceManager::addLemma(const ArithLemma& lemma)
{
  addLemma(std::make_shared<ArithLemma>(lemma));
}
void InferenceManager::addLemma(const Node& lemma, nl::Inference inftype)
{
  addLemma(std::make_shared<ArithLemma>(
      lemma, LemmaProperty::NONE, nullptr, inftype));
}

void InferenceManager::addWaitingLemma(std::shared_ptr<ArithLemma> lemma)
{
  d_waitingLem.emplace_back(std::move(lemma));
}
void InferenceManager::addWaitingLemma(const ArithLemma& lemma)
{
  addLemma(std::make_shared<ArithLemma>(lemma));
}
void InferenceManager::addWaitingLemma(const Node& lemma, nl::Inference inftype)
{
  addLemma(std::make_shared<ArithLemma>(
      lemma, LemmaProperty::NONE, nullptr, inftype));
}

void InferenceManager::flushWaitingLemmas()
{
  for (auto& lem : d_waitingLem)
  {
    addPendingLemma(std::move(lem));
  }
  d_waitingLem.clear();
}

void InferenceManager::addConflict(const Node& conf, nl::Inference inftype)
{
  conflict(conf);
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
