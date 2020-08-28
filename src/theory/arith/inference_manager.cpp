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

#include "options/arith_options.h"
#include "theory/arith/theory_arith.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace arith {

InferenceManager::InferenceManager(TheoryArith& ta,
                                   ArithState& astate,
                                   ProofNodeManager* pnm)
    : InferenceManagerBuffered(ta, astate, pnm),
      d_lemmas(ta.getUserContext()),
      d_lemmasPp(ta.getUserContext())
{
}

void InferenceManager::addLemma(std::shared_ptr<ArithLemma> lemma)
{
  if (!isNewLemma(*lemma))
  {
    return;
  }
  if (isEntailedFalse(*lemma))
  {
      addConflict(lemma->d_node, lemma->d_inference);
      return;
  }
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
  if (!isNewLemma(*lemma))
  {
    return;
  }
  if (isEntailedFalse(*lemma))
  {
      d_waitingLem.clear();
  }
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

std::size_t InferenceManager::countWaitingLemmas() const
{
  return d_waitingLem.size();
}

bool InferenceManager::isNewLemma(ArithLemma& lem)
{
  Trace("arith-inf-manager")
      << "InferenceManager::Lemma pre-rewrite : " << lem.d_node << std::endl;
  lem.d_node = Rewriter::rewrite(lem.d_node);

  NodeSet& lcache =
      isLemmaPropertyPreprocess(lem.d_property) ? d_lemmasPp : d_lemmas;
  if (lcache.find(lem.d_node) != lcache.end())
  {
    Trace("arith-inf-manager")
        << "InferenceManager::Lemma duplicate: " << lem.d_node << std::endl;
    return false;
  }
  return true;
}

bool InferenceManager::isEntailedFalse(const ArithLemma& lem)
{
  if (options::nlExtEntailConflicts())
  {
    Node ch_lemma = lem.d_node.negate();
    ch_lemma = Rewriter::rewrite(ch_lemma);
    Trace("arith-inf-manager") << "InferenceManager::Check entailment of "
                               << ch_lemma << "..." << std::endl;

    std::pair<bool, Node> et = d_theory.getValuation().entailmentCheck(
        options::TheoryOfMode::THEORY_OF_TYPE_BASED, ch_lemma);
    Trace("arith-inf-manager") << "entailment test result : " << et.first << " "
                               << et.second << std::endl;
    if (et.first)
    {
      Trace("arith-inf-manager")
          << "*** Lemma entailed to be in conflict : " << lem.d_node
          << std::endl;
      return true;
    }
  }
  return false;
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
