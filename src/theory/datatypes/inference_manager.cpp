/*********************                                                        */
/*! \file inference_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
    : InferenceManagerBuffered(t, state, pnm),
      d_lemmasSent(t.getSatContext()),
      d_addedLemma(false),
      d_addedFact(false)
{
  d_true = NodeManager::currentNM()->mkConst(true);
}

void InferenceManager::reset()
{
  d_addedLemma = false;
  d_addedFact = false;
}

bool InferenceManager::mustCommunicateFact(Node n, Node exp) const
{
  Trace("dt-lemma-debug") << "Compute for " << exp << " => " << n << std::endl;
  bool addLemma = false;
  if (options::dtInferAsLemmas() && exp != d_true)
  {
    addLemma = true;
  }
  else if (n.getKind() == EQUAL)
  {
    TypeNode tn = n[0].getType();
    if (!tn.isDatatype())
    {
      addLemma = true;
    }
    else
    {
      const DType& dt = tn.getDType();
      addLemma = dt.involvesExternalType();
    }
  }
  else if (n.getKind() == LEQ || n.getKind() == OR)
  {
    addLemma = true;
  }
  if (addLemma)
  {
    Trace("dt-lemma-debug") << "Communicate " << n << std::endl;
    return true;
  }
  Trace("dt-lemma-debug") << "Do not need to communicate " << n << std::endl;
  return false;
}

void InferenceManager::process()
{
  // process pending lemmas, used infrequently, only for definitional lemmas
  doPendingLemmas();
  // now process the pending facts
  size_t i = 0;
  NodeManager* nm = NodeManager::currentNM();
  while (!d_theoryState.isInConflict() && i < d_pendingFact.size())
  {
    std::pair<Node, Node>& pfact = d_pendingFact[i];
    Node fact = pfact.first;
    Node exp = pfact.second;
    Trace("datatypes-debug")
        << "Assert fact (#" << (i + 1) << "/" << d_pendingFact.size() << ") "
        << fact << " with explanation " << exp << std::endl;
    // check to see if we have to communicate it to the rest of the system
    if (mustCommunicateFact(fact, exp))
    {
      Node lem = fact;
      if (exp.isNull() || exp == d_true)
      {
        Trace("dt-lemma-debug") << "Trivial explanation." << std::endl;
      }
      else
      {
        Trace("dt-lemma-debug") << "Get explanation..." << std::endl;
        std::vector<TNode> assumptions;
        explain(exp, assumptions);
        if (assumptions.empty())
        {
          lem = fact;
        }
        else
        {
          std::vector<Node> children;
          for (const TNode& assumption : assumptions)
          {
            children.push_back(assumption.negate());
          }
          children.push_back(fact);
          lem = nm->mkNode(OR, children);
        }
      }
      Trace("dt-lemma") << "Datatypes lemma : " << lem << std::endl;
      doSendLemma(lem);
    }
    else
    {
      // assert the internal fact
      bool polarity = fact.getKind() != NOT;
      TNode atom = polarity ? fact : fact[0];
      assertInternalFact(atom, polarity, exp);
      d_addedFact = true;
    }
    Trace("datatypes-debug") << "Finished fact " << fact
                             << ", now = " << d_theoryState.isInConflict()
                             << " " << d_pendingFact.size() << std::endl;
    i++;
  }
  d_pendingFact.clear();
}

bool InferenceManager::hasAddedFact() const { return d_addedFact; }
bool InferenceManager::hasAddedLemma() const { return d_addedLemma; }
bool InferenceManager::doSendLemma(Node lem, LemmaProperty p, bool cached)
{
  // don't cache lemmas with non-standard properties
  Assert(!cached || p == LemmaProperty::NONE);
  bool doSend = false;
  if (!cached)
  {
    // always send
    doSend = true;
  }
  else if (d_lemmasSent.find(lem) == d_lemmasSent.end())
  {
    Trace("dt-lemma-send") << "TheoryDatatypes::doSendLemma : " << lem
                           << std::endl;
    d_lemmasSent.insert(lem);
    doSend = true;
  }
  if (doSend)
  {
    // call the base class
    lemma(lem);
    d_addedLemma = true;
    return true;
  }
  Trace("dt-lemma-send") << "TheoryDatatypes::doSendLemma : duplicate : " << lem
                         << std::endl;
  return false;
}

bool InferenceManager::doSendLemmas(const std::vector<Node>& lemmas)
{
  bool ret = false;
  for (const Node& lem : lemmas)
  {
    bool cret = doSendLemma(lem);
    ret = ret || cret;
  }
  return ret;
}

}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4
