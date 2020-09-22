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

DatatypesInference::DatatypesInference(Node conc, Node exp, ProofGenerator* pg)
    : SimpleTheoryInternalFact(conc, exp, pg)
{
  // false is not a valid explanation
  Assert(d_exp.isNull() || !d_exp.isConst() || d_exp.getConst<bool>());
}

bool DatatypesInference::mustCommunicateFact(Node n, Node exp)
{
  Trace("dt-lemma-debug") << "Compute for " << exp << " => " << n << std::endl;
  bool addLemma = false;
  if (options::dtInferAsLemmas() && !exp.isConst())
  {
    // all units are lemmas
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

bool DatatypesInference::process(TheoryInferenceManager* im, bool asLemma)
{
  // check to see if we have to communicate it to the rest of the system
  if (mustCommunicateFact(d_conc, d_exp))
  {
    // send it as an (explained) lemma
    std::vector<Node> exp;
    if (!d_exp.isNull() && !d_exp.isConst())
    {
      exp.push_back(d_exp);
    }
    return im->lemmaExp(d_conc, exp, {});
  }
  // assert the internal fact
  bool polarity = d_conc.getKind() != NOT;
  TNode atom = polarity ? d_conc : d_conc[0];
  im->assertInternalFact(atom, polarity, d_exp);
  return true;
}

InferenceManager::InferenceManager(Theory& t,
                                   TheoryState& state,
                                   ProofNodeManager* pnm)
    : InferenceManagerBuffered(t, state, nullptr)
{
}

void InferenceManager::addPendingInference(Node conc,
                                           Node exp,
                                           ProofGenerator* pg)
{
  d_pendingFact.emplace_back(new DatatypesInference(conc, exp, pg));
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

}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4
