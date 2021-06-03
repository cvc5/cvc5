/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the inference manager for the theory of sets.
 */

#include "theory/sets/inference_manager.h"

#include "options/sets_options.h"
#include "theory/rewriter.h"

using namespace std;
using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace sets {

InferenceManager::InferenceManager(Theory& t,
                                   SolverState& s,
                                   ProofNodeManager* pnm)
    : InferenceManagerBuffered(t, s, pnm, "theory::sets::"), d_state(s)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

bool InferenceManager::assertFactRec(Node fact, InferenceId id, Node exp, int inferType)
{
  // should we send this fact out as a lemma?
  if ((options::setsInferAsLemmas() && inferType != -1) || inferType == 1)
  {
    if (d_state.isEntailed(fact, true))
    {
      return false;
    }
    Node lem = fact;
    if (exp != d_true)
    {
      lem = NodeManager::currentNM()->mkNode(IMPLIES, exp, fact);
    }
    addPendingLemma(lem, id);
    return true;
  }
  Trace("sets-fact") << "Assert fact rec : " << fact << ", exp = " << exp
                     << std::endl;
  if (fact.isConst())
  {
    // either trivial or a conflict
    if (fact == d_false)
    {
      Trace("sets-lemma") << "Conflict : " << exp << std::endl;
      conflict(exp, id);
      return true;
    }
    return false;
  }
  else if (fact.getKind() == AND
           || (fact.getKind() == NOT && fact[0].getKind() == OR))
  {
    bool ret = false;
    Node f = fact.getKind() == NOT ? fact[0] : fact;
    for (unsigned i = 0; i < f.getNumChildren(); i++)
    {
      Node factc = fact.getKind() == NOT ? f[i].negate() : f[i];
      bool tret = assertFactRec(factc, id, exp, inferType);
      ret = ret || tret;
      if (d_state.isInConflict())
      {
        return true;
      }
    }
    return ret;
  }
  bool polarity = fact.getKind() != NOT;
  TNode atom = polarity ? fact : fact[0];
  if (d_state.isEntailed(atom, polarity))
  {
    return false;
  }
  // things we can assert to equality engine
  if (atom.getKind() == MEMBER
      || (atom.getKind() == EQUAL && atom[0].getType().isSet()))
  {
    // send to equality engine
    if (assertInternalFact(atom, polarity, id, exp))
    {
      // return true if this wasn't redundant
      return true;
    }
  }
  else
  {
    // must send as lemma
    Node lem = fact;
    if (exp != d_true)
    {
      lem = NodeManager::currentNM()->mkNode(IMPLIES, exp, fact);
    }
    addPendingLemma(lem, id);
    return true;
  }
  return false;
}
void InferenceManager::assertInference(Node fact,
                                       InferenceId id,
                                       Node exp,
                                       int inferType)
{
  if (assertFactRec(fact, id, exp, inferType))
  {
    Trace("sets-lemma") << "Sets::Lemma : " << fact << " from " << exp << " by "
                        << id << std::endl;
    Trace("sets-assertion") << "(assert (=> " << exp << " " << fact
                            << ")) ; by " << id << std::endl;
  }
}

void InferenceManager::assertInference(Node fact,
                                       InferenceId id,
                                       std::vector<Node>& exp,
                                       int inferType)
{
  Node exp_n = exp.empty() ? d_true
                           : (exp.size() == 1
                                  ? exp[0]
                                  : NodeManager::currentNM()->mkNode(AND, exp));
  assertInference(fact, id, exp_n, inferType);
}

void InferenceManager::assertInference(std::vector<Node>& conc,
                                       InferenceId id,
                                       Node exp,
                                       int inferType)
{
  if (!conc.empty())
  {
    Node fact = conc.size() == 1 ? conc[0]
                                 : NodeManager::currentNM()->mkNode(AND, conc);
    assertInference(fact, id, exp, inferType);
  }
}
void InferenceManager::assertInference(std::vector<Node>& conc,
                                       InferenceId id,
                                       std::vector<Node>& exp,
                                       int inferType)
{
  Node exp_n = exp.empty() ? d_true
                           : (exp.size() == 1
                                  ? exp[0]
                                  : NodeManager::currentNM()->mkNode(AND, exp));
  assertInference(conc, id, exp_n, inferType);
}

void InferenceManager::split(Node n, InferenceId id, int reqPol)
{
  n = Rewriter::rewrite(n);
  Node lem = NodeManager::currentNM()->mkNode(OR, n, n.negate());
  // send the lemma
  lemma(lem, id);
  Trace("sets-lemma") << "Sets::Lemma split : " << lem << std::endl;
  if (reqPol != 0)
  {
    Trace("sets-lemma") << "Sets::Require phase " << n << " " << (reqPol > 0)
                        << std::endl;
    requirePhase(n, reqPol > 0);
  }
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5
