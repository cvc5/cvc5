/*********************                                                        */
/*! \file inference_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the inference manager for the theory of sets
 **/

#include "theory/sets/inference_manager.h"

#include "options/sets_options.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sets {

InferenceManager::InferenceManager(Theory& t,
                                   SolverState& s,
                                   ProofNodeManager* pnm)
    : InferenceManagerBuffered(t, s, pnm), d_state(s)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

bool InferenceManager::assertFactRec(Node fact, Node exp, int inferType)
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
    addPendingLemma(lem);
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
      conflict(exp);
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
      bool tret = assertFactRec(factc, exp, inferType);
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
    if (assertInternalFact(atom, polarity, exp))
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
    addPendingLemma(lem);
    return true;
  }
  return false;
}
void InferenceManager::assertInference(Node fact,
                                       Node exp,
                                       const char* c,
                                       int inferType)
{
  if (assertFactRec(fact, exp, inferType))
  {
    Trace("sets-lemma") << "Sets::Lemma : " << fact << " from " << exp << " by "
                        << c << std::endl;
    Trace("sets-assertion")
        << "(assert (=> " << exp << " " << fact << ")) ; by " << c << std::endl;
  }
}

void InferenceManager::assertInference(Node fact,
                                       std::vector<Node>& exp,
                                       const char* c,
                                       int inferType)
{
  Node exp_n = exp.empty() ? d_true
                           : (exp.size() == 1
                                  ? exp[0]
                                  : NodeManager::currentNM()->mkNode(AND, exp));
  assertInference(fact, exp_n, c, inferType);
}

void InferenceManager::assertInference(std::vector<Node>& conc,
                                       Node exp,
                                       const char* c,
                                       int inferType)
{
  if (!conc.empty())
  {
    Node fact = conc.size() == 1 ? conc[0]
                                 : NodeManager::currentNM()->mkNode(AND, conc);
    assertInference(fact, exp, c, inferType);
  }
}
void InferenceManager::assertInference(std::vector<Node>& conc,
                                       std::vector<Node>& exp,
                                       const char* c,
                                       int inferType)
{
  Node exp_n = exp.empty() ? d_true
                           : (exp.size() == 1
                                  ? exp[0]
                                  : NodeManager::currentNM()->mkNode(AND, exp));
  assertInference(conc, exp_n, c, inferType);
}

void InferenceManager::split(Node n, int reqPol)
{
  n = Rewriter::rewrite(n);
  Node lem = NodeManager::currentNM()->mkNode(OR, n, n.negate());
  // send the lemma
  lemma(lem);
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
}  // namespace CVC4
