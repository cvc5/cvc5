/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the solver state of the theory of strings.
 */

#include "theory/strings/solver_state.h"

#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "util/rational.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

SolverState::SolverState(Env& env, Valuation& v)
    : TheoryState(env, v),
      d_eeDisequalities(env.getContext()),
      d_pendingConflictSet(env.getContext(), false),
      d_pendingConflict(InferenceId::UNKNOWN)
{
  d_zero = NodeManager::currentNM()->mkConstInt(Rational(0));
  d_false = NodeManager::currentNM()->mkConst(false);
}

SolverState::~SolverState()
{
  for (std::pair<const Node, EqcInfo*>& it : d_eqcInfo)
  {
    delete it.second;
  }
}

const context::CDList<Node>& SolverState::getDisequalityList() const
{
  return d_eeDisequalities;
}

void SolverState::addDisequality(TNode t1, TNode t2)
{
  d_eeDisequalities.push_back(t1.eqNode(t2));
}

EqcInfo* SolverState::getOrMakeEqcInfo(Node eqc, bool doMake)
{
  std::map<Node, EqcInfo*>::iterator eqc_i = d_eqcInfo.find(eqc);
  if (eqc_i != d_eqcInfo.end())
  {
    return eqc_i->second;
  }
  if (doMake)
  {
    EqcInfo* ei = new EqcInfo(d_env.getContext());
    d_eqcInfo[eqc] = ei;
    return ei;
  }
  return nullptr;
}

TheoryModel* SolverState::getModel() { return d_valuation.getModel(); }

Node SolverState::getLengthExp(Node t, std::vector<Node>& exp, Node te)
{
  Assert(areEqual(t, te));
  Node lt = NodeManager::currentNM()->mkNode(STRING_LENGTH, t);
  lt = rewrite(lt);
  if (hasTerm(lt))
  {
    // use own length if it exists, leads to shorter explanation
    return lt;
  }
  EqcInfo* ei = getOrMakeEqcInfo(t, false);
  Node lengthTerm = ei ? ei->d_lengthTerm : Node::null();
  if (lengthTerm.isNull())
  {
    // typically shouldnt be necessary
    lengthTerm = t;
  }
  else
  {
    lengthTerm = lengthTerm[0];
  }
  Trace("strings") << "SolverState::getLengthTerm " << t << " is " << lengthTerm
                   << std::endl;
  if (te != lengthTerm)
  {
    exp.push_back(te.eqNode(lengthTerm));
  }
  return rewrite(NodeManager::currentNM()->mkNode(STRING_LENGTH, lengthTerm));
}

Node SolverState::getLength(Node t, std::vector<Node>& exp)
{
  return getLengthExp(t, exp, t);
}

Node SolverState::explainNonEmpty(Node s)
{
  Assert(s.getType().isStringLike());
  Node emp = Word::mkEmptyWord(s.getType());
  if (areDisequal(s, emp))
  {
    return s.eqNode(emp).negate();
  }
  Node sLen = NodeManager::currentNM()->mkNode(STRING_LENGTH, s);
  sLen = rewrite(sLen);
  if (areDisequal(sLen, d_zero))
  {
    return sLen.eqNode(d_zero).negate();
  }
  return Node::null();
}

bool SolverState::isEqualEmptyWord(Node s, Node& emps)
{
  Node sr = getRepresentative(s);
  if (sr.isConst())
  {
    if (Word::getLength(sr) == 0)
    {
      emps = sr;
      return true;
    }
  }
  return false;
}

void SolverState::setPendingMergeConflict(Node conf, InferenceId id)
{
  if (d_pendingConflictSet.get())
  {
    // already set conflict
    return;
  }
  InferInfo iiPrefixConf(id);
  iiPrefixConf.d_conc = d_false;
  utils::flattenOp(AND, conf, iiPrefixConf.d_premises);
  setPendingConflict(iiPrefixConf);
}

void SolverState::setPendingConflict(InferInfo& ii)
{
  if (!d_pendingConflictSet.get())
  {
    d_pendingConflict = ii;
    d_pendingConflictSet.set(true);
  }
}

bool SolverState::hasPendingConflict() const { return d_pendingConflictSet; }

bool SolverState::getPendingConflict(InferInfo& ii) const
{
  if (d_pendingConflictSet)
  {
    ii = d_pendingConflict;
    return true;
  }
  return false;
}

std::pair<bool, Node> SolverState::entailmentCheck(options::TheoryOfMode mode,
                                                   TNode lit)
{
  return d_valuation.entailmentCheck(mode, lit);
}

void SolverState::separateByLength(
    const std::vector<Node>& n,
    std::map<TypeNode, std::vector<std::vector<Node>>>& cols,
    std::map<TypeNode, std::vector<Node>>& lts)
{
  unsigned leqc_counter = 0;
  // map (length, type) to an equivalence class identifier
  std::map<std::pair<Node, TypeNode>, unsigned> eqc_to_leqc;
  // backwards map
  std::map<unsigned, std::pair<Node, TypeNode>> leqc_to_eqc;
  // Collection of eqc for each identifier. Notice that some identifiers may
  // not have an associated length in the mappings above, if the length of
  // an equivalence class is unknown.
  std::map<unsigned, std::vector<Node> > eqc_to_strings;
  for (const Node& eqc : n)
  {
    Assert(d_ee->getRepresentative(eqc) == eqc);
    TypeNode tnEqc = eqc.getType();
    EqcInfo* ei = getOrMakeEqcInfo(eqc, false);
    Node lt = ei ? ei->d_lengthTerm : Node::null();
    if (!lt.isNull())
    {
      Node r = d_ee->getRepresentative(lt);
      std::pair<Node, TypeNode> lkey(r, tnEqc);
      if (eqc_to_leqc.find(lkey) == eqc_to_leqc.end())
      {
        eqc_to_leqc[lkey] = leqc_counter;
        leqc_to_eqc[leqc_counter] = lkey;
        leqc_counter++;
      }
      eqc_to_strings[eqc_to_leqc[lkey]].push_back(eqc);
    }
    else
    {
      eqc_to_strings[leqc_counter].push_back(eqc);
      leqc_counter++;
    }
  }
  for (const std::pair<const unsigned, std::vector<Node> >& p : eqc_to_strings)
  {
    Assert(!p.second.empty());
    // get the type of the collection
    TypeNode stn = p.second[0].getType();
    cols[stn].emplace_back(p.second.begin(), p.second.end());
    lts[stn].push_back(leqc_to_eqc[p.first].first);
  }
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
