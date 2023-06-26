/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of higher-order term database class.
 */

#include "theory/quantifiers/ho_term_database.h"

#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/rewriter.h"
#include "theory/uf/equality_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

HoTermDb::HoTermDb(Env& env, QuantifiersState& qs, QuantifiersRegistry& qr)
    : TermDb(env, qs, qr)
{
}

HoTermDb::~HoTermDb() {}

void HoTermDb::addTermInternal(Node n)
{
  if (n.getType().isFunction())
  {
    // nothing special to do with functions
    return;
  }
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Node curr = n;
  std::vector<Node> args;
  while (curr.getKind() == HO_APPLY)
  {
    args.insert(args.begin(), curr[1]);
    curr = curr[0];
    if (!curr.isVar())
    {
      // purify the term
      std::map<Node, Node>::iterator itp = d_hoFunOpPurify.find(curr);
      Node psk;
      if (itp == d_hoFunOpPurify.end())
      {
        psk = sm->mkPurifySkolem(curr);
        d_hoFunOpPurify[curr] = psk;
        // we do not add it to d_ops since it is an internal operator
      }
      else
      {
        psk = itp->second;
      }
      std::vector<Node> children;
      children.push_back(psk);
      children.insert(children.end(), args.begin(), args.end());
      Node p_n = nm->mkNode(APPLY_UF, children);
      Trace("term-db") << "register term in db (via purify) " << p_n
                       << std::endl;
      // also add this one internally
      DbList* dblp = getOrMkDbListForOp(psk);
      dblp->d_list.push_back(p_n);
      // maintain backwards mapping
      d_hoPurifyToTerm[p_n] = n;
    }
  }
  if (!args.empty() && curr.isVar())
  {
    // also add standard application version
    args.insert(args.begin(), curr);
    Node uf_n = nm->mkNode(APPLY_UF, args);
    addTerm(uf_n);
  }
}

void HoTermDb::getOperatorsFor(TNode f, std::vector<TNode>& ops)
{
  ops.push_back(f);
  ops.insert(ops.end(), d_hoOpSlaves[f].begin(), d_hoOpSlaves[f].end());
}

Node HoTermDb::getOperatorRepresentative(TNode op) const
{
  std::map<TNode, TNode>::const_iterator it = d_hoOpRep.find(op);
  if (it != d_hoOpRep.end())
  {
    return it->second;
  }
  return op;
}

bool HoTermDb::resetInternal(Theory::Effort effort)
{
  Trace("quant-ho")
      << "HoTermDb::reset : assert higher-order purify equalities..."
      << std::endl;
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  for (std::pair<const Node, Node>& pp : d_hoPurifyToTerm)
  {
    if (ee->hasTerm(pp.second)
        && (!ee->hasTerm(pp.first) || !ee->areEqual(pp.second, pp.first)))
    {
      Node eq;
      std::map<Node, Node>::iterator itpe = d_hoPurifyToEq.find(pp.first);
      if (itpe == d_hoPurifyToEq.end())
      {
        eq = rewrite(pp.first.eqNode(pp.second));
        d_hoPurifyToEq[pp.first] = eq;
      }
      else
      {
        eq = itpe->second;
      }
      Trace("quant-ho") << "- assert purify equality : " << eq << std::endl;
      // Note that ee may be the central equality engine, in which case this
      // equality is explained trivially with "true", since both sides of
      // eq are HOL and FOL encodings of the same thing.
      ee->assertEquality(eq, true, d_true);
      if (!ee->consistent())
      {
        // In some rare cases, purification functions (in the domain of
        // d_hoPurifyToTerm) may escape the term database. For example,
        // matching algorithms may construct instantiations involving these
        // functions. As a result, asserting these equalities internally may
        // cause a conflict. In this case, we insist that the purification
        // equality is sent out as a lemma here.
        Trace("term-db-lemma") << "Purify equality lemma: " << eq << std::endl;
        d_qim->addPendingLemma(eq, InferenceId::QUANTIFIERS_HO_PURIFY);
        d_qstate.notifyInConflict();
        d_consistent_ee = false;
        return false;
      }
    }
  }
  return true;
}

bool HoTermDb::finishResetInternal(Theory::Effort effort)
{
  if (!options().quantifiers.hoMergeTermDb)
  {
    return true;
  }
  Trace("quant-ho") << "HoTermDb::reset : compute equal functions..."
                    << std::endl;
  // build operator representative map
  d_hoOpRep.clear();
  d_hoOpSlaves.clear();
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
  while (!eqcs_i.isFinished())
  {
    TNode r = (*eqcs_i);
    if (r.getType().isFunction())
    {
      Trace("quant-ho") << "  process function eqc " << r << std::endl;
      Node first;
      eq::EqClassIterator eqc_i = eq::EqClassIterator(r, ee);
      while (!eqc_i.isFinished())
      {
        TNode n = (*eqc_i);
        Node n_use;
        if (n.isVar())
        {
          n_use = n;
        }
        else
        {
          // use its purified variable, if it exists
          std::map<Node, Node>::iterator itp = d_hoFunOpPurify.find(n);
          if (itp != d_hoFunOpPurify.end())
          {
            n_use = itp->second;
          }
        }
        Trace("quant-ho") << "  - process " << n_use << ", from " << n
                          << std::endl;
        if (!n_use.isNull() && d_opMap.find(n_use) != d_opMap.end())
        {
          if (first.isNull())
          {
            first = n_use;
            d_hoOpRep[n_use] = n_use;
          }
          else
          {
            Trace("quant-ho") << "  have : " << n_use << " == " << first
                              << ", type = " << n_use.getType() << std::endl;
            d_hoOpRep[n_use] = first;
            d_hoOpSlaves[first].push_back(n_use);
          }
        }
        ++eqc_i;
      }
    }
    ++eqcs_i;
  }
  Trace("quant-ho") << "...finished compute equal functions." << std::endl;

  return true;
}
bool HoTermDb::checkCongruentDisequal(TNode a, TNode b, std::vector<Node>& exp)
{
  if (!d_qstate.areDisequal(a, b))
  {
    return false;
  }
  exp.push_back(a.eqNode(b));
  // operators might be disequal
  Node af = getMatchOperator(a);
  Node bf = getMatchOperator(b);
  if (af != bf)
  {
    if (a.getKind() == APPLY_UF && b.getKind() == APPLY_UF)
    {
      exp.push_back(af.eqNode(bf).negate());
    }
    else
    {
      Assert(false);
      return false;
    }
  }
  return true;
}

Node HoTermDb::getHoTypeMatchPredicate(TypeNode tn)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  TypeNode ptn = nm->mkFunctionType(tn, nm->booleanType());
  return sm->mkSkolemFunction(SkolemFunId::HO_TYPE_MATCH_PRED, ptn);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
