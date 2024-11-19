/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
    : TermDb(env, qs, qr), d_hoFunOpPurify(userContext())
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
  while (curr.getKind() == Kind::HO_APPLY)
  {
    args.insert(args.begin(), curr[1]);
    curr = curr[0];
    if (!curr.isVar())
    {
      // purify the term
      context::CDHashSet<Node>::const_iterator itp = d_hoFunOpPurify.find(curr);
      if (itp != d_hoFunOpPurify.end())
      {
        continue;
      }
      d_hoFunOpPurify.insert(curr);
      Node psk = sm->mkPurifySkolem(curr);
      // we do not add it to d_ops since it is an internal operator
      Node eq = psk.eqNode(curr);
      std::vector<Node> children;
      children.push_back(psk);
      children.insert(children.end(), args.begin(), args.end());
      Node p_n = nm->mkNode(Kind::APPLY_UF, children);
      Node eqa = p_n.eqNode(n);
      Node lem = nm->mkNode(Kind::AND, eq, eqa);
      d_qim->addPendingLemma(lem, InferenceId::QUANTIFIERS_HO_PURIFY);
    }
  }
  if (!args.empty() && curr.isVar())
  {
    // also add standard application version
    args.insert(args.begin(), curr);
    Node uf_n = nm->mkNode(Kind::APPLY_UF, args);
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
    if (a.getKind() == Kind::APPLY_UF && b.getKind() == Kind::APPLY_UF)
    {
      exp.push_back(af.eqNode(bf).negate());
      Assert(d_qstate.areEqual(af, bf))
          << af << " and " << bf << " are not equal";
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
  return sm->mkInternalSkolemFunction(InternalSkolemId::HO_TYPE_MATCH_PRED,
                                      ptn);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
