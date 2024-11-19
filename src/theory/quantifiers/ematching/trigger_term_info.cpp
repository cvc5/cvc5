/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of trigger term info class.
 */

#include "theory/quantifiers/ematching/trigger_term_info.h"

#include "theory/quantifiers/term_util.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

void TriggerTermInfo::init(Node q, Node n, int reqPol, Node reqPolEq)
{
  if (d_fv.empty())
  {
    quantifiers::TermUtil::computeInstConstContainsForQuant(q, n, d_fv);
  }
  if (d_reqPol == 0)
  {
    d_reqPol = reqPol;
    d_reqPolEq = reqPolEq;
  }
  else
  {
    // determined a ground (dis)equality must hold or else q is a tautology?
  }
  d_weight = getTriggerWeight(n);
}

bool TriggerTermInfo::isAtomicTrigger(Node n)
{
  return isAtomicTriggerKind(n.getKind());
}

bool TriggerTermInfo::isAtomicTriggerKind(Kind k)
{
  return k == Kind::APPLY_UF || k == Kind::SELECT || k == Kind::STORE
         || k == Kind::APPLY_CONSTRUCTOR || k == Kind::APPLY_SELECTOR
         || k == Kind::APPLY_TESTER || k == Kind::SET_UNION
         || k == Kind::SET_INTER || k == Kind::SET_SUBSET
         || k == Kind::SET_MINUS || k == Kind::SET_MEMBER
         || k == Kind::SET_SINGLETON || k == Kind::SEP_PTO
         || k == Kind::BITVECTOR_TO_NAT || k == Kind::INT_TO_BITVECTOR
         || k == Kind::HO_APPLY || k == Kind::STRING_LENGTH
         || k == Kind::SEQ_NTH;
}

bool TriggerTermInfo::isRelationalTrigger(Node n)
{
  return isRelationalTriggerKind(n.getKind());
}

bool TriggerTermInfo::isRelationalTriggerKind(Kind k)
{
  return k == Kind::EQUAL || k == Kind::GEQ;
}

bool TriggerTermInfo::isUsableRelationTrigger(Node n)
{
  bool hasPol, pol;
  Node lit;
  return isUsableRelationTrigger(n, hasPol, pol, lit);
}
bool TriggerTermInfo::isUsableRelationTrigger(Node n,
                                              bool& hasPol,
                                              bool& pol,
                                              Node& lit)
{
  // relational triggers (not) (= (~ x t) true|false), where ~ in { =, >= }.
  hasPol = false;
  pol = n.getKind() != Kind::NOT;
  lit = pol ? n : n[0];
  if (lit.getKind() == Kind::EQUAL && lit[1].getType().isBoolean()
      && lit[1].isConst())
  {
    hasPol = true;
    pol = lit[1].getConst<bool>() ? pol : !pol;
    lit = lit[0];
  }
  // is it a relational trigger?
  if ((lit.getKind() == Kind::EQUAL && lit[0].getType().isRealOrInt())
      || lit.getKind() == Kind::GEQ)
  {
    // if one side of the relation is a variable and the other side is a ground
    // term, we can treat this using the relational match generator
    for (size_t i = 0; i < 2; i++)
    {
      if (lit[i].getKind() == Kind::INST_CONSTANT
          && !quantifiers::TermUtil::hasInstConstAttr(lit[1 - i]))
      {
        return true;
      }
    }
  }
  return false;
}

bool TriggerTermInfo::isSimpleTrigger(Node n)
{
  Node t = n.getKind() == Kind::NOT ? n[0] : n;
  if (t.getKind() == Kind::EQUAL)
  {
    if (!quantifiers::TermUtil::hasInstConstAttr(t[1]))
    {
      t = t[0];
    }
  }
  if (!isAtomicTrigger(t))
  {
    return false;
  }
  for (const Node& tc : t)
  {
    if (tc.getKind() != Kind::INST_CONSTANT
        && quantifiers::TermUtil::hasInstConstAttr(tc))
    {
      return false;
    }
  }
  if (t.getKind() == Kind::HO_APPLY && t[0].getKind() == Kind::INST_CONSTANT)
  {
    return false;
  }
  return true;
}

int32_t TriggerTermInfo::getTriggerWeight(Node n)
{
  if (n.getKind() == Kind::APPLY_UF)
  {
    return 0;
  }
  if (isAtomicTrigger(n) || isUsableRelationTrigger(n))
  {
    return 1;
  }
  return 2;
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
