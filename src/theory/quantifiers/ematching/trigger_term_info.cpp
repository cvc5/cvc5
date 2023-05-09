/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  return k == APPLY_UF || k == SELECT || k == STORE || k == APPLY_CONSTRUCTOR
         || k == APPLY_SELECTOR || k == APPLY_TESTER || k == SET_UNION
         || k == SET_INTER || k == SET_SUBSET || k == SET_MINUS
         || k == SET_MEMBER || k == SET_SINGLETON || k == SEP_PTO
         || k == BITVECTOR_TO_NAT || k == INT_TO_BITVECTOR || k == HO_APPLY
         || k == STRING_LENGTH || k == SEQ_NTH;
}

bool TriggerTermInfo::isRelationalTrigger(Node n)
{
  return isRelationalTriggerKind(n.getKind());
}

bool TriggerTermInfo::isRelationalTriggerKind(Kind k)
{
  return k == EQUAL || k == GEQ;
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
  pol = n.getKind() != NOT;
  lit = pol ? n : n[0];
  if (lit.getKind() == EQUAL && lit[1].getType().isBoolean()
      && lit[1].isConst())
  {
    hasPol = true;
    pol = lit[1].getConst<bool>() ? pol : !pol;
    lit = lit[0];
  }
  // is it a relational trigger?
  if ((lit.getKind() == EQUAL && lit[0].getType().isRealOrInt())
      || lit.getKind() == GEQ)
  {
    // if one side of the relation is a variable and the other side is a ground
    // term, we can treat this using the relational match generator
    for (size_t i = 0; i < 2; i++)
    {
      if (lit[i].getKind() == INST_CONSTANT
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
  Node t = n.getKind() == NOT ? n[0] : n;
  if (t.getKind() == EQUAL)
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
    if (tc.getKind() != INST_CONSTANT
        && quantifiers::TermUtil::hasInstConstAttr(tc))
    {
      return false;
    }
  }
  if (t.getKind() == HO_APPLY && t[0].getKind() == INST_CONSTANT)
  {
    return false;
  }
  return true;
}

int32_t TriggerTermInfo::getTriggerWeight(Node n)
{
  if (n.getKind() == APPLY_UF)
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
