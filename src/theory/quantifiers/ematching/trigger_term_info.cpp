/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of trigger term info class.
 */

#include "theory/quantifiers/ematching/trigger_term_info.h"

#include "theory/quantifiers/term_util.h"

using namespace cvc5::kind;

namespace cvc5 {
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
  // we use both APPLY_SELECTOR and APPLY_SELECTOR_TOTAL since this
  // method is used both for trigger selection and for ground term registration,
  // where these two things require those kinds respectively.
  return k == APPLY_UF || k == SELECT || k == STORE || k == APPLY_CONSTRUCTOR
         || k == APPLY_SELECTOR || k == APPLY_SELECTOR_TOTAL
         || k == APPLY_TESTER || k == UNION || k == INTERSECTION || k == SUBSET
         || k == SETMINUS || k == MEMBER || k == SINGLETON || k == SEP_PTO
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
  if (isAtomicTrigger(n))
  {
    return 1;
  }
  return 2;
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
