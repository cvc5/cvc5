/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of utils for counterexample-guided quantifier instantiation.
 */

#include "theory/quantifiers/cegqi/ceg_utils.h"

#include "theory/arith/arith_utilities.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

CegTermType mkStrictCTT(CegTermType c)
{
  Assert(!isStrictCTT(c));
  if (c == CEG_TT_LOWER)
  {
    return CEG_TT_LOWER_STRICT;
  }
  else if (c == CEG_TT_UPPER)
  {
    return CEG_TT_UPPER_STRICT;
  }
  return c;
}

CegTermType mkNegateCTT(CegTermType c)
{
  if (c == CEG_TT_LOWER)
  {
    return CEG_TT_UPPER;
  }
  else if (c == CEG_TT_UPPER)
  {
    return CEG_TT_LOWER;
  }
  else if (c == CEG_TT_LOWER_STRICT)
  {
    return CEG_TT_UPPER_STRICT;
  }
  else if (c == CEG_TT_UPPER_STRICT)
  {
    return CEG_TT_LOWER_STRICT;
  }
  return c;
}
bool isStrictCTT(CegTermType c)
{
  return c == CEG_TT_LOWER_STRICT || c == CEG_TT_UPPER_STRICT;
}
bool isLowerBoundCTT(CegTermType c)
{
  return c == CEG_TT_LOWER || c == CEG_TT_LOWER_STRICT;
}
bool isUpperBoundCTT(CegTermType c)
{
  return c == CEG_TT_UPPER || c == CEG_TT_UPPER_STRICT;
}

std::ostream& operator<<(std::ostream& os, CegInstEffort e)
{
  switch (e)
  {
    case CEG_INST_EFFORT_NONE: os << "?"; break;
    case CEG_INST_EFFORT_STANDARD: os << "STANDARD"; break;
    case CEG_INST_EFFORT_STANDARD_MV: os << "STANDARD_MV"; break;
    case CEG_INST_EFFORT_FULL: os << "FULL"; break;
    default: Unreachable();
  }
  return os;
}

std::ostream& operator<<(std::ostream& os, CegInstPhase phase)
{
  switch (phase)
  {
    case CEG_INST_PHASE_NONE: os << "?"; break;
    case CEG_INST_PHASE_EQC: os << "eqc"; break;
    case CEG_INST_PHASE_EQUAL: os << "eq"; break;
    case CEG_INST_PHASE_ASSERTION: os << "as"; break;
    case CEG_INST_PHASE_MVALUE: os << "mv"; break;
    default: Unreachable();
  }
  return os;
}
std::ostream& operator<<(std::ostream& os, CegHandledStatus status)
{
  switch (status)
  {
    case CEG_UNHANDLED: os << "unhandled"; break;
    case CEG_PARTIALLY_HANDLED: os << "partially_handled"; break;
    case CEG_HANDLED: os << "handled"; break;
    case CEG_HANDLED_UNCONDITIONAL: os << "handled_unc"; break;
    default: Unreachable();
  }
  return os;
}

void TermProperties::composeProperty(TermProperties& p)
{
  if (p.d_coeff.isNull())
  {
    return;
  }
  if (d_coeff.isNull())
  {
    d_coeff = p.d_coeff;
  }
  else
  {
    d_coeff = arith::multConstants(d_coeff, p.d_coeff);
  }
}

// push the substitution pv_prop.getModifiedTerm(pv) -> n
void SolvedForm::push_back(Node pv, Node n, TermProperties& pv_prop)
{
  Assert(n.getType() == pv.getType());
  d_vars.push_back(pv);
  d_subs.push_back(n);
  d_props.push_back(pv_prop);
  if (pv_prop.isBasic())
  {
    return;
  }
  d_non_basic.push_back(pv);
  // update theta value
  Node new_theta = getTheta();
  if (new_theta.isNull())
  {
    new_theta = pv_prop.d_coeff;
  }
  else
  {
    new_theta = arith::multConstants(new_theta, pv_prop.d_coeff);
  }
  d_theta.push_back(new_theta);
}
// pop the substitution pv_prop.getModifiedTerm(pv) -> n
void SolvedForm::pop_back(Node pv, Node n, TermProperties& pv_prop)
{
  d_vars.pop_back();
  d_subs.pop_back();
  d_props.pop_back();
  if (pv_prop.isBasic())
  {
    return;
  }
  d_non_basic.pop_back();
  // update theta value
  d_theta.pop_back();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
