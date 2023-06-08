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
 * Relational match generator class.
 */

#include "theory/quantifiers/ematching/relational_match_generator.h"

#include "theory/quantifiers/term_util.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

RelationalMatchGenerator::RelationalMatchGenerator(
    Env& env, Trigger* tparent, Node rtrigger, bool hasPol, bool pol)
    : InstMatchGenerator(env, tparent, Node::null()),
      d_vindex(-1),
      d_hasPol(hasPol),
      d_pol(pol),
      d_counter(0)
{
  Assert((rtrigger.getKind() == EQUAL && rtrigger[0].getType().isRealOrInt())
         || rtrigger.getKind() == GEQ);
  Trace("relational-match-gen")
      << "Relational trigger: " << rtrigger << ", hasPol/pol = " << hasPol
      << "/" << pol << std::endl;
  for (size_t i = 0; i < 2; i++)
  {
    if (rtrigger[i].getKind() == INST_CONSTANT)
    {
      d_var = rtrigger[i];
      d_vindex = d_var.getAttribute(InstVarNumAttribute());
      d_rhs = rtrigger[1 - i];
      Assert(!quantifiers::TermUtil::hasInstConstAttr(d_rhs));
      Kind k = rtrigger.getKind();
      d_rel = (i == 0 ? k : (k == GEQ ? LEQ : k));
      break;
    }
  }
  Trace("relational-match-gen") << "...processed " << d_var << " (" << d_vindex
                                << ") " << d_rel << " " << d_rhs << std::endl;
  AlwaysAssert(!d_var.isNull())
      << "Failed to initialize RelationalMatchGenerator";
}

bool RelationalMatchGenerator::reset(Node eqc)
{
  d_counter = 0;
  return true;
}

int RelationalMatchGenerator::getNextMatch(InstMatch& m)
{
  Trace("relational-match-gen") << "getNextMatch, rel match gen" << std::endl;
  // try (up to) two different terms
  Node s;
  Node rhs = d_rhs;
  bool rmPrev = m.get(d_vindex).isNull();
  while (d_counter < 2)
  {
    bool checkPol = false;
    if (d_counter == 0)
    {
      checkPol = d_pol;
    }
    else
    {
      Assert(d_counter == 1);
      if (d_hasPol)
      {
        break;
      }
      // try the opposite polarity
      checkPol = !d_pol;
    }
    NodeManager* nm = NodeManager::currentNM();
    // falsify ( d_var <d_rel> d_rhs ) = checkPol
    s = rhs;
    if (!checkPol)
    {
      s = nm->mkNode(
          ADD,
          s,
          nm->mkConstRealOrInt(s.getType(), Rational(d_rel == GEQ ? -1 : 1)));
    }
    d_counter++;
    Trace("relational-match-gen")
        << "...try set " << s << " for " << checkPol << std::endl;
    if (m.set(d_vindex, s))
    {
      Trace("relational-match-gen") << "...success" << std::endl;
      int ret = continueNextMatch(
          m, InferenceId::QUANTIFIERS_INST_E_MATCHING_RELATIONAL);
      if (ret > 0)
      {
        Trace("relational-match-gen") << "...returned " << ret << std::endl;
        return ret;
      }
      Trace("relational-match-gen") << "...failed to gen inst" << std::endl;
      // failed
      if (rmPrev)
      {
        m.reset(d_vindex);
      }
    }
  }
  return -1;
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
