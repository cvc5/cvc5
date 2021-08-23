/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Relational match generator class.
 */

#include "theory/quantifiers/ematching/relational_match_generator.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace inst {

RelationalMatchGenerator::RelationalMatchGenerator(Trigger* tparent,
                                                   Node rtrigger,
                                                   bool hasPol,
                                                   bool pol)
    : InstMatchGenerator(tparent, Node::null()),
      d_relTrigger(rtrigger),
      d_hasPol(hasPol),
      d_pol(pol),
      d_counter(0)
{
  Assert((rtrigger.getKind() == EQUAL && rtrigger[0].getType().isReal())
         || rtrigger.getKind() == GEQ);
  for (size_t i = 0; i < 2; i++)
  {
    if (rtrigger[i].getKind() == INST_CONSTANT)
    {
      d_var = rtrigger[i];
      d_rhs = rtrigger[1 - i];
      Kind k = rtrigger d_rel = (i == 0 ? k : (k == GEQ ? LEQ : k));
    }
  }
  AlwaysAssert(!d_var.isNull())
      << "Failed to initialize RelationalMatchGenerator";
}

bool RelationalMatchGenerator::reset(Node eqc)
{
  d_counter = 0;
  return true;
}

int RelationalMatchGenerator::getNextMatch(Node q, InstMatch& m)
{
  bool checkPol = false;
  if (d_counter == 0)
  {
    checkPol = d_pol;
  }
  else if (d_counter == 1)
  {
    if (!d_hasPol)
    {
      return -1;
    }
    checkPol = !d_pol;
  }
  else
  {
    return -1;
  }
  // falsify ( d_var <d_rel> d_rhs ) = checkPol

  return -1;
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
