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

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace inst {


RelationalMatchGenerator::RelationalMatchGenerator(Trigger* tparent, Node rtrigger, bool hasPol, bool pol) : d_relTrigger(rtrigger), d_hasPol(hasPol), d_pol(pol), d_counter(0){}

bool RelationalMatchGenerator::reset(Node eqc)
{
  d_counter = 0;
  return true;
}

int RelationalMatchGenerator::getNextMatch(Node q, InstMatch& m)
{
  
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

