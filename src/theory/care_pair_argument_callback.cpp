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
 * The care pair argument callback.
 */

#include "theory/care_pair_argument_callback.h"

namespace cvc5::internal {
namespace theory {

CarePairArgumentCallback::CarePairArgumentCallback(Theory& t) : d_theory(t) {}

bool CarePairArgumentCallback::considerPath(TNode a, TNode b)
{
  // builtin cases for when a is clearly equal/disequal to b
  if (a == b)
  {
    return true;
  }
  if (a.isConst() && b.isConst())
  {
    return false;
  }
  // interested in finding pairs that are not disequal
  return !d_theory.areCareDisequal(a, b);
}

void CarePairArgumentCallback::processData(TNode fa, TNode fb)
{
  d_theory.processCarePairArgs(fa, fb);
}

}  // namespace theory
}  // namespace cvc5::internal
