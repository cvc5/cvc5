/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of instantiator for counterexample-guided quantifier instantiation.
 */

#include "theory/quantifiers/cegqi/instantiator.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

Instantiator::Instantiator(Env& env, TypeNode tn) : EnvObj(env), d_type(tn)
{
  d_closed_enum_type = tn.isClosedEnumerable();
}

bool Instantiator::processEqualTerm(CegInstantiator* ci,
                                    SolvedForm& sf,
                                    Node pv,
                                    TermProperties& pv_prop,
                                    Node n,
                                    CegInstEffort effort)
{
  pv_prop.d_type = CEG_TT_EQUAL;
  return ci->constructInstantiationInc(pv, n, pv_prop, sf);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
