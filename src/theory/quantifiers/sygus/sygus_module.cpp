/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of sygus_module.
 */

#include "theory/quantifiers/sygus/sygus_module.h"

#include "theory/quantifiers/quantifiers_state.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SygusModule::SygusModule(Env& env,
                         QuantifiersState& qs,
                         QuantifiersInferenceManager& qim,
                         TermDbSygus* tds,
                         SynthConjecture* p)
    : EnvObj(env), d_qstate(qs), d_qim(qim), d_tds(tds), d_parent(p)
{
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
