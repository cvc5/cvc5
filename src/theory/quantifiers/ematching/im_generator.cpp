/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inst match generator base class.
 */

#include "theory/quantifiers/ematching/im_generator.h"

#include "theory/quantifiers/ematching/trigger.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

IMGenerator::IMGenerator(Env& env, Trigger* tparent)
    : EnvObj(env),
      d_tparent(tparent),
      d_qstate(tparent->d_qstate),
      d_treg(tparent->d_treg)
{
}

bool IMGenerator::sendInstantiation(std::vector<Node>& terms, InferenceId id)
{
  return d_tparent->sendInstantiation(terms, id);
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
