/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Preregister relevant formulas
 */

#include "prop/preregister_rlv.h"

namespace cvc5::internal {
namespace prop {

PreregisterRlv::PreregisterRlv(Env& env) : EnvObj(env) {}

PreregisterRlv::~PreregisterRlv() {}

void PreregisterRlv::notifyFormula(TNode n, std::vector<Node>& toPreregister)
{
}

void PreregisterRlv::notifyCheck(std::vector<Node>& toPreregister)
{
}

}  // namespace prop
}  // namespace cvc5::internal

