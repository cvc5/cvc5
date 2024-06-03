/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of witness elimination node conversion
 */

#include "expr/elim_witness_converter.h"

namespace cvc5::internal {

  ElimWitnessNodeConverter::ElimWitnessNodeConverter(Env& env) : EnvObj(env), NodeConverter(nodeManager()){}

  Node ElimWitnessNodeConverter::postConvert(Node n)
  {
    return n;
  }
  const std::vector<Node>& ElimWitnessNodeConverter::getExistentials() const
  { return d_exists; }

}  // namespace cvc5::internal

