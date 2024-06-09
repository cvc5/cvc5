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
 * Rewrite database singleton elimination converter.
 */

#include "rewriter/singleton_elim_process.h"

namespace cvc5::internal {
namespace rewriter {

SingletonElimConverter::SingletonElimConverter(Env& env) : d_tpg(env, nullptr)
{
}

std::shared_ptr<ProofNode> SingletonElimConverter::convert(const Node& n, const Node& nse)
{
  // TODO

  Node eq = n.eqNode(nse);
  return d_tpg.getProofFor(eq);
}


}  // namespace rewriter
}  // namespace cvc5::internal

