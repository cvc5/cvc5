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
 * Implementation of beta reduction node conversion
 */

#include "expr/beta_reduce_converter.h"

namespace cvc5::internal {

/** convert node n as described above during post-order traversal */
Node BetaReduceNodeConverter::postConvert(Node n)
{
  if (n.getKind() == Kind::APPLY_UF
      && n.getOperator().getKind() == Kind::LAMBDA)
  {
    Node lam = n.getOperator();
    std::vector<Node> vars(lam[0].begin(), lam[0].end());
    std::vector<Node> subs(n.begin(), n.end());
    // only reduce if arity is correct
    if (vars.size() == subs.size())
    {
      return lam[1].substitute(
          vars.begin(), vars.end(), subs.begin(), subs.end());
    }
  }
  return n;
}

}  // namespace cvc5::internal