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
 * Common functions for dealing with proof nodes.
 */

#include "theory/arith/arith_proof_utilities.h"

#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

std::vector<Node> getMacroSumUbCoeff(const std::vector<Pf>& pfs,
                                     const std::vector<Node>& coeffs)
{
  Assert(pfs.size() == coeffs.size());
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> ret;
  TypeNode itype = nm->integerType();
  TypeNode rtype = nm->realType();
  // For each coefficient, we must use a real if the lhs or rhs of the relation
  // is a real, or if the coefficient is not integral.
  for (size_t i = 0, ncoeff = coeffs.size(); i < ncoeff; i++)
  {
    Assert(coeffs[i].isConst());
    Node res = pfs[i]->getResult();
    Assert(res.getType().isBoolean() && res.getNumChildren() == 2);
    const Rational& r = coeffs[i].getConst<Rational>();
    bool isReal = !r.isIntegral() || res[0].getType().isReal()
                  || res[1].getType().isReal();
    ret.push_back(nm->mkConstRealOrInt(isReal ? rtype : itype, r));
  }
  return ret;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
