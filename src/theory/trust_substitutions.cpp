/*********************                                                        */
/*! \file trust_substitutions.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Trust substitutions
 **/

#include "theory/trust_substitutions.h"

namespace CVC4 {
namespace theory {

TrustSubstitutionMap::TrustSubstitutionMap(context::UserContext* u,
                                             ProofNodeManager* pnm)
    : d_subs(u),
      d_pnm(pnm),
      d_subsPg(pnm ? new TConvProofGenerator(pnm, u) : nullptr)
{
}

void TrustSubstitutionMap::addSubstitution(TNode x,
                                            TNode t,
                                            ProofGenerator* pg)
{
  d_subs.addSubstitution(x, t);
}

TrustNode TrustSubstitutionMap::apply(Node n)
{
  return TrustNode::null();
}

SubstitutionMap& TrustSubstitutionMap::get() { return d_subs; }

}  // namespace theory
}  // namespace CVC4
