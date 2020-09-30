/*********************                                                        */
/*! \file top_level_substitutions.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Top-level substitutions
 **/

#include "preprocessing/top_level_substitutions.h"

namespace CVC4 {
namespace preprocessing {

TopLevelSubstitutions::TopLevelSubstitutions(
    context::UserContext * u, ProofNodeManager * pnm)
    :  d_subs(u), d_pnm(pnm), d_subsPg(pnm ? new TConvProofGenerator(pnm, u) : nullptr)
{
}

void TopLevelSubstitutions::addSubstitution(TNode x, TNode t, ProofGenerator * pg)
{
  d_subs.addSubstitution(x, t);
}

theory::TrustNode TopLevelSubstitutions::apply(Node n)
{
  return theory::TrustNode::null();
}

theory::SubstitutionMap& TopLevelSubstitutions::get()
{
  return d_subs;
}

}  // namespace preprocessing
}  // namespace CVC4
