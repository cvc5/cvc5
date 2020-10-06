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

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {

TrustSubstitutionMap::TrustSubstitutionMap(context::Context* c,
                                           ProofNodeManager* pnm)
    : d_subs(c)
{
}

void TrustSubstitutionMap::addSubstitution(TNode x, TNode t, ProofGenerator* pg)
{
  d_subs.addSubstitution(x, t);
}

TrustNode TrustSubstitutionMap::apply(Node n, bool doRewrite)
{
  Node ns = d_subs.apply(n);
  if (doRewrite)
  {
    ns = Rewriter::rewrite(ns);
  }
  return TrustNode::mkTrustRewrite(n, ns, nullptr);
}

void TrustSubstitutionMap::addSubstitutionSolved(TNode x, TNode t, TrustNode tn)
{
  if (!isProofEnabled() || tn.getGenerator() == nullptr)
  {
    // no generator or not proof enabled, nothing to do
    addSubstitution(x, t, nullptr);
    return;
  }
  // NOTE: can try to transform tn.getProven() to (= x t) here
  addSubstitution(x, t, nullptr);
}

SubstitutionMap& TrustSubstitutionMap::get() { return d_subs; }

bool TrustSubstitutionMap::isProofEnabled() const { return false; }

}  // namespace theory
}  // namespace CVC4
