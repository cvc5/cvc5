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
    : d_subs(c), d_subsPg(pnm ? new TConvProofGenerator(pnm, c) : nullptr)
{
  // Notice that d_subsPg uses the FIXPOINT policy, since SubstitutionMap
  // is applied to fixpoint.
}

void TrustSubstitutionMap::addSubstitution(TNode x, TNode t, ProofGenerator* pg)
{
  d_subs.addSubstitution(x, t);
  if (isProofEnabled())
  {
    // d_subsPg->addRewriteStep(x, t, pg);
  }
}

void TrustSubstitutionMap::addSubstitutions(TrustSubstitutionMap& t)
{
  // TODO?
  SubstitutionMap& st = t.get();
  for (SubstitutionMap::NodeMap::const_iterator it = st.begin(),
                                                it_end = st.end();
       it != it_end;
       ++it)
  {
    Node x = (*it).first;
    // issue: cannot extract original proof generator from rewrite step for x.
  }
}

TrustNode TrustSubstitutionMap::apply(Node n, bool doRewrite)
{
  Node ns = d_subs.apply(n);
  if (doRewrite)
  {
    ns = Rewriter::rewrite(ns);
  }
  return TrustNode::mkTrustRewrite(n, ns, d_subsPg.get());
}

SubstitutionMap& TrustSubstitutionMap::get() { return d_subs; }

bool TrustSubstitutionMap::isProofEnabled() const
{
  return d_subsPg != nullptr;
}

}  // namespace theory
}  // namespace CVC4
