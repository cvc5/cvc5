/*********************                                                        */
/*! \file arith_preprocess.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arithmetic preprocess
 **/

#include "theory/arith/arith_preprocess.h"

namespace CVC4 {
namespace theory {
namespace arith {

ArithPreprocess::ArithPreprocess(ArithState& state,
                                 InferenceManager& im,
                                 ProofNodeManager* pnm,
                                 const LogicInfo& info)
    : d_im(im), d_opElim(pnm, info), d_reduced(state.getUserContext())
{
}
TrustNode ArithPreprocess::eliminate(TNode n, bool partialOnly)
{
  return d_opElim.eliminate(n, partialOnly);
}
bool ArithPreprocess::reduceAssertion(TNode atom)
{
  context::CDHashMap<Node, bool, NodeHashFunction>::const_iterator it =
      d_reduced.find(atom);
  if (it != d_reduced.end())
  {
    // already computed
    return (*it).second;
  }
  TrustNode tn = eliminate(atom);
  if (tn.isNull())
  {
    // did not reduce
    d_reduced[atom] = false;
    return false;
  }
  Assert(tn.getKind() == TrustNodeKind::REWRITE);
  // tn is of kind REWRITE, turn this into a LEMMA here
  TrustNode tlem = TrustNode::mkTrustLemma(tn.getProven(), tn.getGenerator());
  // must preprocess
  d_im.trustedLemma(tlem, LemmaProperty::PREPROCESS);
  // mark the atom as reduced
  d_reduced[atom] = true;
  return true;
}

bool ArithPreprocess::isReduced(TNode atom) const
{
  context::CDHashMap<Node, bool, NodeHashFunction>::const_iterator it =
      d_reduced.find(atom);
  if (it == d_reduced.end())
  {
    return false;
  }
  return (*it).second;
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
