/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic preprocess.
 */

#include "theory/arith/arith_preprocess.h"

#include "theory/arith/inference_manager.h"
#include "theory/skolem_lemma.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

ArithPreprocess::ArithPreprocess(Env& env,
                                 InferenceManager& im,
                                 ProofNodeManager* pnm,
                                 OperatorElim& oe)
    : EnvObj(env), d_im(im), d_opElim(oe), d_reduced(userContext())
{
}
TrustNode ArithPreprocess::eliminate(TNode n,
                                     std::vector<SkolemLemma>& lems,
                                     bool partialOnly)
{
  return d_opElim.eliminate(n, lems, partialOnly);
}

bool ArithPreprocess::reduceAssertion(TNode atom)
{
  context::CDHashMap<Node, bool>::const_iterator it = d_reduced.find(atom);
  if (it != d_reduced.end())
  {
    // already computed
    return (*it).second;
  }
  std::vector<SkolemLemma> lems;
  TrustNode tn = eliminate(atom, lems);
  for (const SkolemLemma& lem : lems)
  {
    d_im.trustedLemma(lem.d_lemma, InferenceId::ARITH_PP_ELIM_OPERATORS_LEMMA);
  }
  if (tn.isNull())
  {
    // did not reduce
    d_reduced[atom] = false;
    return false;
  }
  Assert(tn.getKind() == TrustNodeKind::REWRITE);
  // tn is of kind REWRITE, turn this into a LEMMA here
  TrustNode tlem = TrustNode::mkTrustLemma(tn.getProven(), tn.getGenerator());
  // send the trusted lemma
  d_im.trustedLemma(tlem, InferenceId::ARITH_PP_ELIM_OPERATORS);
  // mark the atom as reduced
  d_reduced[atom] = true;
  return true;
}

bool ArithPreprocess::isReduced(TNode atom) const
{
  context::CDHashMap<Node, bool>::const_iterator it = d_reduced.find(atom);
  if (it == d_reduced.end())
  {
    return false;
  }
  return (*it).second;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
