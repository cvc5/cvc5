/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of bitvector conversions solver.
 */

#include "theory/uf/conversions_solver.h"

#include "theory/arith/arith_utilities.h"
#include "theory/theory_inference_manager.h"
#include "theory/theory_model.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace uf {

ConversionsSolver::ConversionsSolver(Env& env,
                                     TheoryState& state,
                                     TheoryInferenceManager& im)
    : EnvObj(env),
      d_state(state),
      d_im(im),
      d_preRegistered(userContext()),
      d_reduced(userContext())
{
}

ConversionsSolver::~ConversionsSolver() {}

void ConversionsSolver::preRegisterTerm(TNode term)
{
  d_preRegistered.push_back(term);
}

void ConversionsSolver::check()
{
  Trace("bv-convs") << "Bitvector conversion terms : " << std::endl;
  Trace("bv-convs") << "ConversionsSolver: Check reductions for "
                    << d_preRegistered.size() << " terms" << std::endl;
  // check reductions for all bv conversion terms
  for (const Node& a : d_preRegistered)
  {
    checkReduction(a);
  }
}

void ConversionsSolver::checkReduction(Node n)
{
  if (d_reduced.find(n) != d_reduced.end())
  {
    Trace("bv-convs") << "...already reduced" << std::endl;
    return;
  }
  // check whether it already has the correct value in the model?

  Node lem;
  Kind k = n.getKind();
  if (k == BITVECTOR_TO_NAT)
  {
    lem = arith::eliminateBv2Nat(n);
  }
  else if (k == INT_TO_BITVECTOR)
  {
    lem = arith::eliminateInt2Bv(n);
  }
  lem = n.eqNode(lem);
  d_im.lemma(lem, InferenceId::UF_ARITH_BV_CONV_REDUCTION);
  d_reduced.insert(n);
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
