/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of bit-vector conversions solver.
 */

#include "theory/uf/conversions_solver.h"

#include "theory/arith/arith_utilities.h"
#include "theory/theory_inference_manager.h"
#include "theory/theory_model.h"
#include "theory/theory_state.h"

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
  Trace("bv-convs") << "Check reduction " << n << std::endl;
  if (d_reduced.find(n) != d_reduced.end())
  {
    Trace("bv-convs") << "...already reduced" << std::endl;
    return;
  }
  // check whether it already has the correct value in the model?
  Node val = d_state.getModel()->getValue(n);
  Node uval = d_state.getRepresentative(n);
  Trace("bv-convs-debug") << "  model value = " << val << std::endl;
  Trace("bv-convs-debug") << "          rep = " << uval << std::endl;
  if (val == uval)
  {
    // "model-based reduction" strategy, do not reduce things that already have
    // correct model values
    Trace("bv-convs") << "...already correct in model" << std::endl;
    return;
  }

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
  Trace("bv-convs") << "...do reduction" << std::endl;
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
