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
 * Implementation of quantifiers representative bound utility.
 */

#include "theory/quantifiers/quant_rep_bound_ext.h"

#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quant_bound_inference.h"
#include "theory/quantifiers/term_registry.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

QRepBoundExt::QRepBoundExt(Env& env,
                           QuantifiersBoundInference& qbi,
                           QuantifiersState& qs,
                           TermRegistry& tr,
                           TNode q)
    : d_qbi(qbi), d_model(tr.getModel()), d_instMatch(env, qs, tr, q)
{
}

RsiEnumType QRepBoundExt::setBound(Node owner,
                                   size_t i,
                                   std::vector<Node>& elements)
{
  // builtin: check if it is bound by bounded integer module
  if (owner.getKind() == FORALL)
  {
    BoundVarType bvt = d_qbi.getBoundVarType(owner, owner[0][i]);
    if (bvt != BOUND_FINITE)
    {
      d_bound_int[i] = true;
      return ENUM_CUSTOM;
    }
    // indicates the variable is finitely bound due to
    // the (small) cardinality of its type,
    // will treat in default way
  }
  return ENUM_INVALID;
}

bool QRepBoundExt::resetIndex(RepSetIterator* rsi,
                              Node owner,
                              size_t i,
                              bool initial,
                              std::vector<Node>& elements)
{
  if (d_bound_int.find(i) == d_bound_int.end())
  {
    // not bound
    return true;
  }
  Assert(owner.getKind() == FORALL);
  if (!d_qbi.getBoundElements(rsi, initial, owner, owner[0][i], elements))
  {
    return false;
  }
  return true;
}

bool QRepBoundExt::initializeRepresentativesForType(TypeNode tn)
{
  return d_model->initializeRepresentativesForType(tn);
}

bool QRepBoundExt::getVariableOrder(Node owner, std::vector<size_t>& varOrder)
{
  // must set a variable index order based on bounded integers
  if (owner.getKind() != FORALL)
  {
    return false;
  }
  Trace("bound-int-rsi") << "Calculating variable order..." << std::endl;
  d_qbi.getBoundVarIndices(owner, varOrder);
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
