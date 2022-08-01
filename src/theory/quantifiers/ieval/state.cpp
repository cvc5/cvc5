/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * State for instantiation evaluator
 */

#include "theory/quantifiers/ieval/state.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

State::State(Env& env, context::Context* c, QuantifiersState& qs, TermDb& tdb)
    : EnvObj(env),
      d_ctx(c),
      d_qstate(qs),
      d_tdb(tdb),
      d_tevMode(ieval::TermEvaluatorMode::NONE)
{
}

TNode State::evaluate(TNode n) const
{
  if (n.isConst())
  {
    return n;
  }
  // all pattern terms should have been assigned pattern term info
  Assert(!expr::hasBoundVar(n));
  return d_tec->evaluateBase(*this, n);
}

TNode State::getValue(TNode p) const
{
  if (p.isConst())
  {
    return p;
  }
  std::map<Node, PatTermInfo>::const_iterator it = d_pInfo.find(p);
  if (it != d_pInfo.end())
  {
    return it->second.d_eq;
  }
  // all pattern terms should have been assigned pattern term info
  Assert(!expr::hasBoundVar(p));
  return d_tec->evaluateBase(*this, p);
}

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
