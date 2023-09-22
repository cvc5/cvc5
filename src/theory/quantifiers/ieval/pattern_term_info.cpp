/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Info per pattern term in the instantiation evaluator.
 */

#include "theory/quantifiers/ieval/pattern_term_info.h"

#include "expr/node_algorithm.h"
#include "theory/quantifiers/ieval/state.h"
#include "theory/quantifiers/ieval/term_evaluator.h"
#include "theory/quantifiers/term_database.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

PatTermInfo::PatTermInfo(context::Context* c)
    : d_eq(c), d_numUnassigned(c, 0), d_parentNotify(c), d_evalExpChild(c)
{
}

void PatTermInfo::initialize(TNode pattern)
{
  Assert(!pattern.isNull());
  d_pattern = pattern;
}

bool PatTermInfo::isActive() const { return d_eq.get().isNull(); }

bool PatTermInfo::notifyChild(State& s,
                              TNode child,
                              TNode val,
                              TermEvaluator* tec)
{
  Assert(!val.isNull());
  Assert(!expr::hasFreeVar(val));
  if (!d_eq.get().isNull())
  {
    // already set
    return false;
  }
  // ============================ handle short circuiting
  // maybe remember the child for explanations
  Node exp;
  d_eq = tec->partialEvaluateChild(s, d_pattern, child, val, exp);
  if (!d_eq.get().isNull())
  {
    Trace("ieval") << "  " << d_pattern << " := " << d_eq.get()
                   << " (partial evaluate)" << std::endl;
    d_evalExpChild = exp;
    return true;
  }

  // ============================ decrement number of unassigned children
  Assert(d_numUnassigned.get() > 0);
  d_numUnassigned = d_numUnassigned.get() - 1;
  Trace("ieval-state-debug")
      << "...unassigned children now " << d_numUnassigned << std::endl;
  if (d_numUnassigned > 0)
  {
    // not ready to evaluate
    return false;
  }

  // ============================ if fully evaluated, get values
  std::vector<TNode> childValues;
  for (TNode pc : d_pattern)
  {
    TNode pcv = s.getValue(pc);
    Assert(!pcv.isNull());
    childValues.push_back(pcv);
  }
  // call the evaluator
  d_eq = tec->evaluate(s, d_pattern, childValues);
  Assert(!d_eq.get().isNull());
  Trace("ieval") << "  " << d_pattern << " := " << d_eq.get() << " (evaluate)"
                 << std::endl;
  return true;
}

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
