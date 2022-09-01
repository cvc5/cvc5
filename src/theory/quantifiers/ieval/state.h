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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__IEVAL__STATE_H
#define CVC5__THEORY__QUANTIFIERS__IEVAL__STATE_H

#include <memory>

#include "context/cdhashset.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/ieval/free_var_info.h"
#include "theory/quantifiers/ieval/pattern_term_info.h"
#include "theory/quantifiers/ieval/quant_info.h"
#include "theory/quantifiers/ieval/term_evaluator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersState;
class TermRegistry;

namespace ieval {

class State : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  State(Env& env, context::Context* c, QuantifiersState& qs, TermDb& tdb);

  /** Evaluate ground term n */
  TNode evaluate(TNode n) const;
  /** Get value for pattern or ground term p. */
  TNode getValue(TNode p) const;

 private:
  //---------------quantifiers info
  /** Get quantifiers info */
  QuantInfo& getQuantInfo(TNode q);
  const QuantInfo& getQuantInfo(TNode q) const;
  //---------------free variable info
  /** Get free variable info */
  FreeVarInfo& getOrMkFreeVarInfo(TNode v);
  FreeVarInfo& getFreeVarInfo(TNode v);
  //---------------pattern term info
  /** Get pattern term info */
  PatTermInfo& getOrMkPatTermInfo(TNode p);
  PatTermInfo& getPatTermInfo(TNode p);
  const PatTermInfo& getPatTermInfo(TNode p) const;
  //---------------queries
  /** The context, managed by the parent inst evaluator */
  context::Context* d_ctx;
  /** Reference to quantifiers state */
  QuantifiersState& d_qstate;
  /** Reference to term database */
  TermDb& d_tdb;
  /** The term evaluator mode */
  TermEvaluatorMode d_tevMode;
  /** The term evaluator callback we are using */
  std::unique_ptr<TermEvaluator> d_tec;
  /** Map quantified formulas to their info */
  std::map<Node, QuantInfo> d_quantInfo;
  /** Free variable info */
  std::map<Node, FreeVarInfo> d_fvInfo;
  /** Pattern term info */
  std::map<Node, PatTermInfo> d_pInfo;
};

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
