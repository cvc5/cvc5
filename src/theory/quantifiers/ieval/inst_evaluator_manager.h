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
 * Inst evaluator manager class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__IEVAL__INST_EVALUATOR_MANAGER_H
#define CVC5__THEORY__QUANTIFIERS__IEVAL__INST_EVALUATOR_MANAGER_H

#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/ieval/inst_evaluator.h"
#include "theory/quantifiers/quant_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDb;

namespace ieval {

/**
 * Inst evaluator manager, used for allocating InstEvaluators.
 *
 * It ensures that all allocated inst evaluators that are allocated are
 * hard-reset during the beginning of each instantiation round. This is to
 * ensure that the evaluation of terms based on the term database is correct.
 */
class InstEvaluatorManager : public QuantifiersUtil
{
  using QuantEvPair = std::pair<Node, TermEvaluatorMode>;

 public:
  InstEvaluatorManager(Env& env, QuantifiersState& qs, TermDb& tdb);
  /** reset (calculate which terms are active) */
  bool reset(Theory::Effort effort) override;
  /** identify */
  std::string identify() const override;
  /** Get evaluator for quantified formula q in evaluation mode tev */
  InstEvaluator* getEvaluator(Node q, TermEvaluatorMode tev);

 private:
  /** Reference to quantifiers state */
  QuantifiersState& d_qstate;
  /** Reference to term database */
  TermDb& d_tdb;
  /** Maps to the evaluators */
  std::map<QuantEvPair, std::unique_ptr<InstEvaluator> > d_evals;
};

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__IEVAL__INST_EVALUATOR_MANAGER_H */
