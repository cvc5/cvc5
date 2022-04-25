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

class TermRegistry;

namespace ieval {

/**
 * Inst evaluator manager, used for allocating InstEvaluators.
 */
class InstEvaluatorManager : public QuantifiersUtil
{
 public:
  InstEvaluatorManager(Env& env, QuantifiersState& qs, TermRegistry& tr);
  /** reset (calculate which terms are active) */
  bool reset(Theory::Effort effort) override;
  /** identify */
  std::string identify() const override;
  /** Get evaluator */
  InstEvaluator* getEvaluator(Node q, TermEvaluatorMode tev);

 private:
  /** Quantifiers state */
  QuantifiersState& d_qstate;
  /** Reference to term registry */
  TermRegistry& d_treg;
  /** Maps to the evaluators */
  std::map<std::pair<Node, TermEvaluatorMode>, std::unique_ptr<InstEvaluator> >
      d_evals;
};

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__IEVAL__INST_EVALUATOR_MANAGER_H */
