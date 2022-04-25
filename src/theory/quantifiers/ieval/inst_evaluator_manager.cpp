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

#include "theory/quantifiers/ieval/inst_evaluator_manager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

InstEvaluatorManager::InstEvaluatorManager(Env& env,
              QuantifiersState& qs,
              TermRegistry& tr) : QuantifiersUtil(env), d_qstate(qs), d_treg(tr) {}
bool InstEvaluatorManager::reset(Theory::Effort effort)
{
  return true;
}
std::string InstEvaluatorManager::identify() const { return "InstEvaluatorManager"; }

InstEvaluator* InstEvaluatorManager::getEvaluator(Node q, TermEvaluatorMode tev)
{
  std::pair<Node, TermEvaluatorMode> key(q, tev);
  return nullptr;
}

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
