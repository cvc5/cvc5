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

#include "theory/quantifiers/ieval/inst_evaluator_manager.h"

#include "options/quantifiers_options.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

InstEvaluatorManager::InstEvaluatorManager(Env& env,
                                           QuantifiersState& qs,
                                           TermDb& tdb)
    : QuantifiersUtil(env), d_qstate(qs), d_tdb(tdb)
{
}

bool InstEvaluatorManager::reset(Theory::Effort effort)
{
  for (std::pair<const QuantEvPair, std::unique_ptr<InstEvaluator> >& e :
       d_evals)
  {
    // ensure the information is completely cleared
    e.second->resetAll(false);
  }
  return true;
}

std::string InstEvaluatorManager::identify() const
{
  return "InstEvaluatorManager";
}

InstEvaluator* InstEvaluatorManager::getEvaluator(Node q, TermEvaluatorMode tev)
{
  if (tev == ieval::TermEvaluatorMode::NONE)
  {
    // no evaluation specified
    return nullptr;
  }
  options::IevalMode mode = options().quantifiers.ievalMode;
  if (options().quantifiers.ievalMode == options::IevalMode::OFF)
  {
    // not using instantiation evaluation, don't construct
    return nullptr;
  }
  QuantEvPair key(q, tev);
  std::map<QuantEvPair, std::unique_ptr<InstEvaluator> >::iterator it =
      d_evals.find(key);
  if (it != d_evals.end())
  {
    // already constructed
    return it->second.get();
  }
  // don't use canonization or trackAssignments, use generalized learning if
  // option specifies it
  bool genLearning = mode == options::IevalMode::USE_LEARN;
  d_evals[key].reset(
      new InstEvaluator(d_env, d_qstate, d_tdb, tev, genLearning));
  InstEvaluator* ret = d_evals[key].get();
  // set that we are watching quantified formula q
  ret->watch(q);
  // return
  return ret;
}

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
