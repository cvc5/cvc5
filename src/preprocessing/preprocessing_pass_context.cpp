/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The preprocessing pass context for passes.
 */

#include "preprocessing/preprocessing_pass_context.h"

#include "expr/node_algorithm.h"
#include "smt/env.h"
#include "smt/smt_engine.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"

namespace cvc5 {
namespace preprocessing {

PreprocessingPassContext::PreprocessingPassContext(
    SmtEngine* smt,
    Env& env,
    theory::booleans::CircuitPropagator* circuitPropagator)
    : EnvObj(env),
      d_smt(smt),
      d_circuitPropagator(circuitPropagator),
      d_llm(env.getTopLevelSubstitutions(),
            env.getUserContext(),
            env.getProofNodeManager()),
      d_symsInAssertions(env.getUserContext())
{
}
const Options& PreprocessingPassContext::getOptions() const
{
  return d_env.getOptions();
}
const LogicInfo& PreprocessingPassContext::getLogicInfo() const
{
  return d_env.getLogicInfo();
}

theory::TrustSubstitutionMap&
PreprocessingPassContext::getTopLevelSubstitutions() const
{
  return d_env.getTopLevelSubstitutions();
}

TheoryEngine* PreprocessingPassContext::getTheoryEngine() const
{
  return d_smt->getTheoryEngine();
}
prop::PropEngine* PreprocessingPassContext::getPropEngine() const
{
  return d_smt->getPropEngine();
}
context::Context* PreprocessingPassContext::getUserContext() const
{
  return d_env.getUserContext();
}
context::Context* PreprocessingPassContext::getDecisionContext() const
{
  return d_env.getContext();
}
void PreprocessingPassContext::spendResource(Resource r)
{
  d_env.getResourceManager()->spendResource(r);
}
void PreprocessingPassContext::recordSymbolsInAssertions(
    const std::vector<Node>& assertions)
{
  std::unordered_set<TNode> visited;
  std::unordered_set<Node> syms;
  for (TNode cn : assertions)
  {
    expr::getSymbols(cn, syms, visited);
  }
  for (const Node& s : syms)
  {
    d_symsInAssertions.insert(s);
  }
}

void PreprocessingPassContext::notifyLearnedLiteral(TNode lit)
{
  d_llm.notifyLearnedLiteral(lit);
}

std::vector<Node> PreprocessingPassContext::getLearnedLiterals() const
{
  return d_llm.getLearnedLiterals();
}

void PreprocessingPassContext::addSubstitution(const Node& lhs,
                                               const Node& rhs,
                                               ProofGenerator* pg)
{
  getTopLevelSubstitutions().addSubstitution(lhs, rhs, pg);
}

void PreprocessingPassContext::addSubstitution(const Node& lhs,
                                               const Node& rhs,
                                               PfRule id,
                                               const std::vector<Node>& args)
{
  getTopLevelSubstitutions().addSubstitution(lhs, rhs, id, {}, args);
}

ProofNodeManager* PreprocessingPassContext::getProofNodeManager() const
{
  return d_env.getProofNodeManager();
}

}  // namespace preprocessing
}  // namespace cvc5
