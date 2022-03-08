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
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "smt/env.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"

namespace cvc5 {
namespace preprocessing {

PreprocessingPassContext::PreprocessingPassContext(
    Env& env,
    TheoryEngine* te,
    prop::PropEngine* pe,
    theory::booleans::CircuitPropagator* circuitPropagator)
    : EnvObj(env),
      d_theoryEngine(te),
      d_propEngine(pe),
      d_circuitPropagator(circuitPropagator),
      d_llm(env),
      d_symsInAssertions(userContext())
{
}

theory::TrustSubstitutionMap&
PreprocessingPassContext::getTopLevelSubstitutions() const
{
  return d_env.getTopLevelSubstitutions();
}

TheoryEngine* PreprocessingPassContext::getTheoryEngine() const
{
  return d_theoryEngine;
}
prop::PropEngine* PreprocessingPassContext::getPropEngine() const
{
  return d_propEngine;
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

void PreprocessingPassContext::printSubstitution(const Node& lhs,
                                                 const Node& rhs) const
{
  Node eq = SkolemManager::getOriginalForm(lhs.eqNode(rhs));
  output(OutputTag::LEARNED_LITS)
      << "(learned-lit " << eq << " :preprocess-subs)" << std::endl;
  output(OutputTag::SUBS) << "(substitution " << eq << ")" << std::endl;
}

void PreprocessingPassContext::addSubstitution(const Node& lhs,
                                               const Node& rhs,
                                               ProofGenerator* pg)
{
  if (isOutputOn(OutputTag::LEARNED_LITS) || isOutputOn(OutputTag::SUBS))
  {
    printSubstitution(lhs, rhs);
  }
  d_env.getTopLevelSubstitutions().addSubstitution(lhs, rhs, pg);
}

void PreprocessingPassContext::addSubstitution(const Node& lhs,
                                               const Node& rhs,
                                               PfRule id,
                                               const std::vector<Node>& args)
{
  if (isOutputOn(OutputTag::LEARNED_LITS) || isOutputOn(OutputTag::SUBS))
  {
    printSubstitution(lhs, rhs);
  }
  d_env.getTopLevelSubstitutions().addSubstitution(lhs, rhs, id, {}, args);
}

void PreprocessingPassContext::addSubstitutions(
    theory::TrustSubstitutionMap& tm)
{
  if (isOutputOn(OutputTag::LEARNED_LITS) || isOutputOn(OutputTag::SUBS))
  {
    std::unordered_map<Node, Node> subs = tm.get().getSubstitutions();
    for (const std::pair<const Node, Node>& s : subs)
    {
      printSubstitution(s.first, s.second);
    }
  }
  d_env.getTopLevelSubstitutions().addSubstitutions(tm);
}

}  // namespace preprocessing
}  // namespace cvc5
