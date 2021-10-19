/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for mining interesting satisfiability queries from a stream
 * of generated expressions.
 */

#include "theory/quantifiers/query_generator_unsat.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

QueryGeneratorUnsat::QueryGeneratorUnsat(Env& env)
    : ExprMiner(env), d_queryCount(0)
{
}

void QueryGeneratorUnsat::initialize(const std::vector<Node>& vars,
                                     SygusSampler* ss)
{
  Assert(ss != nullptr);
  d_queryCount = 0;
  ExprMiner::initialize(vars, ss);
}

bool QueryGeneratorUnsat::addTerm(Node n, std::ostream& out)
{
  d_terms.push_back(n);
  Trace("sygus-qgen") << "Add term: " << n << std::endl;

  std::unordered_set<size_t> indices;
  std::unordered_set<size_t> activeIndices;

  return true;
}

Result QueryGeneratorUnsat::checkCurrent(const std::vector<Node>& activeTerms, std::vector<Node>& unsatCore)
{
  NodeManager * nm = NodeManager::currentNM();
  Node qy = nm->mkAnd(activeTerms);
  std::unique_ptr<SolverEngine> queryChecker;
  initializeChecker(queryChecker, qy);
  Result r = queryChecker->checkSat();
  if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    // if unsat, get the unsat core
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
