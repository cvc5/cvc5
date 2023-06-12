/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of expr_miner.
 */

#include "theory/quantifiers/expr_miner.h"

#include <sstream>

#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

void ExprMiner::initialize(const std::vector<Node>& vars, SygusSampler* ss)
{
  d_sampler = ss;
  d_vars.insert(d_vars.end(), vars.begin(), vars.end());
}

Node ExprMiner::convertToSkolem(Node n)
{
  if (d_skolems.empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    for (const Node& v : d_vars)
    {
      std::stringstream ss;
      ss << "k_" << v;
      Node sk = sm->mkDummySkolem(ss.str(), v.getType());
      d_skolems.push_back(sk);
      d_fv_to_skolem[v] = sk;
    }
  }
  return n.substitute(
      d_vars.begin(), d_vars.end(), d_skolems.begin(), d_skolems.end());
}

void ExprMiner::initializeChecker(std::unique_ptr<SolverEngine>& checker,
                                  Node query,
                                  const SubsolverSetupInfo& info)
{
  Assert (!query.isNull());
  initializeSubsolver(
      checker,
      info,
      options().quantifiers.sygusExprMinerCheckTimeoutWasSetByUser,
      options().quantifiers.sygusExprMinerCheckTimeout);
  // Convert bound variables to skolems. This ensures the satisfiability
  // check is ground.
  Node squery = convertToSkolem(query);
  checker->assertFormula(squery);
}

Result ExprMiner::doCheck(Node query, const SubsolverSetupInfo& info)
{
  Node queryr = rewrite(query);
  if (queryr.isConst())
  {
    if (!queryr.getConst<bool>())
    {
      return Result(Result::UNSAT);
    }
    else
    {
      return Result(Result::SAT);
    }
  }
  std::unique_ptr<SolverEngine> smte;
  initializeChecker(smte, query, info);
  return smte->checkSat();
}

bool ExprMinerId::addTerm(Node n, std::vector<Node>& found)
{
  found.push_back(n);
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
