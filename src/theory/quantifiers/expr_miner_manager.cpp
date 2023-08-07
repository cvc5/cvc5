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
 * Implementation of expression miner manager.
 */

#include "theory/quantifiers/expr_miner_manager.h"

#include "options/quantifiers_options.h"
#include "smt/env.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/query_generator_sample_sat.h"
#include "theory/quantifiers/query_generator_unsat.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

ExpressionMinerManager::ExpressionMinerManager(Env& env)
    : EnvObj(env), d_doFilterLogicalStrength(false), d_sols(env)
{
}

void ExpressionMinerManager::initializeSygus(const TypeNode& tn)
{
  Assert(tn.isDatatype());
  const DType& dt = tn.getDType();
  Assert(dt.isSygus());
  Node vlist = dt.getSygusVarList();
  std::vector<Node> vars;
  if (!vlist.isNull())
  {
    for (const Node& sv : vlist)
    {
      d_vars.push_back(sv);
    }
  }
  if (options().quantifiers.sygusFilterSolMode
      == options::SygusFilterSolMode::STRONG)
  {
    enableFilterStrongSolutions();
  }
  else if (options().quantifiers.sygusFilterSolMode
           == options::SygusFilterSolMode::WEAK)
  {
    enableFilterWeakSolutions();
  }
}

void ExpressionMinerManager::enableFilterWeakSolutions()
{
  d_doFilterLogicalStrength = true;
  d_sols.initialize(d_vars);
  d_sols.setLogicallyStrong(true);
}

void ExpressionMinerManager::enableFilterStrongSolutions()
{
  d_doFilterLogicalStrength = true;
  d_sols.initialize(d_vars);
  d_sols.setLogicallyStrong(false);
}

bool ExpressionMinerManager::addTerm(Node sol)
{
  // set the builtin version
  Node solb = datatypes::utils::sygusToBuiltin(sol, true);

  bool ret = true;
  // filter based on logical strength
  if (d_doFilterLogicalStrength)
  {
    std::vector<Node> filtered;
    ret = d_sols.addTerm(solb, filtered);
  }
  return ret;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
