/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of expr_miner.
 */

#include "theory/quantifiers/expr_miner.h"

#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"

using namespace std;
using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {

void ExprMiner::initialize(const std::vector<Node>& vars, SygusSampler* ss)
{
  d_sampler = ss;
  d_vars.insert(d_vars.end(), vars.begin(), vars.end());
}

Node ExprMiner::convertToSkolem(Node n)
{
  std::vector<Node> fvs;
  TermUtil::computeVarContains(n, fvs);
  if (fvs.empty())
  {
    return n;
  }
  std::vector<Node> sfvs;
  std::vector<Node> sks;
  // map to skolems
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  for (unsigned i = 0, size = fvs.size(); i < size; i++)
  {
    Node v = fvs[i];
    // only look at the sampler variables
    if (std::find(d_vars.begin(), d_vars.end(), v) != d_vars.end())
    {
      sfvs.push_back(v);
      std::map<Node, Node>::iterator itf = d_fv_to_skolem.find(v);
      if (itf == d_fv_to_skolem.end())
      {
        Node sk = sm->mkDummySkolem("rrck", v.getType());
        d_fv_to_skolem[v] = sk;
        sks.push_back(sk);
      }
      else
      {
        sks.push_back(itf->second);
      }
    }
  }
  return n.substitute(sfvs.begin(), sfvs.end(), sks.begin(), sks.end());
}

void ExprMiner::initializeChecker(std::unique_ptr<SmtEngine>& checker,
                                  Node query)
{
  Assert (!query.isNull());
  if (Options::current().quantifiers.sygusExprMinerCheckTimeout__setByUser)
  {
    initializeSubsolver(checker, true, options::sygusExprMinerCheckTimeout());
  }
  else
  {
    initializeSubsolver(checker);
  }
  // also set the options
  checker->setOption("sygus-rr-synth-input", "false");
  checker->setOption("input-language", "smt2");
  // Convert bound variables to skolems. This ensures the satisfiability
  // check is ground.
  Node squery = convertToSkolem(query);
  checker->assertFormula(squery);
}

Result ExprMiner::doCheck(Node query)
{
  Node queryr = Rewriter::rewrite(query);
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
  std::unique_ptr<SmtEngine> smte;
  initializeChecker(smte, query);
  return smte->checkSat();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
