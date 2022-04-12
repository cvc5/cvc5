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
    : EnvObj(env),
      d_doRewSynth(false),
      d_doFilterLogicalStrength(false),
      d_use_sygus_type(false),
      d_tds(nullptr),
      d_crd(env,
            options().quantifiers.sygusRewSynthCheck,
            options().quantifiers.sygusRewSynthAccel,
            false),
      d_qg(nullptr),
      d_sols(env),
      d_sampler(env)
{
}

void ExpressionMinerManager::initialize(const std::vector<Node>& vars,
                                        TypeNode tn,
                                        unsigned nsamples,
                                        bool unique_type_ids)
{
  d_doRewSynth = false;
  d_qg = nullptr;
  d_doFilterLogicalStrength = false;
  d_sygus_fun = Node::null();
  d_use_sygus_type = false;
  d_tds = nullptr;
  // initialize the sampler
  d_sampler.initialize(tn, vars, nsamples, unique_type_ids);
}

void ExpressionMinerManager::initializeSygus(TermDbSygus* tds,
                                             Node f,
                                             unsigned nsamples,
                                             bool useSygusType)
{
  d_doRewSynth = false;
  d_qg = nullptr;
  d_doFilterLogicalStrength = false;
  d_sygus_fun = f;
  d_use_sygus_type = useSygusType;
  d_tds = tds;
  // initialize the sampler
  d_sampler.initializeSygus(d_tds, f, nsamples, useSygusType);
}

void ExpressionMinerManager::initializeMinersForOptions()
{
  if (options().quantifiers.sygusRewSynth)
  {
    enableRewriteRuleSynth();
  }
  if (options().quantifiers.sygusQueryGen != options::SygusQueryGenMode::NONE)
  {
    enableQueryGeneration(options().quantifiers.sygusQueryGenThresh);
  }
  if (options().quantifiers.sygusFilterSolMode
      != options::SygusFilterSolMode::NONE)
  {
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
}

void ExpressionMinerManager::enableRewriteRuleSynth()
{
  if (d_doRewSynth)
  {
    // already enabled
    return;
  }
  d_doRewSynth = true;
  std::vector<Node> vars;
  d_sampler.getVariables(vars);
  // initialize the candidate rewrite database
  if (!d_sygus_fun.isNull())
  {
    Assert(d_tds != nullptr);
    d_crd.initializeSygus(vars, d_tds, d_sygus_fun, &d_sampler);
  }
  else
  {
    d_crd.initialize(vars, &d_sampler);
  }
  d_crd.enableExtendedRewriter();
  d_crd.setSilent(false);
}

void ExpressionMinerManager::enableQueryGeneration(unsigned deqThresh)
{
  if (d_qg != nullptr)
  {
    // already enabled
    return;
  }
  options::SygusQueryGenMode mode = options().quantifiers.sygusQueryGen;
  std::vector<Node> vars;
  d_sampler.getVariables(vars);
  if (mode == options::SygusQueryGenMode::SAMPLE_SAT)
  {
    // must also enable rewrite rule synthesis
    if (!d_doRewSynth)
    {
      // initialize the candidate rewrite database, in silent mode
      enableRewriteRuleSynth();
      d_crd.setSilent(true);
    }
    d_qg = std::make_unique<QueryGeneratorSampleSat>(d_env, deqThresh);
  }
  else if (mode == options::SygusQueryGenMode::UNSAT)
  {
    d_qg = std::make_unique<QueryGeneratorUnsat>(d_env);
  }
  else if (mode == options::SygusQueryGenMode::BASIC)
  {
    d_qg = std::make_unique<QueryGeneratorBasic>(d_env);
  }
  if (d_qg != nullptr)
  {
    // initialize the query generator
    d_qg->initialize(vars, &d_sampler);
  }
}

void ExpressionMinerManager::enableFilterWeakSolutions()
{
  d_doFilterLogicalStrength = true;
  std::vector<Node> vars;
  d_sampler.getVariables(vars);
  d_sols.initialize(vars, &d_sampler);
  d_sols.setLogicallyStrong(true);
}

void ExpressionMinerManager::enableFilterStrongSolutions()
{
  d_doFilterLogicalStrength = true;
  std::vector<Node> vars;
  d_sampler.getVariables(vars);
  d_sols.initialize(vars, &d_sampler);
  d_sols.setLogicallyStrong(false);
}

bool ExpressionMinerManager::addTerm(Node sol,
                                     std::ostream& out,
                                     bool& rew_print)
{
  // set the builtin version
  Node solb = sol;
  if (d_use_sygus_type)
  {
    solb = datatypes::utils::sygusToBuiltin(sol, true);
  }

  // add to the candidate rewrite rule database
  bool ret = true;
  if (d_doRewSynth)
  {
    Node rsol = d_crd.addTerm(
        sol, options().quantifiers.sygusRewSynthRec, out, rew_print);
    ret = (sol == rsol);
  }

  // a unique term, let's try the query generator
  if (ret && d_qg != nullptr)
  {
    d_qg->addTerm(solb, out);
  }

  // filter based on logical strength
  if (ret && d_doFilterLogicalStrength)
  {
    ret = d_sols.addTerm(solb, out);
  }
  return ret;
}

bool ExpressionMinerManager::addTerm(Node sol, std::ostream& out)
{
  bool rew_print = false;
  return addTerm(sol, out, rew_print);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
