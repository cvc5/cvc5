/*********************                                                        */
/*! \file expr_miner_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of expr_miner_manager
 **/

#include "theory/quantifiers/expr_miner_manager.h"

#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

ExpressionMinerManager::ExpressionMinerManager()
    : d_do_rew_synth(false),
      d_do_query_gen(false),
      d_use_sygus_type(false),
      d_tds(nullptr)
{
}

void ExpressionMinerManager::initialize(const std::vector<Node>& vars,
                                        bool doRewSynth,
                                        bool doQueryGen,
                                        ExtendedRewriter* er,
                                        TypeNode tn,
                                        unsigned nsamples,
                                        bool unique_type_ids,
                                        unsigned deqThresh)
{
  Assert(doRewSynth || doQueryGen);
  d_do_rew_synth = doRewSynth;
  d_do_query_gen = doQueryGen;
  d_use_sygus_type = false;
  d_tds = nullptr;
  // initialize the sampler
  d_sampler.initialize(tn, vars, nsamples, unique_type_ids);
  // initialize the candidate rewrite database
  d_crd.initialize(vars, &d_sampler);
  d_crd.setExtendedRewriter(er);
  if (!doRewSynth)
  {
    d_crd.setSilent(true);
  }
  // initialize the query generator
  if (doQueryGen)
  {
    d_qg.initialize(vars, &d_sampler);
    d_qg.setThreshold(deqThresh);
  }
}

void ExpressionMinerManager::initializeSygus(bool doRewSynth,
                                             bool doQueryGen,
                                             QuantifiersEngine* qe,
                                             Node f,
                                             unsigned nsamples,
                                             bool useSygusType,
                                             unsigned deqThresh)
{
  Assert(doRewSynth || doQueryGen);
  d_do_rew_synth = doRewSynth;
  d_do_query_gen = doQueryGen;
  d_use_sygus_type = useSygusType;
  d_tds = qe->getTermDatabaseSygus();
  // initialize the sampler
  d_sampler.initializeSygus(d_tds, f, nsamples, useSygusType);
  // get the variables from the sampler
  std::vector<Node> vars;
  d_sampler.getVariables(vars);
  // initialize the candidate rewrite database
  d_crd.initializeSygus(vars, qe, f, &d_sampler);
  if (!d_do_rew_synth)
  {
    d_crd.setSilent(true);
  }
  // initialize the query generator
  if (d_do_query_gen)
  {
    d_qg.initialize(vars, &d_sampler);
    d_qg.setThreshold(deqThresh);
  }
}

bool ExpressionMinerManager::addTerm(Node sol,
                                     std::ostream& out,
                                     bool& rew_print)
{
  bool ret = d_crd.addTerm(sol, out, rew_print);
  if (ret && d_do_query_gen)
  {
    // always use the builtin version
    Node solb = sol;
    if (d_use_sygus_type)
    {
      solb = d_tds->sygusToBuiltin(sol);
    }
    // a unique term, let's try the query generator
    d_qg.addTerm(solb, out);
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
}  // namespace CVC4
