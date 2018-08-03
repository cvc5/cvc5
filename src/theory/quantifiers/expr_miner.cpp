/*********************                                                        */
/*! \file expr_miner.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of expr_miner
 **/

#include "theory/quantifiers/expr_miner.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

ExpressionMiner::ExpressionMiner()
    : d_do_rew_synth(false), d_do_query_gen(false), d_use_sygus_type(false)
{
}

void ExpressionMiner::initialize(bool doRewSynth,
                                 bool doQueryGen,
                                 ExtendedRewriter* er,
                                 TypeNode tn,
                                 std::vector<Node>& vars,
                                 unsigned nsamples,
                                 bool unique_type_ids,
                                      unsigned deqThresh)
{
  Assert(doRewSynth || doQueryGen);
  d_do_rew_synth = doRewSynth;
  d_do_query_gen = doQueryGen;
  d_use_sygus_type = false;
  d_crd.initialize(&d_sampler, er, tn, vars, nsamples, unique_type_ids);
  if (!doRewSynth)
  {
    d_crd.setSilent(true);
  }
  if (doQueryGen)
  {
    d_qg.initialize(&d_sampler,deqThresh);
  }
}

void ExpressionMiner::initializeSygus(bool doRewSynth,
                                      bool doQueryGen,
                                      QuantifiersEngine* qe,
                                      Node f,
                                      unsigned nsamples,
                                      bool useSygusType,
                                      unsigned deqThresh
                                     )
{
  Assert(doRewSynth || doQueryGen);
  d_do_rew_synth = doRewSynth;
  d_do_query_gen = doQueryGen;
  d_use_sygus_type = useSygusType;
  d_crd.initializeSygus(&d_sampler, qe, f, nsamples, useSygusType);
  if (!d_do_rew_synth)
  {
    d_crd.setSilent(true);
  }
  if (d_do_query_gen)
  {
    d_qg.initialize(&d_sampler,deqThresh);
  }
}

bool ExpressionMiner::addTerm(Node sol, std::ostream& out, bool& rew_print)
{
  bool ret = d_crd.addTerm(sol, out, rew_print);
  if (ret && d_do_query_gen)
  {
    // a unique term, let's try the query generator
    d_qg.addTerm(sol);
  }
  return ret;
}

bool ExpressionMiner::addTerm(Node sol, std::ostream& out)
{
  bool rew_print = false;
  return addTerm(sol, out, rew_print);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
