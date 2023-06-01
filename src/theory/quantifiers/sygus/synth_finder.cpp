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
 * Synthesis finder
 */

#include "theory/quantifiers/sygus/synth_finder.h"

#include "options/quantifiers_options.h"
#include "smt/env.h"
#include "theory/quantifiers/query_generator_sample_sat.h"
#include "theory/quantifiers/query_generator_unsat.h"
#include "options/base_options.h"
#include "printer/printer.h"
#include "theory/datatypes/sygus_datatype_utils.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SynthFinder::SynthFinder(Env& env)
    : EnvObj(env)
{
}

Node SynthFinder::findSynth(modes::FindSynthTarget fst, const TypeNode& gtn)
{
  // should be a sygus datatype
  if (gtn.isNull() || !gtn.isDatatype() || !gtn.getDType().isSygus())
  {
    return Node::null();
  }
  modes::FindSynthTarget fstu = fst;
  // rewrites from input use the same algorithm
  if (fstu==modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE_INPUT)
  {
    fstu = modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE;
  }
  NodeManager* nm = NodeManager::currentNM();
  
  // make the enumerator variable
  Node e = nm->mkBoundVar(gtn);
  
  // initialize the expression miner
  initialize(fstu, e);
  
  // initialize the enumerator
  SygusEnumerator sygusEnum(d_env);
  sygusEnum.initialize(e);
  // run the enumerator until we are finished
  Node curr;
  std::vector<Node> ret;
  while (sygusEnum.increment())
  {
    curr = sygusEnum.getCurrent();
    if (curr.isNull())
    {
      continue;
    }
    // run the next expression mining for the current term
    ret = runNext(curr, fstu, e);
    if (!ret.empty())
    {
      // output the returned term
      std::ostream& out = options().base.out;
      for (const Node& r : ret)
      {
        out << "(" << fst << " " << r << ")" << std::endl;
      }
      // if sygus stream, we continue, otherwise we terminate and return
      if (!options().quantifiers.sygusStream)
      {
        break;
      }
    }
  }
  Node retn = nm->mkNode(kind::SEXPR, ret);
  return retn;
}

class SygusEnumeratorCallbackNoSym : public SygusEnumeratorCallback
{
public:
  SygusEnumeratorCallbackNoSym(Env& env) : SygusEnumeratorCallback(env){}
protected:
  /** Get the cache value for the given candidate */
  Node getCacheValue(const Node& n, const Node& bn) override {
    return bn;
  }
};

void SynthFinder::initialize(modes::FindSynthTarget fst, const Node& e)
{
  options::SygusQueryGenMode qmode = options().quantifiers.sygusQueryGen;
  
  // get the sygus variables from the type of the enumerator
  const TypeNode& gtn = e.getType();
  Assert (gtn.isDatatype());
  const DType& dt = gtn.getDType();
  Assert (dt.isSygus());
  Node vlist = dt.getSygusVarList();
  std::vector<Node> vars;
  if (!vlist.isNull())
  {
    for (const Node& sv : vlist)
    {
      vars.push_back(sv);
    }
  }
  
  // initialize the sampler if necessary
  bool needsSampler = false;
  size_t nsamples = options().quantifiers.sygusSamples;
  bool samplerUniqueTypeIds = false;
  if (fst==modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE_UNSOUND)
  {
    needsSampler = true;
  }
  else if (fst==modes::FindSynthTarget::FIND_SYNTH_TARGET_QUERY)
  {
    needsSampler = (qmode == options::SygusQueryGenMode::SAMPLE_SAT);
  }
  d_sampler = nullptr;
  if (needsSampler)
  {
    d_sampler.reset(new SygusSampler(d_env));
    d_sampler->initialize(dt.getSygusType(), vars, nsamples, samplerUniqueTypeIds);
  }
  
  // initialize the candidate rewrite database
  bool needsCandidateRewriteDb = false;
  if (fst==modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE ||
    fst==modes::FindSynthTarget::FIND_SYNTH_TARGET_QUERY)
  {
    needsCandidateRewriteDb = true;
  }
  
  // initialize the sygus enumerator callback if necessary
  d_ecb = nullptr;
  if (fst==modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE_UNSOUND)
  {
    d_ecb.reset(new SygusEnumeratorCallbackNoSym(d_env));
  } 
  
  // now, setup the handlers
  if (fst==modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE)
  {
    d_crd.reset(new CandidateRewriteDatabase(d_env,
            options().quantifiers.sygusRewSynthCheck));
    d_crd->initialize(vars, d_sampler.get());
  }
  else if (fst==modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE_UNSOUND)
  {
    // only the sampler is required
  }
  else if (fst==modes::FindSynthTarget::FIND_SYNTH_TARGET_QUERY)
  {
    if (qmode == options::SygusQueryGenMode::SAMPLE_SAT)
    {
      size_t deqThresh = options().quantifiers.sygusQueryGenThresh;
      d_qg = std::make_unique<QueryGeneratorSampleSat>(d_env, deqThresh);
    }
    else if (qmode == options::SygusQueryGenMode::UNSAT)
    {
      d_qg = std::make_unique<QueryGeneratorUnsat>(d_env);
    }
    else if (qmode == options::SygusQueryGenMode::BASIC)
    {
      d_qg = std::make_unique<QueryGeneratorBasic>(d_env);
    }
    else
    {
      Unhandled() << "Unknown query generation mode " << qmode;
    }
    // initialize the query generator
    d_qg->initialize(vars, d_sampler.get());
  }
}

std::vector<Node> SynthFinder::runNext(const Node& n, modes::FindSynthTarget fst, const Node& e)
{
  std::vector<Node> ret;
  Node bn = datatypes::utils::sygusToBuiltin(n, true);
  if (fst==modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE)
  {
    std::vector<std::pair<bool, Node>> rewrites;
    d_crd->addTerm(
        n, options().quantifiers.sygusRewSynthRec, rewrites);
    for (const std::pair<bool,Node>& r : rewrites)
    {
      ret.push_back(r.second);
    }
  }
  else if (fst==modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE_UNSOUND)
  {
    // check its rewritten form
    Node nr = rewrite(n);
    if (!d_sampler->checkEquivalent(n, nr))
    {
      std::stringstream ss;
      d_sampler->checkEquivalent(n, nr, &ss);
      Warning() << ss.str();
      ret.push_back(n.eqNode(nr));
    }
  }
  else if (fst==modes::FindSynthTarget::FIND_SYNTH_TARGET_QUERY)
  {
    Assert (d_qg!=nullptr);
    std::vector<Node> queries;
    d_qg->addTerm(n, queries);
    ret.insert(ret.end(), queries.begin(), queries.end());
  }
  return ret;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
