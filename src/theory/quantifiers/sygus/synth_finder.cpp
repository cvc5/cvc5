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

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "smt/env.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/query_generator_sample_sat.h"
#include "theory/quantifiers/query_generator_unsat.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SynthFinder::SynthFinder(Env& env) : EnvObj(env), d_current(nullptr) {}

void SynthFinder::initializeFindSynth(modes::FindSynthTarget fst,
                                      const TypeNode& gtn)
{
  // should be a sygus datatype
  Assert(!gtn.isNull() && gtn.isDatatype() && gtn.getDType().isSygus());
  d_fst = fst;
  d_fstu = fst;
  // rewrites from input use the same algorithm
  if (d_fstu == modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE_INPUT)
  {
    d_fstu = modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE;
  }
  NodeManager* nm = NodeManager::currentNM();

  // make the enumerator variable
  Node e = nm->mkBoundVar(gtn);

  // initialize the expression miner
  initialize(d_fstu, e);

  // initialize the enumerator
  d_enum.reset(new SygusEnumerator(d_env, nullptr, d_ecb.get()));
  d_enum->initialize(e);
}

bool SynthFinder::increment()
{
  Assert(d_enum != nullptr);
  return d_enum->increment();
}

Node SynthFinder::getCurrent()
{
  Assert(d_enum != nullptr);
  Node curr = d_enum->getCurrent();
  if (curr.isNull())
  {
    // enumerator does not yet have a term
    return curr;
  }
  return runNext(curr, d_fstu);
}

class SygusEnumeratorCallbackNoSym : public SygusEnumeratorCallback
{
 public:
  SygusEnumeratorCallbackNoSym(Env& env) : SygusEnumeratorCallback(env) {}

 protected:
  /** Get the cache value for the given candidate */
  Node getCacheValue(const Node& n, const Node& bn) override { return bn; }
};

void SynthFinder::initialize(modes::FindSynthTarget fst, const Node& e)
{
  options::SygusQueryGenMode qmode = options().quantifiers.sygusQueryGen;

  // get the sygus variables from the type of the enumerator
  const TypeNode& gtn = e.getType();
  Assert(gtn.isDatatype());
  const DType& dt = gtn.getDType();
  Assert(dt.isSygus());
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
  if (fst == modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE
      || fst == modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE_UNSOUND)
  {
    needsSampler = true;
  }
  else if (fst == modes::FindSynthTarget::FIND_SYNTH_TARGET_QUERY)
  {
    needsSampler = (qmode == options::SygusQueryGenMode::SAMPLE_SAT);
  }
  d_sampler = nullptr;
  if (needsSampler)
  {
    d_sampler.reset(new SygusSampler(d_env));
    d_sampler->initialize(
        dt.getSygusType(), vars, nsamples, samplerUniqueTypeIds);
  }

  // initialize the sygus enumerator callback if necessary
  d_ecb = nullptr;
  if (fst == modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE_UNSOUND)
  {
    d_ecb.reset(new SygusEnumeratorCallbackNoSym(d_env));
  }

  // now, setup the handlers
  if (fst == modes::FindSynthTarget::FIND_SYNTH_TARGET_ENUM)
  {
    d_eid.reset(new ExprMinerId(d_env));
    d_current = d_eid.get();
  }
  else if (fst == modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE)
  {
    d_crd.reset(
        new CandidateRewriteDatabase(d_env,
                                     options().quantifiers.sygusRewSynthCheck,
                                     false,
                                     true,
                                     options().quantifiers.sygusRewSynthRec));
    d_crd->initialize(vars, d_sampler.get());
    d_current = d_crd.get();
  }
  else if (fst == modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE_UNSOUND)
  {
  }
  else if (fst == modes::FindSynthTarget::FIND_SYNTH_TARGET_QUERY)
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
    d_current = d_qg.get();
  }
}

Node SynthFinder::runNext(const Node& n, modes::FindSynthTarget fst)
{
  std::vector<Node> ret;
  Node bn = datatypes::utils::sygusToBuiltin(n, true);
  Trace("synth-finder") << "runNext " << d_fstu << " " << bn << std::endl;
  if (fst == modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE)
  {
    d_crd->addTerm(bn, ret);
  }
  else if (fst == modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE_UNSOUND)
  {
    // check its rewritten form
    Node bnr = rewrite(bn);
    if (!d_sampler->checkEquivalent(bn, bnr))
    {
      std::stringstream ss;
      d_sampler->checkEquivalent(bn, bnr, &ss);
      Warning() << ss.str();
      ret.push_back(bn.eqNode(bnr));
    }
  }
  else if (fst == modes::FindSynthTarget::FIND_SYNTH_TARGET_QUERY)
  {
    Assert(d_qg != nullptr);
    d_qg->addTerm(bn, ret);
  }
  if (!ret.empty())
  {
    return NodeManager::currentNM()->mkNode(kind::SEXPR, ret);
  }
  return Node::null();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
