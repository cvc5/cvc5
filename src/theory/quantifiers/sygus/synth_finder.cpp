/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Synthesis finder
 */

#include "theory/quantifiers/sygus/synth_finder.h"

#include "expr/sygus_term_enumerator.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "smt/env.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/candidate_rewrite_database.h"
#include "theory/quantifiers/query_generator_sample_sat.h"
#include "theory/quantifiers/query_generator_unsat.h"
#include "theory/quantifiers/rewrite_verifier.h"
#include "theory/quantifiers/sygus/print_sygus_to_builtin.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_enumerator_callback.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SynthFinder::SynthFinder(Env& env) : EnvObj(env), d_current(nullptr) {}

void SynthFinder::initialize(modes::FindSynthTarget fst, const TypeNode& gtn)
{
  // should be a sygus datatype
  Assert(!gtn.isNull() && gtn.isDatatype() && gtn.getDType().isSygus());
  d_fst = fst;
  d_fstu = fst;
  // rewrites from input use the same algorithm
  if (d_fstu == modes::FindSynthTarget::REWRITE_INPUT)
  {
    d_fstu = modes::FindSynthTarget::REWRITE;
  }

  // clear the buffer
  d_bufferIndex = 0;
  d_buffer.clear();

  // initialize the enumerator with the given callback, which also will ensure
  // that expanded definition forms are set on gtn.
  d_enum.reset(new SygusTermEnumerator(d_env, gtn, d_ecb.get()));

  // initialize the expression miner
  initializeInternal(d_fstu, gtn);
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

/**
 * A callback that does not do symmetry breaking based on rewriting.
 */
class SygusEnumeratorCallbackNoSym : public SygusEnumeratorCallback
{
 public:
  SygusEnumeratorCallbackNoSym(Env& env) : SygusEnumeratorCallback(env) {}

 protected:
  /**
   * Get the cache value for the given candidate, which returns bn itself,
   * without invoking the rewriter.
   */
  Node getCacheValue(const Node& n, const Node& bn) override { return bn; }
};

void SynthFinder::initializeInternal(modes::FindSynthTarget fst,
                                     const TypeNode& gtn)
{
  options::SygusQueryGenMode qmode = options().quantifiers.sygusQueryGen;

  // get the sygus variables from the type of the enumerator
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
  if (fst == modes::FindSynthTarget::REWRITE
      || fst == modes::FindSynthTarget::REWRITE_UNSOUND)
  {
    needsSampler = true;
  }
  else if (fst == modes::FindSynthTarget::QUERY)
  {
    needsSampler = (qmode == options::SygusQueryGenMode::SAMPLE_SAT);
  }
  d_sampler = nullptr;
  if (needsSampler)
  {
    d_sampler.reset(new SygusSampler(d_env));
    d_sampler->initializeSygus(gtn, nsamples);
  }

  // initialize the sygus enumerator callback if necessary
  d_ecb = nullptr;
  if (fst == modes::FindSynthTarget::REWRITE_UNSOUND)
  {
    d_ecb.reset(new SygusEnumeratorCallbackNoSym(d_env));
  }

  // now, setup the handlers
  if (fst == modes::FindSynthTarget::ENUM)
  {
    d_eid.reset(new ExprMinerId(d_env));
    d_current = d_eid.get();
  }
  else if (fst == modes::FindSynthTarget::REWRITE)
  {
    d_crd.reset(
        new CandidateRewriteDatabase(d_env,
                                     options().quantifiers.sygusRewSynthCheck,
                                     false,
                                     true,
                                     options().quantifiers.sygusRewSynthRec));
    d_current = d_crd.get();
  }
  else if (fst == modes::FindSynthTarget::REWRITE_UNSOUND)
  {
    d_rrv.reset(new RewriteVerifier(d_env));
    d_current = d_rrv.get();
  }
  else if (fst == modes::FindSynthTarget::QUERY)
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
    d_current = d_qg.get();
  }
  else
  {
    Unhandled() << "Unknown find synthesis target " << fst;
  }
  // initialize
  if (d_current != nullptr)
  {
    d_current->initialize(vars, d_sampler.get());
  }
}

Node SynthFinder::runNext(const Node& n, modes::FindSynthTarget fst)
{
  // if we already have a solution from a previous call that was buffered
  if (d_bufferIndex < d_buffer.size())
  {
    Node ret = d_buffer[d_bufferIndex];
    d_bufferIndex++;
    return ret;
  }
  d_bufferIndex = 0;
  d_buffer.clear();
  Node bn = datatypes::utils::sygusToBuiltin(n, true);
  Trace("synth-finder") << "runNext " << d_fstu << " " << bn << std::endl;
  // run the expression miner
  Assert(d_current != nullptr);
  d_current->addTerm(bn, d_buffer);
  // return null if empty
  if (d_buffer.empty())
  {
    return Node::null();
  }
  // ENUM is the only find synth target that makes sense to print grammar terms
  // with; the others return terms that do not coincide with the enumerated
  // term.
  if (fst == modes::FindSynthTarget::ENUM)
  {
    if (isOutputOn(OutputTag::SYGUS_SOL_GTERM))
    {
      Node psol = getPrintableSygusToBuiltin(n);
      d_env.output(OutputTag::SYGUS_SOL_GTERM)
          << "(sygus-sol-gterm " << psol << " :" << fst << ")" << std::endl;
    }
  }
  d_bufferIndex = 1;
  return d_buffer[0];
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
