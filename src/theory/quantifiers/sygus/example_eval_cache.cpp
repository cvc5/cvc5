/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * This class caches the evaluation of nodes on a fixed list of examples.
 */
#include "theory/quantifiers/sygus/example_eval_cache.h"

#include "theory/quantifiers/sygus/example_min_eval.h"

using namespace cvc5::internal;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

ExampleEvalCache::ExampleEvalCache(TermDbSygus* tds,
                                   Node e)
    : d_tds(tds), d_stn(e.getType())
{
  d_indexSearchVals = !d_tds->isVariableAgnosticEnumerator(e);
}

ExampleEvalCache::~ExampleEvalCache() {}

void ExampleEvalCache::addExample(const std::vector<Node>& ex)
{
  d_examples.push_back(ex);
}

Node ExampleEvalCache::addSearchVal(TypeNode tn, Node bv)
{
  if (!d_indexSearchVals)
  {
    // not indexing search values
    return Node::null();
  }
  std::vector<Node> vals;
  evaluateVec(bv, vals, true);
  Trace("sygus-pbe-debug") << "Add to trie..." << std::endl;
  Node ret = d_trie[tn].addOrGetTerm(bv, vals);
  Trace("sygus-pbe-debug") << "...got " << ret << std::endl;
  // Only save the cache data if necessary: if the enumerated term
  // is redundant, its cached data will not be used later and thus should
  // be discarded. This applies also to the case where the evaluation
  // was cached prior to this call.
  if (ret != bv)
  {
    clearEvaluationCache(bv);
  }
  Assert(ret.getType() == bv.getType());
  return ret;
}

void ExampleEvalCache::evaluateVec(Node bv,
                                   std::vector<Node>& exOut,
                                   bool doCache)
{
  // is it in the cache?
  std::map<Node, std::vector<Node>>::iterator it = d_exOutCache.find(bv);
  if (it != d_exOutCache.end())
  {
    exOut.insert(exOut.end(), it->second.begin(), it->second.end());
    return;
  }
  // get the evaluation
  evaluateVecInternal(bv, exOut);
  // store in cache if necessary
  if (doCache)
  {
    std::vector<Node>& eocv = d_exOutCache[bv];
    eocv.insert(eocv.end(), exOut.begin(), exOut.end());
  }
}

void ExampleEvalCache::evaluateVecInternal(Node bv,
                                           std::vector<Node>& exOut) const
{
  // use ExampleMinEval
  SygusTypeInfo& ti = d_tds->getTypeInfo(d_stn);
  const std::vector<Node>& varlist = ti.getVarList();
  EmeEvalTds emetds(d_tds, d_stn);
  ExampleMinEval eme(bv, varlist, &emetds);
  for (size_t j = 0, esize = d_examples.size(); j < esize; j++)
  {
    Node res = eme.evaluate(d_examples[j]);
    exOut.push_back(res);
  }
}

Node ExampleEvalCache::evaluate(Node bn, unsigned i) const
{
  Assert(i < d_examples.size());
  return d_tds->evaluateBuiltin(d_stn, bn, d_examples[i]);
}

void ExampleEvalCache::clearEvaluationCache(Node bv)
{
  Assert(d_exOutCache.find(bv) != d_exOutCache.end());
  d_exOutCache.erase(bv);
}

void ExampleEvalCache::clearEvaluationAll() { d_exOutCache.clear(); }

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
