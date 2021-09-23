/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The preprocessor of the SMT engine.
 */

#include "smt/preprocessor.h"

#include "options/base_options.h"
#include "options/expr_options.h"
#include "options/smt_options.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "printer/printer.h"
#include "smt/abstract_values.h"
#include "smt/assertions.h"
#include "smt/dump.h"
#include "smt/env.h"
#include "smt/preprocess_proof_generator.h"
#include "smt/smt_engine.h"
#include "theory/rewriter.h"

using namespace std;
using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
namespace smt {

Preprocessor::Preprocessor(SmtEngine& smt,
                           Env& env,
                           AbstractValues& abs,
                           SmtEngineStatistics& stats)
    : d_smt(smt),
      d_env(env),
      d_absValues(abs),
      d_propagator(true, true),
      d_assertionsProcessed(env.getUserContext(), false),
      d_exDefs(env, stats),
      d_processor(smt, *env.getResourceManager(), stats),
      d_pnm(nullptr)
{
}

Preprocessor::~Preprocessor()
{
  if (d_propagator.getNeedsFinish())
  {
    d_propagator.finish();
    d_propagator.setNeedsFinish(false);
  }
}

void Preprocessor::finishInit()
{
  d_ppContext.reset(new preprocessing::PreprocessingPassContext(
      &d_smt, d_env, &d_propagator));

  // initialize the preprocessing passes
  d_processor.finishInit(d_ppContext.get());
}

bool Preprocessor::process(Assertions& as)
{
  preprocessing::AssertionPipeline& ap = as.getAssertionPipeline();

  // should not be called if empty
  Assert(ap.size() != 0)
      << "Can only preprocess a non-empty list of assertions";

  if (d_assertionsProcessed && options::incrementalSolving())
  {
    // TODO(b/1255): Substitutions in incremental mode should be managed with a
    // proper data structure.
    ap.enableStoreSubstsInAsserts();
  }
  else
  {
    ap.disableStoreSubstsInAsserts();
  }

  // process the assertions, return true if no conflict is discovered
  bool noConflict = d_processor.apply(as);

  // now, post-process the assertions

  // if incremental, compute which variables are assigned
  if (options::incrementalSolving())
  {
    d_ppContext->recordSymbolsInAssertions(ap.ref());
  }

  // mark that we've processed assertions
  d_assertionsProcessed = true;

  return noConflict;
}

void Preprocessor::clearLearnedLiterals()
{
  d_propagator.getLearnedLiterals().clear();
}

void Preprocessor::cleanup() { d_processor.cleanup(); }

Node Preprocessor::expandDefinitions(const Node& n)
{
  std::unordered_map<Node, Node> cache;
  return expandDefinitions(n, cache);
}

Node Preprocessor::expandDefinitions(const Node& node,
                                     std::unordered_map<Node, Node>& cache)
{
  Trace("smt") << "SMT expandDefinitions(" << node << ")" << endl;
  // Substitute out any abstract values in node.
  Node n = d_absValues.substituteAbstractValues(node);
  if (options::typeChecking())
  {
    // Ensure node is type-checked at this point.
    n.getType(true);
  }
  // we apply substitutions here, before expanding definitions
  n = d_env.getTopLevelSubstitutions().apply(n, false);
  // now call expand definitions
  n = d_exDefs.expandDefinitions(n, cache);
  return n;
}

void Preprocessor::expandDefinitions(std::vector<Node>& ns)
{
  std::unordered_map<Node, Node> cache;
  for (size_t i = 0, nasserts = ns.size(); i < nasserts; i++)
  {
    ns[i] = expandDefinitions(ns[i], cache);
  }
}

Node Preprocessor::simplify(const Node& node)
{
  Trace("smt") << "SMT simplify(" << node << ")" << endl;
  if (Dump.isOn("benchmark"))
  {
    d_smt.getOutputManager().getPrinter().toStreamCmdSimplify(
        d_smt.getOutputManager().getDumpOut(), node);
  }
  Node ret = expandDefinitions(node);
  ret = theory::Rewriter::rewrite(ret);
  return ret;
}

void Preprocessor::setProofGenerator(PreprocessProofGenerator* pppg)
{
  Assert(pppg != nullptr);
  d_pnm = pppg->getManager();
  d_exDefs.setProofNodeManager(d_pnm);
  d_propagator.setProof(d_pnm, d_env.getUserContext(), pppg);
}

}  // namespace smt
}  // namespace cvc5
