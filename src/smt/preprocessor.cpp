/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "printer/printer.h"
#include "smt/assertions.h"
#include "smt/env.h"
#include "smt/preprocess_proof_generator.h"
#include "theory/rewriter.h"

using namespace std;
using namespace cvc5::internal::theory;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace smt {

Preprocessor::Preprocessor(Env& env,
                           SolverEngineStatistics& stats)
    : EnvObj(env),
      d_pppg(nullptr),
      d_propagator(env, true, true),
      d_assertionsProcessed(env.getUserContext(), false),
      d_processor(env, stats)
{

}

Preprocessor::~Preprocessor() {}

void Preprocessor::finishInit(TheoryEngine* te, prop::PropEngine* pe)
{
  // set up the preprocess proof generator, if necessary
  if (options().smt.produceProofs && d_pppg == nullptr)
  {
    d_pppg = std::make_unique<PreprocessProofGenerator>(
        d_env, userContext(), "smt::PreprocessProofGenerator");
    d_propagator.enableProofs(userContext(), d_pppg.get());
  }

  d_ppContext.reset(new preprocessing::PreprocessingPassContext(
      d_env, te, pe, &d_propagator));

  // initialize the preprocessing passes
  d_processor.finishInit(d_ppContext.get());
}

bool Preprocessor::process(preprocessing::AssertionPipeline& ap)
{
  if (ap.size() == 0)
  {
    // nothing to do
    return true;
  }
  if (d_assertionsProcessed && options().base.incrementalSolving)
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
  bool noConflict = d_processor.apply(ap);

  // now, post-process the assertions

  // if incremental, compute which variables are assigned
  if (options().base.incrementalSolving)
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

std::vector<Node> Preprocessor::getLearnedLiterals() const
{
  if (d_ppContext == nullptr)
  {
    return {};
  }
  return d_ppContext->getLearnedLiterals();
}

void Preprocessor::cleanup() { d_processor.cleanup(); }

Node Preprocessor::applySubstitutions(const Node& node)
{
  return d_env.getTopLevelSubstitutions().apply(node);
}

void Preprocessor::applySubstitutions(std::vector<Node>& ns)
{
  for (size_t i = 0, nasserts = ns.size(); i < nasserts; i++)
  {
    ns[i] = applySubstitutions(ns[i]);
  }
}

PreprocessProofGenerator* Preprocessor::getPreprocessProofGenerator()
{
  return d_pppg.get();
}

}  // namespace smt
}  // namespace cvc5::internal
