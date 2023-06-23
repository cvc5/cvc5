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
 * Smt Environment, main access to global utilities available to
 * internal code.
 */

#include "smt/env.h"

#include "context/context.h"
#include "expr/node.h"
#include "options/base_options.h"
#include "options/printer_options.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "printer/printer.h"
#include "proof/conv_proof_generator.h"
#include "smt/solver_engine_stats.h"
#include "theory/evaluator.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "theory/trust_substitutions.h"
#include "util/resource_manager.h"
#include "util/statistics_registry.h"

using namespace cvc5::internal::smt;

namespace cvc5::internal {

Env::Env(const Options* opts)
    : d_context(new context::Context()),
      d_userContext(new context::UserContext()),
      d_proofNodeManager(nullptr),
      d_rewriter(new theory::Rewriter()),
      d_evalRew(nullptr),
      d_eval(nullptr),
      d_topLevelSubs(nullptr),
      d_logic(),
      d_statisticsRegistry(std::make_unique<StatisticsRegistry>(*this)),
      d_options(),
      d_resourceManager(),
      d_uninterpretedSortOwner(theory::THEORY_UF)
{
  if (opts != nullptr)
  {
    d_options.copyValues(*opts);
  }
  // make the evaluators, which depend on the alphabet of strings
  d_evalRew.reset(new theory::Evaluator(d_rewriter.get(),
                                        d_options.strings.stringsAlphaCard));
  d_eval.reset(
      new theory::Evaluator(nullptr, d_options.strings.stringsAlphaCard));
  d_statisticsRegistry->registerTimer("global::totalTime").start();
  d_resourceManager = std::make_unique<ResourceManager>(*d_statisticsRegistry, d_options);
  d_rewriter->d_resourceManager = d_resourceManager.get();
}

Env::~Env() {}

void Env::finishInit(ProofNodeManager* pnm)
{
  if (pnm != nullptr)
  {
    Assert(d_proofNodeManager == nullptr);
    d_proofNodeManager = pnm;
    d_rewriter->finishInit(*this);
  }
  d_topLevelSubs.reset(
      new theory::TrustSubstitutionMap(*this, d_userContext.get()));
}

void Env::shutdown()
{
  d_rewriter.reset(nullptr);
  // d_resourceManager must be destroyed before d_statisticsRegistry
  d_resourceManager.reset(nullptr);
}

context::Context* Env::getContext() { return d_context.get(); }

context::UserContext* Env::getUserContext() { return d_userContext.get(); }

ProofNodeManager* Env::getProofNodeManager() { return d_proofNodeManager; }

bool Env::isSatProofProducing() const
{
  return d_proofNodeManager != nullptr
         && d_options.smt.proofMode != options::ProofMode::PP_ONLY;
}

bool Env::isTheoryProofProducing() const
{
  return d_proofNodeManager != nullptr
         && d_options.smt.proofMode == options::ProofMode::FULL;
}

theory::Rewriter* Env::getRewriter() { return d_rewriter.get(); }

theory::Evaluator* Env::getEvaluator(bool useRewriter)
{
  return useRewriter ? d_evalRew.get() : d_eval.get();
}

theory::TrustSubstitutionMap& Env::getTopLevelSubstitutions()
{
  return *d_topLevelSubs.get();
}

const LogicInfo& Env::getLogicInfo() const { return d_logic; }

StatisticsRegistry& Env::getStatisticsRegistry()
{
  return *d_statisticsRegistry;
}

const Options& Env::getOptions() const { return d_options; }

ResourceManager* Env::getResourceManager() const
{
  return d_resourceManager.get();
}

bool Env::isOutputOn(OutputTag tag) const
{
  return d_options.base.outputTagHolder[static_cast<size_t>(tag)];
}
bool Env::isOutputOn(const std::string& tag) const
{
  return isOutputOn(options::stringToOutputTag(tag));
}
std::ostream& Env::output(const std::string& tag) const
{
  return output(options::stringToOutputTag(tag));
}

std::ostream& Env::output(OutputTag tag) const
{
  if (isOutputOn(tag))
  {
    return *d_options.base.out;
  }
  return cvc5::internal::null_os;
}

bool Env::isVerboseOn(int64_t level) const
{
  return !Configuration::isMuzzledBuild() && d_options.base.verbosity >= level;
}

std::ostream& Env::verbose(int64_t level) const
{
  if (isVerboseOn(level))
  {
    return *d_options.base.err;
  }
  return cvc5::internal::null_os;
}

std::ostream& Env::warning() const
{
  return verbose(0);
}

Node Env::evaluate(TNode n,
                   const std::vector<Node>& args,
                   const std::vector<Node>& vals,
                   bool useRewriter) const
{
  std::unordered_map<Node, Node> visited;
  return evaluate(n, args, vals, visited, useRewriter);
}

Node Env::evaluate(TNode n,
                   const std::vector<Node>& args,
                   const std::vector<Node>& vals,
                   const std::unordered_map<Node, Node>& visited,
                   bool useRewriter) const
{
  if (useRewriter)
  {
    return d_evalRew->eval(n, args, vals, visited);
  }
  return d_eval->eval(n, args, vals, visited);
}

Node Env::rewriteViaMethod(TNode n, MethodId idr)
{
  if (idr == MethodId::RW_REWRITE)
  {
    return d_rewriter->rewrite(n);
  }
  if (idr == MethodId::RW_EXT_REWRITE)
  {
    return d_rewriter->extendedRewrite(n);
  }
  if (idr == MethodId::RW_REWRITE_EQ_EXT)
  {
    return d_rewriter->rewriteEqualityExt(n);
  }
  if (idr == MethodId::RW_EVALUATE)
  {
    return evaluate(n, {}, {}, false);
  }
  if (idr == MethodId::RW_IDENTITY)
  {
    // does nothing
    return n;
  }
  // unknown rewriter
  Unhandled() << "Env::rewriteViaMethod: no rewriter for " << idr
              << std::endl;
  return n;
}

bool Env::isFiniteType(TypeNode tn) const
{
  return isCardinalityClassFinite(tn.getCardinalityClass(),
                                  d_options.quantifiers.finiteModelFind);
}

void Env::setUninterpretedSortOwner(theory::TheoryId theory)
{
  d_uninterpretedSortOwner = theory;
}

theory::TheoryId Env::getUninterpretedSortOwner() const
{
  return d_uninterpretedSortOwner;
}

theory::TheoryId Env::theoryOf(TypeNode typeNode) const
{
  return theory::Theory::theoryOf(typeNode, d_uninterpretedSortOwner);
}

theory::TheoryId Env::theoryOf(TNode node) const
{
  return theory::Theory::theoryOf(
      node, d_options.theory.theoryOfMode, d_uninterpretedSortOwner);
}

bool Env::hasSepHeap() const { return !d_sepLocType.isNull(); }

TypeNode Env::getSepLocType() const { return d_sepLocType; }

TypeNode Env::getSepDataType() const { return d_sepDataType; }

void Env::declareSepHeap(TypeNode locT, TypeNode dataT)
{
  Assert(!locT.isNull());
  Assert(!dataT.isNull());
  // remember the types we have set
  d_sepLocType = locT;
  d_sepDataType = dataT;
}

}  // namespace cvc5::internal
