/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/subtype_elim_node_converter.h"
#include "options/base_options.h"
#include "options/printer_options.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "printer/printer.h"
#include "proof/conv_proof_generator.h"
#include "smt/proof_manager.h"
#include "smt/solver_engine_stats.h"
#include "theory/evaluator.h"
#include "theory/quantifiers/oracle_checker.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "theory/trust_substitutions.h"
#include "util/resource_manager.h"
#include "util/statistics_registry.h"

using namespace cvc5::internal::smt;

namespace cvc5::internal {

Env::Env(NodeManager* nm, const Options* opts)
    : d_nm(nm),
      d_context(new context::Context()),
      d_userContext(new context::UserContext()),
      d_pfManager(nullptr),
      d_proofNodeManager(nullptr),
      d_rewriter(new theory::Rewriter(nm)),
      d_evalRew(nullptr),
      d_eval(nullptr),
      d_topLevelSubs(nullptr),
      d_logic(),
      d_options(),
      d_resourceManager(),
      d_uninterpretedSortOwner(theory::THEORY_UF),
      d_boolTermSkolems(d_userContext.get())
{
  if (opts != nullptr)
  {
    d_options.copyValues(*opts);
  }
  d_statisticsRegistry.reset(new StatisticsRegistry(
      d_options.base.statisticsInternal, d_options.base.statisticsAll));
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

NodeManager* Env::getNodeManager() const { return d_nm; }

void Env::finishInit(smt::PfManager* pm)
{
  if (pm != nullptr)
  {
    d_pfManager = pm;
    Assert(d_proofNodeManager == nullptr);
    d_proofNodeManager = pm->getProofNodeManager();
    d_rewriter->finishInit(*this);
  }
  d_topLevelSubs.reset(
      new theory::TrustSubstitutionMap(*this, d_userContext.get()));

  if (d_options.quantifiers.oracles)
  {
    d_ochecker.reset(new theory::quantifiers::OracleChecker(*this));
  }
}

void Env::shutdown()
{
  d_rewriter.reset(nullptr);
  // d_resourceManager must be destroyed before d_statisticsRegistry
  d_resourceManager.reset(nullptr);
}

context::Context* Env::getContext() { return d_context.get(); }

context::UserContext* Env::getUserContext() { return d_userContext.get(); }

smt::PfManager* Env::getProofManager() { return d_pfManager; }

ProofLogger* Env::getProofLogger()
{
  return d_pfManager ? d_pfManager->getProofLogger() : nullptr;
}

ProofNodeManager* Env::getProofNodeManager() { return d_proofNodeManager; }

bool Env::isProofProducing() const { return d_proofNodeManager != nullptr; }

bool Env::isSatProofProducing() const
{
  return d_proofNodeManager != nullptr
         && d_options.smt.proofMode != options::ProofMode::PP_ONLY;
}

bool Env::isTheoryProofProducing() const
{
  return d_proofNodeManager != nullptr
         && (d_options.smt.proofMode == options::ProofMode::FULL
             || d_options.smt.proofMode == options::ProofMode::FULL_STRICT);
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
  if (idr == MethodId::RW_EXT_REWRITE_AGG)
  {
    return d_rewriter->extendedRewrite(n, true);
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
  theory::TheoryId tid = theory::Theory::theoryOf(node,
                                  d_options.theory.theoryOfMode,
                                  d_uninterpretedSortOwner);
  // Special case: Boolean term skolems belong to THEORY_UF.
  if (tid==theory::TheoryId::THEORY_BOOL && isBooleanTermSkolem(node))
  {
    return theory::TheoryId::THEORY_UF;
  }
  return tid;
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

void Env::addPlugin(Plugin* p) { d_plugins.push_back(p); }
const std::vector<Plugin*>& Env::getPlugins() const { return d_plugins; }

theory::quantifiers::OracleChecker* Env::getOracleChecker() const
{
  return d_ochecker.get();
}

void Env::registerBooleanTermSkolem(const Node& k)
{
  Assert(k.isVar());
  d_boolTermSkolems.insert(k);
}

bool Env::isBooleanTermSkolem(const Node& k) const
{
  // optimization: check whether k is a variable
  if (!k.isVar())
  {
    return false;
  }
  return d_boolTermSkolems.find(k) != d_boolTermSkolems.end();
}

Node Env::getSharableFormula(const Node& n) const
{
  Node on = n;
  if (!d_options.base.pluginShareSkolems)
  {
    // note we only remove purify skolems if the above option is disabled
    on = SkolemManager::getOriginalForm(n);
  }
  SkolemManager * skm = d_nm->getSkolemManager();
  std::vector<Node> toProcess;
  toProcess.push_back(on);
  // The set of kinds that we never want to share. Any kind that can appear
  // in lemmas but we don't have API support for should go in this list.
  const std::unordered_set<Kind> excludeKinds = {
      Kind::INST_CONSTANT,
      Kind::DUMMY_SKOLEM,
      Kind::CARDINALITY_CONSTRAINT,
      Kind::COMBINED_CARDINALITY_CONSTRAINT};
  size_t index = 0;
  do
  {
    Node nn = toProcess[index];
    index++;
    // get the symbols contained in nn
    std::unordered_set<Node> syms;
    expr::getSymbols(nn, syms);
    for (const Node& s : syms)
    {
      Kind sk = s.getKind();
      if (excludeKinds.find(sk) != excludeKinds.end())
      {
        // these kinds are never sharable
        return Node::null();
      }
      if (sk == Kind::SKOLEM)
      {
        if (!d_options.base.pluginShareSkolems)
        {
          // not shared if option is false
          return Node::null();
        }
        // must ensure that the indices of the skolem are also legal
        SkolemId id;
        Node cacheVal;
        if (!skm->isSkolemFunction(s, id, cacheVal))
        {
          // kind SKOLEM should imply that it is a skolem function
          Assert(false);
          return Node::null();
        }
        if (!cacheVal.isNull()
            && std::find(toProcess.begin(), toProcess.end(), cacheVal)
                   == toProcess.end())
        {
          // if we have a cache value, add it to process vector
          toProcess.push_back(cacheVal);
        }
      }
    }
  } while (index < toProcess.size());
  // If we didn't encounter an illegal term, we now eliminate subtyping
  SubtypeElimNodeConverter senc(d_nm);
  on = senc.convert(on);
  return on;
}

}  // namespace cvc5::internal
