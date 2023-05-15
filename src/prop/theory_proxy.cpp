/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */
#include "prop/theory_proxy.h"

#include "context/context.h"
#include "decision/decision_engine.h"
#include "decision/justification_strategy.h"
#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/decision_options.h"
#include "options/parallel_options.h"
#include "options/prop_options.h"
#include "options/smt_options.h"
#include "prop/cnf_stream.h"
#include "prop/proof_cnf_stream.h"
#include "prop/prop_engine.h"
#include "prop/skolem_def_manager.h"
#include "prop/zero_level_learner.h"
#include "smt/env.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace prop {

TheoryProxy::TheoryProxy(Env& env,
                         PropEngine* propEngine,
                         TheoryEngine* theoryEngine,
                         SkolemDefManager* skdm)
    : EnvObj(env),
      d_propEngine(propEngine),
      d_cnfStream(nullptr),
      d_decisionEngine(nullptr),
      d_trackActiveSkDefs(false),
      d_theoryEngine(theoryEngine),
      d_queue(context()),
      d_tpp(env, *theoryEngine),
      d_skdm(skdm),
      d_zll(nullptr),
      d_prr(nullptr),
      d_stopSearch(userContext(), false),
      d_activatedSkDefs(false)
{
  bool trackZeroLevel =
      options().smt.deepRestartMode != options::DeepRestartMode::NONE
      || isOutputOn(OutputTag::LEARNED_LITS)
      || options().smt.produceLearnedLiterals
      || options().parallel.computePartitions > 0;
  if (trackZeroLevel)
  {
    d_zll = std::make_unique<ZeroLevelLearner>(env, theoryEngine);
  }
}

TheoryProxy::~TheoryProxy() {
  /* nothing to do for now */
}

void TheoryProxy::finishInit(CDCLTSatSolver* ss, CnfStream* cs)
{
  // make the decision engine, which requires pointers to the SAT solver and CNF
  // stream
  options::DecisionMode dmode = options().decision.decisionMode;
  if (dmode == options::DecisionMode::JUSTIFICATION
      || dmode == options::DecisionMode::STOPONLY)
  {
    d_decisionEngine.reset(new decision::JustificationStrategy(d_env, ss, cs));
  }
  else
  {
    d_decisionEngine.reset(new decision::DecisionEngineEmpty(d_env));
  }
  // make the theory preregistrar
  d_prr.reset(new TheoryPreregistrar(d_env, d_theoryEngine, ss, cs));
  // compute if we need to track skolem definitions
  d_trackActiveSkDefs = d_decisionEngine->needsActiveSkolemDefs()
                        || d_prr->needsActiveSkolemDefs();
  d_cnfStream = cs;
}

void TheoryProxy::presolve()
{
  d_decisionEngine->presolve();
  d_theoryEngine->presolve();
  d_stopSearch = false;
}

void TheoryProxy::postsolve() { d_theoryEngine->postsolve(); }

void TheoryProxy::notifyTopLevelSubstitution(const Node& lhs,
                                             const Node& rhs) const
{
  if (d_zll != nullptr)
  {
    d_zll->notifyTopLevelSubstitution(lhs, rhs);
  }
}

void TheoryProxy::notifyInputFormulas(
    const std::vector<Node>& assertions,
    std::unordered_map<size_t, Node>& skolemMap)
{
  // notify the theory engine of preprocessed assertions
  d_theoryEngine->notifyPreprocessedAssertions(assertions);
  // Now, notify the theory proxy of the assertions and skolem definitions.
  // Notice we do this before asserting the formulas to the CNF stream below,
  // since (preregistration) lemmas may occur during calls to assertInternal.
  // These lemmas we want to be notified about after the theory proxy has
  // been notified about all input assertions.
  std::unordered_map<size_t, Node>::iterator it;
  for (size_t i = 0, asize = assertions.size(); i < asize; i++)
  {
    // is the assertion a skolem definition?
    it = skolemMap.find(i);
    Node skolem;
    if (it != skolemMap.end())
    {
      skolem = it->second;
    }
    if (!skolem.isNull())
    {
      notifySkolemDefinition(assertions[i], skolem);
    }
    notifyAssertion(assertions[i], skolem, false);
  }

  // the zero-level learner needs to be notified of the input assertions, to
  // determine what is learnable
  if (d_zll != nullptr)
  {
    d_zll->notifyInputFormulas(assertions);
  }
}

void TheoryProxy::notifySkolemDefinition(Node a, TNode skolem)
{
  Assert(!skolem.isNull());
  d_skdm->notifySkolemDefinition(skolem, a);
}

void TheoryProxy::notifyAssertion(Node a, TNode skolem, bool isLemma)
{
  // ignore constants
  if (a.isConst())
  {
    return;
  }
  // notify the decision engine
  d_decisionEngine->addAssertion(a, skolem, isLemma);
  // notify the preregistrar
  d_prr->addAssertion(a, skolem, isLemma);
}

void TheoryProxy::variableNotify(SatVariable var) {
  notifySatLiteral(getNode(SatLiteral(var)));
}

void TheoryProxy::theoryCheck(theory::Theory::Effort effort) {
  Trace("theory-proxy") << "TheoryProxy: check " << effort << std::endl;
  d_activatedSkDefs = false;
  // check with the preregistrar
  d_prr->check();
  TNode assertion;
  int32_t alevel;
  while (!d_queue.empty())
  {
    std::tie(assertion, alevel) = d_queue.front();
    d_queue.pop();
    if (d_zll != nullptr)
    {
      if (d_stopSearch.get())
      {
        break;
      }
      if (!d_zll->notifyAsserted(assertion, alevel))
      {
        d_stopSearch = true;
        break;
      }
    }
    // notify the preregister utility, which may trigger new preregistrations
    if (!d_prr->notifyAsserted(assertion))
    {
      // the preregistrar determined we should not assert this assertion, which
      // can be the case for Boolean variables that we are notified about for
      // the purposes of updating justification when using preregistration
      // mode relevant.
      continue;
    }
    // now, assert to theory engine
    Trace("prereg") << "assert: " << assertion << std::endl;
    d_theoryEngine->assertFact(assertion);
    if (d_trackActiveSkDefs)
    {
      Assert(d_skdm != nullptr);
      // Assertion makes all skolems in assertion active,
      // which triggers their definitions to becoming active.
      std::vector<TNode> activeSkolemDefs;
      d_skdm->notifyAsserted(assertion, activeSkolemDefs);
      if (!activeSkolemDefs.empty())
      {
        // notify the decision engine of the skolem definitions that have become
        // active due to the assertion.
        d_decisionEngine->notifyActiveSkolemDefs(activeSkolemDefs);
        d_prr->notifyActiveSkolemDefs(activeSkolemDefs);
        // if we are doing a FULL effort check (propagating with no remaining
        // decisions) and a new skolem definition becomes active, then the SAT
        // assignment is not complete.
        if (effort == theory::Theory::EFFORT_FULL)
        {
          Trace("theory-proxy") << "...change check to STANDARD!" << std::endl;
          effort = theory::Theory::EFFORT_STANDARD;
        }
        d_activatedSkDefs = true;
      }
    }
  }
  if (!d_stopSearch.get())
  {
    d_theoryEngine->check(effort);
  }
}

void TheoryProxy::theoryPropagate(std::vector<SatLiteral>& output) {
  // Get the propagated literals
  std::vector<TNode> outputNodes;
  d_theoryEngine->getPropagatedLiterals(outputNodes);
  for (unsigned i = 0, i_end = outputNodes.size(); i < i_end; ++ i) {
    Trace("prop-explain") << "theoryPropagate() => " << outputNodes[i] << std::endl;
    output.push_back(d_cnfStream->getLiteral(outputNodes[i]));
  }
}

void TheoryProxy::explainPropagation(SatLiteral l, SatClause& explanation) {
  TNode lNode = d_cnfStream->getNode(l);
  Trace("prop-explain") << "explainPropagation(" << lNode << ")" << std::endl;

  TrustNode tte = d_theoryEngine->getExplanation(lNode);
  Node theoryExplanation = tte.getNode();
  if (d_env.isSatProofProducing())
  {
    Assert(options().smt.proofMode != options::ProofMode::FULL
           || tte.getGenerator());
    d_propEngine->getProofCnfStream()->convertPropagation(tte);
  }
  Trace("prop-explain") << "explainPropagation() => " << theoryExplanation
                        << std::endl;
  explanation.push_back(l);
  if (theoryExplanation.getKind() == kind::AND)
  {
    for (const Node& n : theoryExplanation)
    {
      explanation.push_back(~d_cnfStream->getLiteral(n));
    }
  }
  else
  {
    explanation.push_back(~d_cnfStream->getLiteral(theoryExplanation));
  }
  if (TraceIsOn("sat-proof"))
  {
    std::stringstream ss;
    ss << "TheoryProxy::explainPropagation: clause for lit is ";
    for (unsigned i = 0, size = explanation.size(); i < size; ++i)
    {
      ss << explanation[i] << " [" << d_cnfStream->getNode(explanation[i])
         << "] ";
    }
    Trace("sat-proof") << ss.str() << "\n";
  }
}

void TheoryProxy::notifyCurrPropagationInsertedAtLevel(int explLevel)
{
  d_propEngine->getProofCnfStream()->notifyCurrPropagationInsertedAtLevel(
      explLevel);
}

void TheoryProxy::notifyClauseInsertedAtLevel(const SatClause& clause,
                                              int clLevel)
{
  d_propEngine->getProofCnfStream()->notifyClauseInsertedAtLevel(clause,
                                                                 clLevel);
}

void TheoryProxy::enqueueTheoryLiteral(const SatLiteral& l) {
  Node literalNode = d_cnfStream->getNode(l);
  Trace("prop") << "enqueueing theory literal " << l << " " << literalNode << std::endl;
  Assert(!literalNode.isNull());
  // Decision level = SAT context level - 1 due to global push().
  d_queue.push(std::make_pair(literalNode, context()->getLevel() - 1));
}

SatLiteral TheoryProxy::getNextTheoryDecisionRequest() {
  TNode n = d_theoryEngine->getNextDecisionRequest();
  return n.isNull() ? undefSatLiteral : d_cnfStream->getLiteral(n);
}

SatLiteral TheoryProxy::getNextDecisionEngineRequest(bool &stopSearch) {
  Assert(d_decisionEngine != NULL);
  Assert(stopSearch != true);
  Trace("theory-proxy") << "TheoryProxy: getNextDecisionEngineRequest"
                        << std::endl;
  if (d_stopSearch.get())
  {
    Trace("theory-proxy") << "...stopped search, finish" << std::endl;
    stopSearch = true;
    return undefSatLiteral;
  }
  SatLiteral ret = d_decisionEngine->getNext(stopSearch);
  if(stopSearch) {
    Trace("theory-proxy") << "  ***  Decision Engine stopped search *** "
                          << std::endl;
  }
  else
  {
    Trace("theory-proxy") << "...returned next decision" << std::endl;
  }
  return ret;
}

bool TheoryProxy::theoryNeedCheck() const {
  if (d_stopSearch.get())
  {
    return false;
  }
  else if (d_activatedSkDefs)
  {
    // a new skolem definition become active on the last call to theoryCheck,
    // return true
    return true;
  }
  // otherwise ask the theory engine, which will return true if its output
  // channel was used.
  bool needCheck = d_theoryEngine->needCheck();
  Trace("theory-proxy") << "TheoryProxy: theoryNeedCheck returns " << needCheck
                        << std::endl;
  return needCheck;
}

bool TheoryProxy::isModelUnsound() const
{
  return d_stopSearch.get() || d_theoryEngine->isModelUnsound();
}

bool TheoryProxy::isRefutationUnsound() const
{
  return d_theoryEngine->isRefutationUnsound();
}

theory::IncompleteId TheoryProxy::getModelUnsoundId() const
{
  if (d_stopSearch.get())
  {
    return theory::IncompleteId::STOP_SEARCH;
  }
  return d_theoryEngine->getModelUnsoundId();
}

theory::IncompleteId TheoryProxy::getRefutationUnsoundId() const
{
  return d_theoryEngine->getRefutationUnsoundId();
}

TNode TheoryProxy::getNode(SatLiteral lit) {
  return d_cnfStream->getNode(lit);
}

void TheoryProxy::notifyRestart() {
  d_propEngine->spendResource(Resource::RestartStep);
  d_theoryEngine->notifyRestart();
}

void TheoryProxy::spendResource(Resource r)
{
  d_theoryEngine->spendResource(r);
}

bool TheoryProxy::isDecisionRelevant(SatVariable var) { return true; }

bool TheoryProxy::isDecisionEngineDone() {
  return d_decisionEngine->isDone() || d_stopSearch.get();
}

SatValue TheoryProxy::getDecisionPolarity(SatVariable var) {
  return SAT_VALUE_UNKNOWN;
}

CnfStream* TheoryProxy::getCnfStream() { return d_cnfStream; }

TrustNode TheoryProxy::preprocessLemma(
    TrustNode trn, std::vector<theory::SkolemLemma>& newLemmas)
{
  return d_tpp.preprocessLemma(trn, newLemmas);
}

TrustNode TheoryProxy::preprocess(TNode node,
                                  std::vector<theory::SkolemLemma>& newLemmas)
{
  return d_tpp.preprocess(node, newLemmas);
}

TrustNode TheoryProxy::removeItes(TNode node,
                                  std::vector<theory::SkolemLemma>& newLemmas)
{
  RemoveTermFormulas& rtf = d_tpp.getRemoveTermFormulas();
  return rtf.run(node, newLemmas, true);
}

void TheoryProxy::getSkolems(TNode node,
                             std::vector<Node>& skAsserts,
                             std::vector<Node>& sks)
{
  std::unordered_set<Node> skolems;
  d_skdm->getSkolems(node, skolems);
  for (const Node& k : skolems)
  {
    sks.push_back(k);
    skAsserts.push_back(d_skdm->getDefinitionForSkolem(k));
  }
}

void TheoryProxy::notifySatLiteral(Node n)
{
  // notify the preregister utility, which may trigger new preregistrations
  d_prr->notifySatLiteral(n);
}

void TheoryProxy::notifyBacktrack(uint32_t nlevels)
{
  // notify the preregistrar, which may trigger reregistrations
  d_prr->notifyBacktrack(nlevels);
}

std::vector<Node> TheoryProxy::getLearnedZeroLevelLiterals(
    modes::LearnedLitType ltype) const
{
  if (d_zll != nullptr)
  {
    return d_zll->getLearnedZeroLevelLiterals(ltype);
  }
  return {};
}

modes::LearnedLitType TheoryProxy::getLiteralType(const Node& lit) const
{
  if (d_zll != nullptr)
  {
    return d_zll->computeLearnedLiteralType(lit);
  }
  return modes::LEARNED_LIT_UNKNOWN;
}

std::vector<Node> TheoryProxy::getLearnedZeroLevelLiteralsForRestart() const
{
  if (d_zll != nullptr)
  {
    return d_zll->getLearnedZeroLevelLiteralsForRestart();
  }
  return {};
}

}  // namespace prop
}  // namespace cvc5::internal
