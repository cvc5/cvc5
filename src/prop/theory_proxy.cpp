/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "options/decision_options.h"
#include "options/smt_options.h"
#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "prop/skolem_def_manager.h"
#include "smt/env.h"
#include "smt/smt_statistics_registry.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"
#include "util/statistics_stats.h"

namespace cvc5 {
namespace prop {

TheoryProxy::TheoryProxy(Env& env,
                         PropEngine* propEngine,
                         TheoryEngine* theoryEngine,
                         decision::DecisionEngine* decisionEngine,
                         SkolemDefManager* skdm)
    : EnvObj(env),
      d_propEngine(propEngine),
      d_cnfStream(nullptr),
      d_decisionEngine(decisionEngine),
      d_dmNeedsActiveDefs(d_decisionEngine->needsActiveSkolemDefs()),
      d_theoryEngine(theoryEngine),
      d_queue(env.getContext()),
      d_tpp(env, *theoryEngine),
      d_skdm(skdm)
{
}

TheoryProxy::~TheoryProxy() {
  /* nothing to do for now */
}

void TheoryProxy::finishInit(CnfStream* cnfStream) { d_cnfStream = cnfStream; }

void TheoryProxy::presolve()
{
  d_decisionEngine->presolve();
  d_theoryEngine->presolve();
}

void TheoryProxy::notifyAssertion(Node a, TNode skolem, bool isLemma)
{
  if (skolem.isNull())
  {
    d_decisionEngine->addAssertion(a, isLemma);
  }
  else
  {
    d_skdm->notifySkolemDefinition(skolem, a);
    d_decisionEngine->addSkolemDefinition(a, skolem, isLemma);
  }
}

void TheoryProxy::variableNotify(SatVariable var) {
  d_theoryEngine->preRegister(getNode(SatLiteral(var)));
}

void TheoryProxy::theoryCheck(theory::Theory::Effort effort) {
  while (!d_queue.empty()) {
    TNode assertion = d_queue.front();
    d_queue.pop();
    // now, assert to theory engine
    d_theoryEngine->assertFact(assertion);
    if (d_dmNeedsActiveDefs)
    {
      Assert(d_skdm != nullptr);
      Trace("sat-rlv-assert")
          << "Assert to theory engine: " << assertion << std::endl;
      // Assertion makes all skolems in assertion active,
      // which triggers their definitions to becoming active.
      std::vector<TNode> activeSkolemDefs;
      d_skdm->notifyAsserted(assertion, activeSkolemDefs, true);
      // notify the decision engine of the skolem definitions that have become
      // active due to the assertion.
      d_decisionEngine->notifyActiveSkolemDefs(activeSkolemDefs);
    }
  }
  d_theoryEngine->check(effort);
}

void TheoryProxy::theoryPropagate(std::vector<SatLiteral>& output) {
  // Get the propagated literals
  std::vector<TNode> outputNodes;
  d_theoryEngine->getPropagatedLiterals(outputNodes);
  for (unsigned i = 0, i_end = outputNodes.size(); i < i_end; ++ i) {
    Debug("prop-explain") << "theoryPropagate() => " << outputNodes[i] << std::endl;
    output.push_back(d_cnfStream->getLiteral(outputNodes[i]));
  }
}

void TheoryProxy::explainPropagation(SatLiteral l, SatClause& explanation) {
  TNode lNode = d_cnfStream->getNode(l);
  Debug("prop-explain") << "explainPropagation(" << lNode << ")" << std::endl;

  TrustNode tte = d_theoryEngine->getExplanation(lNode);
  Node theoryExplanation = tte.getNode();
  if (d_env.isSatProofProducing())
  {
    Assert(options().smt.unsatCoresMode != options::UnsatCoresMode::FULL_PROOF
           || tte.getGenerator());
    d_propEngine->getProofCnfStream()->convertPropagation(tte);
  }
  Debug("prop-explain") << "explainPropagation() => " << theoryExplanation
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
  if (Trace.isOn("sat-proof"))
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

void TheoryProxy::enqueueTheoryLiteral(const SatLiteral& l) {
  Node literalNode = d_cnfStream->getNode(l);
  Debug("prop") << "enqueueing theory literal " << l << " " << literalNode << std::endl;
  Assert(!literalNode.isNull());
  d_queue.push(literalNode);
}

SatLiteral TheoryProxy::getNextTheoryDecisionRequest() {
  TNode n = d_theoryEngine->getNextDecisionRequest();
  return n.isNull() ? undefSatLiteral : d_cnfStream->getLiteral(n);
}

SatLiteral TheoryProxy::getNextDecisionEngineRequest(bool &stopSearch) {
  Assert(d_decisionEngine != NULL);
  Assert(stopSearch != true);
  SatLiteral ret = d_decisionEngine->getNext(stopSearch);
  if(stopSearch) {
    Trace("decision") << "  ***  Decision Engine stopped search *** " << std::endl;
  }
  return ret;
}

bool TheoryProxy::theoryNeedCheck() const {
  return d_theoryEngine->needCheck();
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
  return d_decisionEngine->isDone();
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

void TheoryProxy::preRegister(Node n) { d_theoryEngine->preRegister(n); }

}  // namespace prop
}  // namespace cvc5
