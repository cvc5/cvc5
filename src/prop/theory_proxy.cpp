/*********************                                                        */
/*! \file theory_proxy.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/
#include "prop/theory_proxy.h"

#include "context/context.h"
#include "decision/decision_engine.h"
#include "options/decision_options.h"
#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "proof/cnf_proof.h"
#include "proof/new_proof_manager.h"
#include "smt/command.h"
#include "smt/smt_statistics_registry.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"
#include "util/statistics_registry.h"


namespace CVC4 {
namespace prop {

TheoryProxy::TheoryProxy(PropEngine* propEngine,
                         TheoryEngine* theoryEngine,
                         DecisionEngine* decisionEngine,
                         context::Context* context,
                         CnfStream* cnfStream)
    : d_propEngine(propEngine),
      d_cnfStream(cnfStream),
      d_decisionEngine(decisionEngine),
      d_theoryEngine(theoryEngine),
      d_queue(context)
{
}

TheoryProxy::~TheoryProxy() {
  /* nothing to do for now */
}

void TheoryProxy::variableNotify(SatVariable var) {
  d_theoryEngine->preRegister(getNode(SatLiteral(var)));
}

void TheoryProxy::theoryCheck(theory::Theory::Effort effort) {
  while (!d_queue.empty()) {
    TNode assertion = d_queue.front();
    d_queue.pop();
    d_theoryEngine->assertFact(assertion);
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

  LemmaProofRecipe* proofRecipe = NULL;
  PROOF(proofRecipe = new LemmaProofRecipe;);

  theory::TrustNode tte =
      d_theoryEngine->getExplanationAndRecipe(lNode, proofRecipe);
  Node theoryExplanation = tte.getNode();

  if (CVC4::options::proofNew())
  {
    NewProofManager* pm = NewProofManager::currentPM();
    Trace("newproof-explain")
        << "TheoryProxy::explainPropagation: explanation of lit " << l << "["
        << lNode << "] is " << theoryExplanation << " to prove "
        << tte.getProven() << "\n";
    Node proven = tte.getProven();
    Assert(tte.getGenerator());
    Assert(tte.getGenerator()->getProofFor(proven));
    pm->getProof()->addProof(tte.getGenerator()->getProofFor(proven));
    Assert(proven[1] == lNode);
    NodeManager* nm = NodeManager::currentNM();

    Node clauseImpliesElim =
        nm->mkNode(kind::OR, proven[0].notNode(), proven[1]);
    Trace("newproof") << "TheoryProxy::explainPropagation: adding "
                      << PfRule::IMPLIES_ELIM << " rule to conclude "
                      << clauseImpliesElim << "\n";
    pm->addStep(clauseImpliesElim, PfRule::IMPLIES_ELIM, {proven}, {});
    // need to eliminate AND
    if (proven[0].getKind() == kind::AND)
    {
      std::vector<Node> disjunctsAndNeg{proven[0]};
      std::vector<Node> disjunctsRes;
      for (unsigned i = 0, size = proven[0].getNumChildren(); i < size; ++i)
      {
        disjunctsAndNeg.push_back(proven[0][i].notNode());
        disjunctsRes.push_back(proven[0][i].notNode());
      }
      disjunctsRes.push_back(proven[1]);
      Node clauseAndNeg = nm->mkNode(kind::OR, disjunctsAndNeg);
      // add proof steps to convert into clause
      pm->addStep(clauseAndNeg, PfRule::CNF_AND_NEG, {}, {proven[0]});
      Node clauseRes = nm->mkNode(kind::OR, disjunctsRes);
      pm->addStep(clauseRes,
                  PfRule::RESOLUTION,
                  {clauseAndNeg, clauseImpliesElim},
                  {proven[0]});
      // Rewrite clauseNode before proceeding. This is so ordering/factoring is
      // consistent with the clause that is added to the SAT solver
      Node clauseExplanation = pm->factorAndReorder(clauseRes);
      Trace("newproof") << "TheoryProxy::explainPropagation: processed first "
                           "disjunct to conclude "
                        << clauseExplanation << "\n";
    }
  }
  PROOF({
      ProofManager::getCnfProof()->pushCurrentAssertion(theoryExplanation);
      ProofManager::getCnfProof()->setProofRecipe(proofRecipe);

      Debug("pf::sat") << "TheoryProxy::explainPropagation: setting lemma recipe to: "
                       << std::endl;
      proofRecipe->dump("pf::sat");

      delete proofRecipe;
      proofRecipe = NULL;
    });

  Debug("prop-explain") << "explainPropagation() => " << theoryExplanation << std::endl;
  if (theoryExplanation.getKind() == kind::AND) {
    Node::const_iterator it = theoryExplanation.begin();
    Node::const_iterator it_end = theoryExplanation.end();
    explanation.push_back(l);
    for (; it != it_end; ++ it) {
      explanation.push_back(~d_cnfStream->getLiteral(*it));
    }
  } else {
    explanation.push_back(l);
    explanation.push_back(~d_cnfStream->getLiteral(theoryExplanation));
  }
  if (CVC4::options::proofNew())
  {
    Trace("newproof") << "TheoryProxy::explainPropagation: clause for lit is ";

    for (unsigned i = 0, size = explanation.size(); i < size; ++i)
    {
      Trace("newproof") << explanation[i] << " ["
                        << d_cnfStream->getNode(explanation[i]) << "] ";
    }
    Trace("newproof") << "\n";
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
  return options::decisionStopOnly() ? undefSatLiteral : ret;
}

bool TheoryProxy::theoryNeedCheck() const {
  return d_theoryEngine->needCheck();
}

TNode TheoryProxy::getNode(SatLiteral lit) {
  return d_cnfStream->getNode(lit);
}

void TheoryProxy::notifyRestart() {
  d_propEngine->spendResource(ResourceManager::Resource::RestartStep);
  d_theoryEngine->notifyRestart();
}

void TheoryProxy::spendResource(ResourceManager::Resource r)
{
  d_theoryEngine->spendResource(r);
}

bool TheoryProxy::isDecisionRelevant(SatVariable var) {
  return d_decisionEngine->isRelevant(var);
}

bool TheoryProxy::isDecisionEngineDone() {
  return d_decisionEngine->isDone();
}

SatValue TheoryProxy::getDecisionPolarity(SatVariable var) {
  return d_decisionEngine->getPolarity(var);
}

void TheoryProxy::dumpStatePop() {
  if(Dump.isOn("state")) {
    Dump("state") << PopCommand();
  }
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */
