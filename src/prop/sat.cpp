/*********************                                                        */
/*! \file sat.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: dejan, taking, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "prop/sat.h"
#include "context/context.h"
#include "theory/theory_engine.h"
#include "expr/expr_stream.h"

namespace CVC4 {
namespace prop {

void SatSolver::variableNotify(SatVariable var) {
  d_theoryEngine->preRegister(getNode(variableToLiteral(var)));
}

void SatSolver::theoryCheck(theory::Theory::Effort effort) {
  d_theoryEngine->check(effort);
}

void SatSolver::theoryPropagate(std::vector<SatLiteral>& output) {
  // Get the propagated literals
  std::vector<TNode> outputNodes;
  d_theoryEngine->getPropagatedLiterals(outputNodes);
  for (unsigned i = 0, i_end = outputNodes.size(); i < i_end; ++ i) {
    Debug("prop-explain") << "theoryPropagate() => " << outputNodes[i].toString() << std::endl;
    output.push_back(d_cnfStream->getLiteral(outputNodes[i]));
  }
}

void SatSolver::explainPropagation(SatLiteral l, SatClause& explanation) {
  TNode lNode = d_cnfStream->getNode(l);
  Debug("prop-explain") << "explainPropagation(" << lNode << ")" << std::endl;
  Node theoryExplanation = d_theoryEngine->getExplanation(lNode);
  Debug("prop-explain") << "explainPropagation() => " <<  theoryExplanation << std::endl;
  if (theoryExplanation.getKind() == kind::AND) {
    Node::const_iterator it = theoryExplanation.begin();
    Node::const_iterator it_end = theoryExplanation.end();
    explanation.push(l);
    for (; it != it_end; ++ it) {
      explanation.push(~d_cnfStream->getLiteral(*it));
    }
  } else {
    explanation.push(l);
    explanation.push(~d_cnfStream->getLiteral(theoryExplanation));
  }
}

void SatSolver::enqueueTheoryLiteral(const SatLiteral& l) {
  Node literalNode = d_cnfStream->getNode(l);
  Debug("prop") << "enqueueing theory literal " << l << " " << literalNode << std::endl;
  Assert(!literalNode.isNull());
  d_theoryEngine->assertFact(literalNode);
}

bool SatSolver::theoryNeedCheck() const {
  return d_theoryEngine->needCheck();
}

void SatSolver::setCnfStream(CnfStream* cnfStream) {
  d_cnfStream = cnfStream;
}

void SatSolver::removeClausesAboveLevel(int level) {
  d_cnfStream->removeClausesAboveLevel(level);
}

TNode SatSolver::getNode(SatLiteral lit) {
  return d_cnfStream->getNode(lit);
}

void SatSolver::notifyRestart() {
  d_propEngine->checkTime();
  d_theoryEngine->notifyRestart();
}

SatLiteral SatSolver::getNextReplayDecision() {
#ifdef CVC4_REPLAY
  if(Options::current()->replayStream != NULL) {
    Expr e = Options::current()->replayStream->nextExpr();
    if(!e.isNull()) { // we get null node when out of decisions to replay
      // convert & return
      return d_cnfStream->getLiteral(e);
    }
  }
#endif /* CVC4_REPLAY */
  return Minisat::lit_Undef;
}

void SatSolver::logDecision(SatLiteral lit) {
#ifdef CVC4_REPLAY
  if(Options::current()->replayLog != NULL) {
    Assert(lit != Minisat::lit_Undef, "logging an `undef' decision ?!");
    *Options::current()->replayLog << d_cnfStream->getNode(lit) << std::endl;
  }
#endif /* CVC4_REPLAY */
}

void SatSolver::checkTime() {
  d_propEngine->checkTime();
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */
