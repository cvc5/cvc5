/*********************                                                        */
/*! \file cnf_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Andrew Reynolds, Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "proof/cnf_proof.h"

#include "proof/clause_id.h"
#include "proof/proof_manager.h"
#include "prop/cnf_stream.h"
#include "prop/minisat/minisat.h"
#include "prop/sat_solver_types.h"

namespace CVC4 {

CnfProof::CnfProof(prop::CnfStream* stream,
                   context::Context* ctx,
                   const std::string& name)
  : d_cnfStream(stream)
  , d_clauseToAssertion(ctx)
  , d_currentAssertionStack()
  , d_currentDefinitionStack()
  , d_clauseToDefinition(ctx)
  , d_definitions()
  , d_cnfDeps()
  , d_name(name)
{
  // Setting the proof object for the CnfStream
  d_cnfStream->setProof(this);
}

CnfProof::~CnfProof() {}

Node CnfProof::getAssertionForClause(ClauseId clause) {
  ClauseIdToNode::const_iterator it = d_clauseToAssertion.find(clause);
  Assert(it != d_clauseToAssertion.end() && !(*it).second.isNull());
  return (*it).second;
}

Node CnfProof::getDefinitionForClause(ClauseId clause) {
  ClauseIdToNode::const_iterator it = d_clauseToDefinition.find(clause);
  Assert(it != d_clauseToDefinition.end());
  return (*it).second;
}

void CnfProof::registerConvertedClause(ClauseId clause, bool explanation) {
  Assert(clause != ClauseIdUndef && clause != ClauseIdError
         && clause != ClauseIdEmpty);

  // Explanations do not need a CNF conversion proof since they are in CNF
  // (they will only need a theory proof as they are theory valid)
  if (explanation) {
    Debug("proof:cnf") << "CnfProof::registerConvertedClause "
                       << clause << " explanation? " << explanation << std::endl;
    Assert(d_explanations.find(clause) == d_explanations.end());
    d_explanations.insert(clause);
    return;
  }

  Node current_assertion = getCurrentAssertion();
  Node current_expr = getCurrentDefinition();

  Debug("proof:cnf") << "CnfProof::registerConvertedClause "
                     << clause << " assertion = " << current_assertion
                     << clause << " definition = " << current_expr << std::endl;

  setClauseAssertion(clause, current_assertion);
  setClauseDefinition(clause, current_expr);
}

void CnfProof::registerTrueUnitClause(ClauseId clauseId)
{
  Node trueNode = NodeManager::currentNM()->mkConst<bool>(true);
  pushCurrentAssertion(trueNode);
  pushCurrentDefinition(trueNode);
  registerConvertedClause(clauseId);
  popCurrentAssertion();
  popCurrentDefinition();
  d_cnfStream->ensureLiteral(trueNode);
  d_trueUnitClause = clauseId;
}

void CnfProof::registerFalseUnitClause(ClauseId clauseId)
{
  Node falseNode = NodeManager::currentNM()->mkConst<bool>(false).notNode();
  pushCurrentAssertion(falseNode);
  pushCurrentDefinition(falseNode);
  registerConvertedClause(clauseId);
  popCurrentAssertion();
  popCurrentDefinition();
  d_cnfStream->ensureLiteral(falseNode);
  d_falseUnitClause = clauseId;
}

void CnfProof::setClauseAssertion(ClauseId clause, Node expr) {
  Debug("proof:cnf") << "CnfProof::setClauseAssertion "
                     << clause << " assertion " << expr << std::endl;
  // We can add the same clause from different assertions.  In this
  // case we keep the first assertion. For example asserting a /\ b
  // and then b /\ c where b is an atom, would assert b twice (note
  // that since b is top level, it is not cached by the CnfStream)
  //
  // Note: If the current assertion associated with the clause is null, we
  // update it because it means that it was previously added the clause without
  // associating it with an assertion.
  const auto& it = d_clauseToAssertion.find(clause);
  if (it != d_clauseToAssertion.end() && (*it).second != Node::null())
  {
    return;
  }

  d_clauseToAssertion.insert (clause, expr);
}

void CnfProof::setClauseDefinition(ClauseId clause, Node definition) {
  Debug("proof:cnf") << "CnfProof::setClauseDefinition "
                     << clause << " definition " << definition << std::endl;
  // We keep the first definition
  if (d_clauseToDefinition.find(clause) != d_clauseToDefinition.end())
    return;

  d_clauseToDefinition.insert(clause, definition);
  d_definitions.insert(definition);
}

void CnfProof::setCnfDependence(Node from, Node to) {
  Debug("proof:cnf") << "CnfProof::setCnfDependence "
                     << "from " << from  << std::endl
                     << "     to " << to << std::endl;

  Assert(from != to);
  d_cnfDeps.insert(std::make_pair(from, to));
}

void CnfProof::pushCurrentAssertion(Node assertion) {
  Debug("proof:cnf") << "CnfProof::pushCurrentAssertion " << assertion
                     << std::endl;

  d_currentAssertionStack.push_back(assertion);

  Debug("proof:cnf") << "CnfProof::pushCurrentAssertion "
                     << "new stack size = " << d_currentAssertionStack.size()
                     << std::endl;
}

void CnfProof::popCurrentAssertion() {
  Assert(d_currentAssertionStack.size());

  Debug("proof:cnf") << "CnfProof::popCurrentAssertion "
                     << d_currentAssertionStack.back() << std::endl;

  d_currentAssertionStack.pop_back();

  Debug("proof:cnf") << "CnfProof::popCurrentAssertion "
                     << "new stack size = " << d_currentAssertionStack.size()
                     << std::endl;
}

Node CnfProof::getCurrentAssertion() {
  Assert(d_currentAssertionStack.size());
  return d_currentAssertionStack.back();
}

void CnfProof::pushCurrentDefinition(Node definition) {
  Debug("proof:cnf") << "CnfProof::pushCurrentDefinition "
                     << definition  << std::endl;

  d_currentDefinitionStack.push_back(definition);
}

void CnfProof::popCurrentDefinition() {
  Assert(d_currentDefinitionStack.size());

  Debug("proof:cnf") << "CnfProof::popCurrentDefinition "
                     << d_currentDefinitionStack.back() << std::endl;

  d_currentDefinitionStack.pop_back();
}

Node CnfProof::getCurrentDefinition() {
  Assert(d_currentDefinitionStack.size());
  return d_currentDefinitionStack.back();
}

Node CnfProof::getAtom(prop::SatVariable var) {
  prop::SatLiteral lit (var);
  Node node = d_cnfStream->getNode(lit);
  return node;
}

prop::SatLiteral CnfProof::getLiteral(TNode atom) {
  return d_cnfStream->getLiteral(atom);
}

bool CnfProof::hasLiteral(TNode atom) {
  return d_cnfStream->hasLiteral(atom);
}

void CnfProof::ensureLiteral(TNode atom, bool noPreregistration) {
  d_cnfStream->ensureLiteral(atom, noPreregistration);
}

} /* CVC4 namespace */
