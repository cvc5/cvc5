/*********************                                                        */
/*! \file cnf_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Andres Noetzli, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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

void CnfProof::registerConvertedClause(ClauseId clause)
{
  Assert(clause != ClauseIdUndef && clause != ClauseIdError
         && clause != ClauseIdEmpty);
  Node current_assertion = getCurrentAssertion();

  Debug("proof:cnf") << "CnfProof::registerConvertedClause " << clause
                     << " assertion = " << current_assertion << std::endl;

  setClauseAssertion(clause, current_assertion);
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

  d_clauseToAssertion.insert(clause, expr);
}

void CnfProof::pushCurrentAssertion(Node assertion, bool isInput)
{
  Debug("proof:cnf") << "CnfProof::pushCurrentAssertion " << assertion
                     << std::endl;

  d_currentAssertionStack.push_back(std::pair<Node, bool>(assertion, isInput));

  Debug("proof:cnf") << "CnfProof::pushCurrentAssertion "
                     << "new stack size = " << d_currentAssertionStack.size()
                     << std::endl;
}

void CnfProof::popCurrentAssertion() {
  Assert(d_currentAssertionStack.size());

  Debug("proof:cnf") << "CnfProof::popCurrentAssertion "
                     << d_currentAssertionStack.back().first << std::endl;

  d_currentAssertionStack.pop_back();

  Debug("proof:cnf") << "CnfProof::popCurrentAssertion "
                     << "new stack size = " << d_currentAssertionStack.size()
                     << std::endl;
}

Node CnfProof::getCurrentAssertion() {
  Assert(d_currentAssertionStack.size());
  return d_currentAssertionStack.back().first;
}

bool CnfProof::getCurrentAssertionKind()
{
  return d_currentAssertionStack.back().second;
}

} /* CVC4 namespace */
