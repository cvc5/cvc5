/*********************                                                        */
/*! \file assertions_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for managing assertions for an SMT engine.
 **/

#include "smt/assertions_manager.h"

#include "expr/node_algorithm.h"
#include "options/language.h"
#include "options/smt_options.h"

using namespace CVC4::theory;
using namespace CVC4::kind;

namespace CVC4 {
namespace smt {

AssertionsManager::AssertionsManager(SmtEngine& smt, ResourceManager& rm)
    : d_smt(smt),
      d_proc(smt, rm),
      d_assertionList(nullptr),
      d_assignments(nullptr),
      d_globalNegation(false),
      d_assertions(),
      d_assertionsProcessed(smt.getUserContext(), false)
{
}

AssertionsManager::~AssertionsManager()
{
  if(d_assignments != NULL) {
    d_assignments->deleteSelf();
  }
  if(d_assertionList != NULL) {
    d_assertionList->deleteSelf();
  }
}

void AssertionsManager::notifyPush() {

}

void AssertionsManager::notifyPop() {
  d_assertions.clear();
}


void AssertionsManager::initializeCheckSat(const std::vector<Node>& assumptions,
                            bool inUnsatCore,
                            bool isEntailmentCheck)
{
  d_assumptions.clear();
  if (isEntailmentCheck)
  {
    size_t size = assumptions.size();
    if (size > 1)
    {
      /* Assume: not (BIGAND assumptions)  */
      d_assumptions.push_back(
          d_exprManager->mkExpr(kind::AND, assumptions).notExpr());
    }
    else if (size == 1)
    {
      /* Assume: not expr  */
      d_assumptions.push_back(assumptions[0].notExpr());
    }
  }
  else
  {
    /* Assume: BIGAND assumptions  */
    d_assumptions = assumptions;
  }

  if (!d_assumptions.empty())
  {
    internalPush();
    didInternalPush = true;
  }

  Result r(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
  for (Expr e : d_assumptions)
  {
    // Substitute out any abstract values in ex.
    Node n = d_absValues->substituteAbstractValues(Node::fromExpr(e));
    // Ensure expr is type-checked at this point.
    ensureBoolean(n);

    /* Add assumption  */
    if (d_assertionList != NULL)
    {
      d_assertionList->push_back(n);
    }
    addFormula(n, inUnsatCore, true, true);
  }
}

void AssertionsManager::addFormula(
    TNode n, bool inUnsatCore, bool inInput, bool isAssumption, bool maybeHasFv)
{
  if (n.isConst() && n.getConst<bool>()) {
    // true, nothing to do
    return;
  }

  Trace("smt") << "SmtEnginePrivate::addFormula(" << n
               << "), inUnsatCore = " << inUnsatCore
               << ", inInput = " << inInput
               << ", isAssumption = " << isAssumption << endl;

  // Ensure that it does not contain free variables
  if (maybeHasFv)
  {
    if (expr::hasFreeVar(n))
    {
      std::stringstream se;
      se << "Cannot process assertion with free variable.";
      if (language::isInputLangSygus(options::inputLanguage()))
      {
        // Common misuse of SyGuS is to use top-level assert instead of
        // constraint when defining the synthesis conjecture.
        se << " Perhaps you meant `constraint` instead of `assert`?";
      }
      throw ModalException(se.str().c_str());
    }
  }

  // Give it to proof manager
  PROOF(
    if( inInput ){
      // n is an input assertion
      if (inUnsatCore || options::unsatCores() || options::dumpUnsatCores() || options::checkUnsatCores() || options::fewerPreprocessingHoles()) {

        ProofManager::currentPM()->addCoreAssertion(n.toExpr());
      }
    }else{
      // n is the result of an unknown preprocessing step, add it to dependency map to null
      ProofManager::currentPM()->addDependence(n, Node::null());
    }
  );

  // Add the normalized formula to the queue
  d_assertions.push_back(n, isAssumption);
}

void AssertionsManager::finishInit()
{
  Trace("smt-debug") << "Set up assertion list..." << std::endl;
  // [MGD 10/20/2011] keep around in incremental mode, due to a
  // cleanup ordering issue and Nodes/TNodes.  If SAT is popped
  // first, some user-context-dependent TNodes might still exist
  // with rc == 0.
  if(options::produceAssertions() ||
     options::incrementalSolving()) {
    // In the case of incremental solving, we appear to need these to
    // ensure the relevant Nodes remain live.
    d_assertionList = new (true) AssertionList(getUserContext());
  }
}

std::vector<Node>& AssertionsManager::getAssumptions()
{
  return d_assumptions;
}

void AssertionsManager::addFormula(
    TNode n, bool inUnsatCore, bool inInput, bool isAssumption, bool maybeHasFv)
{
  if (n.isConst() && n.getConst<bool>()) {
    // nothing to do
    return;
  }

  Trace("smt") << "SmtEnginePrivate::addFormula(" << n
               << "), inUnsatCore = " << inUnsatCore
               << ", inInput = " << inInput
               << ", isAssumption = " << isAssumption << endl;

  // Ensure that it does not contain free variables
  if (maybeHasFv)
  {
    if (expr::hasFreeVar(n))
    {
      std::stringstream se;
      se << "Cannot process assertion with free variable.";
      if (language::isInputLangSygus(options::inputLanguage()))
      {
        // Common misuse of SyGuS is to use top-level assert instead of
        // constraint when defining the synthesis conjecture.
        se << " Perhaps you meant `constraint` instead of `assert`?";
      }
      throw ModalException(se.str().c_str());
    }
  }

  // Give it to proof manager
  PROOF(
    if( inInput ){
      // n is an input assertion
      if (inUnsatCore || options::unsatCores() || options::dumpUnsatCores() || options::checkUnsatCores() || options::fewerPreprocessingHoles()) {
        ProofManager::currentPM()->addCoreAssertion(n.toExpr());
      }
    }else{
      // n is the result of an unknown preprocessing step, add it to dependency map to null
      ProofManager::currentPM()->addDependence(n, Node::null());
    }
  );

  // Add the normalized formula to the queue
  d_assertions.push_back(n, isAssumption);
}

}  // namespace smt
}  // namespace CVC4
