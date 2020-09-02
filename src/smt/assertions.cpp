/*********************                                                        */
/*! \file assertions.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for storing assertions for an SMT engine.
 **/

#include "smt/assertions.h"

#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/smt_options.h"
#include "proof/proof_manager.h"
#include "smt/smt_engine.h"

using namespace CVC4::theory;
using namespace CVC4::kind;

namespace CVC4 {
namespace smt {

Assertions::Assertions(context::UserContext* u, AbstractValues& absv)
    : d_userContext(u),
      d_absValues(absv),
      d_assertionList(nullptr),
      d_globalNegation(false),
      d_assertions()
{
}

Assertions::~Assertions()
{
  if (d_assertionList != nullptr)
  {
    d_assertionList->deleteSelf();
  }
}

void Assertions::finishInit()
{
  // [MGD 10/20/2011] keep around in incremental mode, due to a
  // cleanup ordering issue and Nodes/TNodes.  If SAT is popped
  // first, some user-context-dependent TNodes might still exist
  // with rc == 0.
  if (options::produceAssertions() || options::incrementalSolving())
  {
    // In the case of incremental solving, we appear to need these to
    // ensure the relevant Nodes remain live.
    d_assertionList = new (true) AssertionList(d_userContext);
    d_globalDefineFunRecLemmas.reset(new std::vector<Node>());
  }
}

void Assertions::clearCurrent()
{
  d_assertions.clear();
  d_assertions.getIteSkolemMap().clear();
}

void Assertions::initializeCheckSat(const std::vector<Node>& assumptions,
                                    bool inUnsatCore,
                                    bool isEntailmentCheck)
{
  NodeManager* nm = NodeManager::currentNM();
  // reset global negation
  d_globalNegation = false;
  // clear the assumptions
  d_assumptions.clear();
  if (isEntailmentCheck)
  {
    size_t size = assumptions.size();
    if (size > 1)
    {
      /* Assume: not (BIGAND assumptions)  */
      d_assumptions.push_back(nm->mkNode(AND, assumptions).notNode());
    }
    else if (size == 1)
    {
      /* Assume: not expr  */
      d_assumptions.push_back(assumptions[0].notNode());
    }
  }
  else
  {
    /* Assume: BIGAND assumptions  */
    d_assumptions = assumptions;
  }

  Result r(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
  for (const Node& e : d_assumptions)
  {
    // Substitute out any abstract values in ex.
    Node n = d_absValues.substituteAbstractValues(e);
    // Ensure expr is type-checked at this point.
    ensureBoolean(n);

    /* Add assumption  */
    if (d_assertionList != nullptr)
    {
      d_assertionList->push_back(n);
    }
    addFormula(n, inUnsatCore, true, true, false);
  }
  if (d_globalDefineFunRecLemmas != nullptr)
  {
    // Global definitions are asserted at check-sat-time because we have to
    // make sure that they are always present (they are essentially level
    // zero assertions)
    for (const Node& lemma : *d_globalDefineFunRecLemmas)
    {
      addFormula(lemma, false, true, false, false);
    }
  }
}

void Assertions::assertFormula(const Node& n, bool inUnsatCore)
{
  ensureBoolean(n);
  if (d_assertionList != nullptr)
  {
    d_assertionList->push_back(n);
  }
  bool maybeHasFv = language::isInputLangSygus(options::inputLanguage());
  addFormula(n, inUnsatCore, true, false, maybeHasFv);
}

std::vector<Node>& Assertions::getAssumptions() { return d_assumptions; }
bool Assertions::isGlobalNegated() const { return d_globalNegation; }
void Assertions::flipGlobalNegated() { d_globalNegation = !d_globalNegation; }

preprocessing::AssertionPipeline& Assertions::getAssertionPipeline()
{
  return d_assertions;
}

context::CDList<Node>* Assertions::getAssertionList()
{
  return d_assertionList;
}

void Assertions::addFormula(
    TNode n, bool inUnsatCore, bool inInput, bool isAssumption, bool maybeHasFv)
{
  if (n.isConst() && n.getConst<bool>())
  {
    // true, nothing to do
    return;
  }

  Trace("smt") << "SmtEnginePrivate::addFormula(" << n
               << "), inUnsatCore = " << inUnsatCore
               << ", inInput = " << inInput
               << ", isAssumption = " << isAssumption << std::endl;

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
  if (options::unsatCores())
  {
    if (inInput)
    {  // n is an input assertion
      if (inUnsatCore || options::unsatCores() || options::dumpUnsatCores()
          || options::checkUnsatCores())
      {
        ProofManager::currentPM()->addCoreAssertion(n.toExpr());
      }
    }
    else
    {
      // n is the result of an unknown preprocessing step, add it to dependency
      // map to null
      ProofManager::currentPM()->addDependence(n, Node::null());
    }
  }

  // Add the normalized formula to the queue
  d_assertions.push_back(n, isAssumption, true);
}

void Assertions::addDefineFunRecDefinition(Node n, bool global)
{
  n = d_absValues.substituteAbstractValues(n);
  if (d_assertionList != nullptr)
  {
    d_assertionList->push_back(n);
  }
  if (global && d_globalDefineFunRecLemmas != nullptr)
  {
    // Global definitions are asserted at check-sat-time because we have to
    // make sure that they are always present
    Assert(!language::isInputLangSygus(options::inputLanguage()));
    d_globalDefineFunRecLemmas->emplace_back(n);
  }
  else
  {
    bool maybeHasFv = language::isInputLangSygus(options::inputLanguage());
    addFormula(n, false, true, false, maybeHasFv);
  }
}

void Assertions::ensureBoolean(const Node& n)
{
  TypeNode type = n.getType(options::typeChecking());
  if (!type.isBoolean())
  {
    std::stringstream ss;
    ss << "Expected Boolean type\n"
       << "The assertion : " << n << "\n"
       << "Its type      : " << type;
    throw TypeCheckingException(n.toExpr(), ss.str());
  }
}

void Assertions::setProofGenerator(smt::PreprocessProofGenerator* pppg)
{
  d_assertions.setProofGenerator(pppg);
}

bool Assertions::isProofEnabled() const
{
  return d_assertions.isProofEnabled();
}

}  // namespace smt
}  // namespace CVC4
