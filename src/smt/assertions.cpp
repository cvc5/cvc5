/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for storing assertions for an SMT engine.
 */

#include "smt/assertions.h"

#include <sstream>

#include "base/modal_exception.h"
#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/expr_options.h"
#include "options/language.h"
#include "options/smt_options.h"
#include "smt/abstract_values.h"
#include "smt/env.h"
#include "smt/smt_engine.h"
#include "theory/trust_substitutions.h"

using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
namespace smt {

Assertions::Assertions(Env& env, AbstractValues& absv)
    : d_env(env),
      d_absValues(absv),
      d_produceAssertions(false),
      d_assertionList(env.getUserContext()),
      d_globalNegation(false),
      d_assertions()
{
}

Assertions::~Assertions()
{
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
    d_produceAssertions = true;
    d_globalDefineFunLemmas.reset(new std::vector<Node>());
  }
}

void Assertions::clearCurrent()
{
  d_assertions.clear();
  d_assertions.getIteSkolemMap().clear();
}

void Assertions::initializeCheckSat(const std::vector<Node>& assumptions,
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
    addFormula(n, true, true, false, false);
  }
  if (d_globalDefineFunLemmas != nullptr)
  {
    // Global definitions are asserted at check-sat-time because we have to
    // make sure that they are always present (they are essentially level
    // zero assertions)
    for (const Node& lemma : *d_globalDefineFunLemmas)
    {
      addFormula(lemma, true, false, true, false);
    }
  }
}

void Assertions::assertFormula(const Node& n)
{
  ensureBoolean(n);
  bool maybeHasFv = language::isLangSygus(options::inputLanguage());
  addFormula(n, true, false, false, maybeHasFv);
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
  return d_produceAssertions ? &d_assertionList : nullptr;
}

void Assertions::addFormula(TNode n,
                            bool inInput,
                            bool isAssumption,
                            bool isFunDef,
                            bool maybeHasFv)
{
  // add to assertion list if it exists
  if (d_produceAssertions)
  {
    d_assertionList.push_back(n);
  }
  if (n.isConst() && n.getConst<bool>())
  {
    // true, nothing to do
    return;
  }
  Trace("smt") << "SmtEnginePrivate::addFormula(" << n
               << ", inInput = " << inInput
               << ", isAssumption = " << isAssumption
               << ", isFunDef = " << isFunDef << std::endl;
  if (isFunDef)
  {
    // if a non-recursive define-fun, just add as a top-level substitution
    if (n.getKind() == EQUAL && n[0].isVar())
    {
      // A define-fun is an assumption in the overall proof, thus
      // we justify the substitution with ASSUME here.
      d_env.getTopLevelSubstitutions().addSubstitution(
          n[0], n[1], PfRule::ASSUME, {}, {n});
      return;
    }
  }

  // Ensure that it does not contain free variables
  if (maybeHasFv)
  {
    if (expr::hasFreeVar(n))
    {
      std::stringstream se;
      if (isFunDef)
      {
        se << "Cannot process function definition with free variable.";
      }
      else
      {
        se << "Cannot process assertion with free variable.";
        if (language::isLangSygus(options::inputLanguage()))
        {
          // Common misuse of SyGuS is to use top-level assert instead of
          // constraint when defining the synthesis conjecture.
          se << " Perhaps you meant `constraint` instead of `assert`?";
        }
      }
      throw ModalException(se.str().c_str());
    }
  }

  // Add the normalized formula to the queue
  d_assertions.push_back(n, isAssumption, true);
}

void Assertions::addDefineFunDefinition(Node n, bool global)
{
  n = d_absValues.substituteAbstractValues(n);
  if (global && d_globalDefineFunLemmas != nullptr)
  {
    // Global definitions are asserted at check-sat-time because we have to
    // make sure that they are always present
    Assert(!language::isLangSygus(options::inputLanguage()));
    d_globalDefineFunLemmas->emplace_back(n);
  }
  else
  {
    // We don't permit functions-to-synthesize within recursive function
    // definitions currently. Thus, we should check for free variables if the
    // input language is SyGuS.
    bool maybeHasFv = language::isLangSygus(options::inputLanguage());
    addFormula(n, true, false, true, maybeHasFv);
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
    throw TypeCheckingExceptionPrivate(n, ss.str());
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
}  // namespace cvc5
