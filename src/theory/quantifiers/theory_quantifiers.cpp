/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the theory of quantifiers.
 */

#include "theory/quantifiers/theory_quantifiers.h"

#include "options/quantifiers_options.h"
#include "proof/proof_node_manager.h"
#include "theory/quantifiers/quantifiers_macros.h"
#include "theory/quantifiers/quantifiers_modules.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/trust_substitutions.h"
#include "theory/valuation.h"

using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

TheoryQuantifiers::TheoryQuantifiers(Env& env,
                                     OutputChannel& out,
                                     Valuation valuation)
    : Theory(THEORY_QUANTIFIERS, env, out, valuation),
      d_rewriter(env.getRewriter(), options()),
      d_qstate(env, valuation, logicInfo()),
      d_qreg(env),
      d_treg(env, d_qstate, d_qreg),
      d_qim(env, *this, d_qstate, d_qreg, d_treg),
      d_qengine(nullptr)
{
  // construct the quantifiers engine
  d_qengine.reset(
      new QuantifiersEngine(env, d_qstate, d_qreg, d_treg, d_qim, d_pnm));

  // indicate we are using the quantifiers theory state object
  d_theoryState = &d_qstate;
  // use the inference manager as the official inference manager
  d_inferManager = &d_qim;
  // Set the pointer to the quantifiers engine, which this theory owns. This
  // pointer will be retreived by TheoryEngine and set to all theories
  // post-construction.
  d_quantEngine = d_qengine.get();

  if (options().quantifiers.macrosQuant)
  {
    d_qmacros.reset(new QuantifiersMacros(env, d_qreg));
  }
}

TheoryQuantifiers::~TheoryQuantifiers() {
}

TheoryRewriter* TheoryQuantifiers::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryQuantifiers::getProofChecker() { return &d_checker; }

void TheoryQuantifiers::finishInit()
{
  // quantifiers are not evaluated in getModelValue
  d_valuation.setUnevaluatedKind(EXISTS);
  d_valuation.setUnevaluatedKind(FORALL);
  // witness is used in several instantiation strategies
  d_valuation.setUnevaluatedKind(WITNESS);
}

bool TheoryQuantifiers::needsEqualityEngine(EeSetupInfo& esi)
{
  // use the master equality engine
  esi.d_useMaster = true;
  return true;
}

void TheoryQuantifiers::preRegisterTerm(TNode n)
{
  if (n.getKind() != FORALL)
  {
    return;
  }
  Trace("quantifiers-prereg")
      << "TheoryQuantifiers::preRegisterTerm() " << n << std::endl;
  // Preregister the quantified formula.
  // This initializes the modules used for handling n in this user context.
  getQuantifiersEngine()->preRegisterQuantifier(n);
  Trace("quantifiers-prereg")
      << "TheoryQuantifiers::preRegisterTerm() done " << n << std::endl;
}


void TheoryQuantifiers::presolve() {
  Trace("quantifiers-presolve") << "TheoryQuantifiers::presolve()" << std::endl;
  if( getQuantifiersEngine() ){
    getQuantifiersEngine()->presolve();
  }
}

Theory::PPAssertStatus TheoryQuantifiers::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  if (d_qmacros != nullptr)
  {
    bool reqGround =
        options().quantifiers.macrosQuantMode != options::MacrosQuantMode::ALL;
    Node eq = d_qmacros->solve(tin.getProven(), reqGround);
    if (!eq.isNull())
    {
      // must be legal
      if (isLegalElimination(eq[0], eq[1]))
      {
        // add substitution solved, which ensures we track that eq depends on
        // tin, which can impact unsat cores.
        outSubstitutions.addSubstitutionSolved(eq[0], eq[1], tin);
        return Theory::PP_ASSERT_STATUS_SOLVED;
      }
    }
  }
  return Theory::PP_ASSERT_STATUS_UNSOLVED;
}
void TheoryQuantifiers::ppNotifyAssertions(
    const std::vector<Node>& assertions) {
  Trace("quantifiers-presolve")
      << "TheoryQuantifiers::ppNotifyAssertions" << std::endl;
  if (getQuantifiersEngine()) {
    getQuantifiersEngine()->ppNotifyAssertions(assertions);
  }
}

bool TheoryQuantifiers::collectModelValues(TheoryModel* m,
                                           const std::set<Node>& termSet)
{
  for(assertions_iterator i = facts_begin(); i != facts_end(); ++i) {
    if ((*i).d_assertion.getKind() == NOT)
    {
      Trace("quantifiers::collectModelInfo")
          << "got quant FALSE: " << (*i).d_assertion[0] << std::endl;
      if (!m->assertPredicate((*i).d_assertion[0], false))
      {
        return false;
      }
    }
    else
    {
      Trace("quantifiers::collectModelInfo")
          << "got quant TRUE : " << *i << std::endl;
      if (!m->assertPredicate(*i, true))
      {
        return false;
      }
    }
  }
  return true;
}

void TheoryQuantifiers::postCheck(Effort level)
{
  // call the quantifiers engine to check
  getQuantifiersEngine()->check(level);
}

bool TheoryQuantifiers::preNotifyFact(
    TNode atom, bool polarity, TNode fact, bool isPrereg, bool isInternal)
{
  Kind k = atom.getKind();
  if (k == FORALL)
  {
    getQuantifiersEngine()->assertQuantifier(atom, polarity);
  }
  else
  {
    Unhandled() << "Unexpected fact " << fact;
  }
  // don't use equality engine, always return true
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
