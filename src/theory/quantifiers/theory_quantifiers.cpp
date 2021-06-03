/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

using namespace cvc5::kind;
using namespace cvc5::context;

namespace cvc5 {
namespace theory {
namespace quantifiers {

TheoryQuantifiers::TheoryQuantifiers(Context* c,
                                     context::UserContext* u,
                                     OutputChannel& out,
                                     Valuation valuation,
                                     const LogicInfo& logicInfo,
                                     ProofNodeManager* pnm)
    : Theory(THEORY_QUANTIFIERS, c, u, out, valuation, logicInfo, pnm),
      d_qstate(c, u, valuation, logicInfo),
      d_qreg(),
      d_treg(d_qstate, d_qreg),
      d_qim(*this, d_qstate, d_qreg, d_treg, pnm),
      d_qengine(nullptr)
{
  out.handleUserAttribute( "fun-def", this );
  out.handleUserAttribute("qid", this);
  out.handleUserAttribute( "quant-inst-max-level", this );
  out.handleUserAttribute( "quant-elim", this );
  out.handleUserAttribute( "quant-elim-partial", this );

  // construct the quantifiers engine
  d_qengine.reset(new QuantifiersEngine(d_qstate, d_qreg, d_treg, d_qim, pnm));

  // indicate we are using the quantifiers theory state object
  d_theoryState = &d_qstate;
  // use the inference manager as the official inference manager
  d_inferManager = &d_qim;
  // Set the pointer to the quantifiers engine, which this theory owns. This
  // pointer will be retreived by TheoryEngine and set to all theories
  // post-construction.
  d_quantEngine = d_qengine.get();

  if (options::macrosQuant())
  {
    d_qmacros.reset(new QuantifiersMacros(d_qreg));
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
  Debug("quantifiers-prereg")
      << "TheoryQuantifiers::preRegisterTerm() " << n << std::endl;
  // Preregister the quantified formula.
  // This initializes the modules used for handling n in this user context.
  getQuantifiersEngine()->preRegisterQuantifier(n);
  Debug("quantifiers-prereg")
      << "TheoryQuantifiers::preRegisterTerm() done " << n << std::endl;
}


void TheoryQuantifiers::presolve() {
  Debug("quantifiers-presolve") << "TheoryQuantifiers::presolve()" << std::endl;
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
        options::macrosQuantMode() != options::MacrosQuantMode::ALL;
    Node eq = d_qmacros->solve(tin.getProven(), reqGround);
    if (!eq.isNull())
    {
      // must be legal
      if (isLegalElimination(eq[0], eq[1]))
      {
        outSubstitutions.addSubstitution(eq[0], eq[1]);
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
      Debug("quantifiers::collectModelInfo")
          << "got quant FALSE: " << (*i).d_assertion[0] << std::endl;
      if (!m->assertPredicate((*i).d_assertion[0], false))
      {
        return false;
      }
    }
    else
    {
      Debug("quantifiers::collectModelInfo")
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

void TheoryQuantifiers::setUserAttribute(const std::string& attr, Node n, std::vector<Node> node_values, std::string str_value){
  QuantAttributes::setUserAttribute( attr, n, node_values, str_value );
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
