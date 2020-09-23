/*********************                                                        */
/*! \file theory_quantifiers.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the theory of quantifiers
 **
 ** Implementation of the theory of quantifiers.
 **/

#include "theory/quantifiers/theory_quantifiers.h"

#include "base/check.h"
#include "expr/kind.h"
#include "expr/proof_node_manager.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/ematching/instantiation_engine.h"
#include "theory/quantifiers/fmf/model_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/valuation.h"

using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

TheoryQuantifiers::TheoryQuantifiers(Context* c,
                                     context::UserContext* u,
                                     OutputChannel& out,
                                     Valuation valuation,
                                     const LogicInfo& logicInfo,
                                     ProofNodeManager* pnm)
    : Theory(THEORY_QUANTIFIERS, c, u, out, valuation, logicInfo, pnm),
      d_qstate(c, u, valuation)
{
  out.handleUserAttribute( "fun-def", this );
  out.handleUserAttribute( "sygus", this );
  out.handleUserAttribute("qid", this);
  out.handleUserAttribute("sygus-synth-grammar", this);
  out.handleUserAttribute( "sygus-synth-fun-var-list", this );
  out.handleUserAttribute( "quant-inst-max-level", this );
  out.handleUserAttribute( "quant-elim", this );
  out.handleUserAttribute( "quant-elim-partial", this );

  ProofChecker* pc = pnm != nullptr ? pnm->getChecker() : nullptr;
  if (pc != nullptr)
  {
    // add the proof rules
    d_qChecker.registerTo(pc);
  }
  // indicate we are using the quantifiers theory state object
  d_theoryState = &d_qstate;
}

TheoryQuantifiers::~TheoryQuantifiers() {
}

TheoryRewriter* TheoryQuantifiers::getTheoryRewriter() { return &d_rewriter; }
void TheoryQuantifiers::finishInit()
{
  // quantifiers are not evaluated in getModelValue
  d_valuation.setUnevaluatedKind(EXISTS);
  d_valuation.setUnevaluatedKind(FORALL);
  // witness is used in several instantiation strategies
  d_valuation.setUnevaluatedKind(WITNESS);
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
  else if (k == INST_CLOSURE)
  {
    if (!polarity)
    {
      Unhandled() << "Unexpected inst-closure fact " << fact;
    }
    getQuantifiersEngine()->addTermToDatabase(atom[0], false, true);
    if (!options::lteRestrictInstClosure())
    {
      getQuantifiersEngine()->getMasterEqualityEngine()->addTerm(atom[0]);
    }
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
}  // namespace CVC4
