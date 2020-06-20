/*********************                                                        */
/*! \file theory_quantifiers.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
#include "options/quantifiers_options.h"
#include "theory/quantifiers/ematching/instantiation_engine.h"
#include "theory/quantifiers/fmf/model_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/valuation.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

TheoryQuantifiers::TheoryQuantifiers(Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo) :
    Theory(THEORY_QUANTIFIERS, c, u, out, valuation, logicInfo)
{
  out.handleUserAttribute( "fun-def", this );
  out.handleUserAttribute( "sygus", this );
  out.handleUserAttribute("quant-name", this);
  out.handleUserAttribute("sygus-synth-grammar", this);
  out.handleUserAttribute( "sygus-synth-fun-var-list", this );
  out.handleUserAttribute( "quant-inst-max-level", this );
  out.handleUserAttribute( "quant-elim", this );
  out.handleUserAttribute( "quant-elim-partial", this );
}

TheoryQuantifiers::~TheoryQuantifiers() {
}

void TheoryQuantifiers::finishInit()
{
  // quantifiers are not evaluated in getModelValue
  TheoryModel* tm = d_valuation.getModel();
  Assert(tm != nullptr);
  tm->setUnevaluatedKind(EXISTS);
  tm->setUnevaluatedKind(FORALL);
  // witness is used in several instantiation strategies
  tm->setUnevaluatedKind(WITNESS);
}

void TheoryQuantifiers::preRegisterTerm(TNode n) {
  if (n.getKind() != FORALL)
  {
    return;
  }
  Debug("quantifiers-prereg") << "TheoryQuantifiers::preRegisterTerm() " << n << endl;
  // Preregister the quantified formula.
  // This initializes the modules used for handling n in this user context.
  getQuantifiersEngine()->preRegisterQuantifier(n);
  Debug("quantifiers-prereg")
      << "TheoryQuantifiers::preRegisterTerm() done " << n << endl;
}


void TheoryQuantifiers::presolve() {
  Debug("quantifiers-presolve") << "TheoryQuantifiers::presolve()" << endl;
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

bool TheoryQuantifiers::collectModelInfo(TheoryModel* m)
{
  for(assertions_iterator i = facts_begin(); i != facts_end(); ++i) {
    if ((*i).d_assertion.getKind() == kind::NOT)
    {
      Debug("quantifiers::collectModelInfo")
          << "got quant FALSE: " << (*i).d_assertion[0] << endl;
      if (!m->assertPredicate((*i).d_assertion[0], false))
      {
        return false;
      }
    }
    else
    {
      Debug("quantifiers::collectModelInfo") << "got quant TRUE : " << *i << endl;
      if (!m->assertPredicate(*i, true))
      {
        return false;
      }
    }
  }
  return true;
}

void TheoryQuantifiers::check(Effort e) {
  if (done() && !fullEffort(e)) {
    return;
  }

  TimerStat::CodeTimer checkTimer(d_checkTime);

  Trace("quantifiers-check") << "quantifiers::check(" << e << ")" << std::endl;
  while(!done()) {
    Node assertion = get();
    Trace("quantifiers-assert") << "quantifiers::assert(): " << assertion << std::endl;
    switch(assertion.getKind()) {
    case kind::FORALL:
      getQuantifiersEngine()->assertQuantifier(assertion, true);
      break;
    case kind::INST_CLOSURE:
      getQuantifiersEngine()->addTermToDatabase( assertion[0], false, true );
      if( !options::lteRestrictInstClosure() ){
        getQuantifiersEngine()->getMasterEqualityEngine()->addTerm( assertion[0] );
      }
      break;
    case kind::EQUAL:
      //do nothing
      break;
    case kind::NOT:
      {
        switch( assertion[0].getKind()) {
        case kind::FORALL:
          getQuantifiersEngine()->assertQuantifier(assertion[0], false);
          break;
        case kind::EQUAL:
          //do nothing
          break;
        case kind::INST_CLOSURE:
        default: Unhandled() << assertion[0].getKind(); break;
        }
      }
      break;
      default: Unhandled() << assertion.getKind(); break;
    }
  }
  // call the quantifiers engine to check
  getQuantifiersEngine()->check( e );
}

void TheoryQuantifiers::setUserAttribute(const std::string& attr, Node n, std::vector<Node> node_values, std::string str_value){
  QuantAttributes::setUserAttribute( attr, n, node_values, str_value );
}
