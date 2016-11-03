/*********************                                                        */
/*! \file theory_quantifiers.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the theory of quantifiers
 **
 ** Implementation of the theory of quantifiers.
 **/

#include "theory/quantifiers/theory_quantifiers.h"


#include "base/cvc4_assert.h"
#include "expr/kind.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiation_engine.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"
#include "theory/valuation.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

TheoryQuantifiers::TheoryQuantifiers(Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo) :
    Theory(THEORY_QUANTIFIERS, c, u, out, valuation, logicInfo),
  d_masterEqualityEngine(0)
{
  d_numInstantiations = 0;
  d_baseDecLevel = -1;
  out.handleUserAttribute( "axiom", this );
  out.handleUserAttribute( "conjecture", this );
  out.handleUserAttribute( "fun-def", this );
  out.handleUserAttribute( "sygus", this );
  out.handleUserAttribute( "synthesis", this );
  out.handleUserAttribute( "quant-inst-max-level", this );
  out.handleUserAttribute( "rr-priority", this );
  out.handleUserAttribute( "quant-elim", this );
  out.handleUserAttribute( "quant-elim-partial", this );
}

TheoryQuantifiers::~TheoryQuantifiers() {
}

void TheoryQuantifiers::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_masterEqualityEngine = eq;
}

void TheoryQuantifiers::addSharedTerm(TNode t) {
  Debug("quantifiers-other") << "TheoryQuantifiers::addSharedTerm(): "
                     << t << endl;
}


void TheoryQuantifiers::notifyEq(TNode lhs, TNode rhs) {
  Debug("quantifiers-other") << "TheoryQuantifiers::notifyEq(): "
                     << lhs << " = " << rhs << endl;

}

void TheoryQuantifiers::preRegisterTerm(TNode n) {
  Debug("quantifiers-prereg") << "TheoryQuantifiers::preRegisterTerm() " << n << endl;
  if( n.getKind()==FORALL ){
    if( !options::cbqi() || options::recurseCbqi() || !TermDb::hasInstConstAttr(n) ){
      getQuantifiersEngine()->registerQuantifier( n );
      Debug("quantifiers-prereg") << "TheoryQuantifiers::preRegisterTerm() done " << n << endl;
    }
  }
}


void TheoryQuantifiers::presolve() {
  Debug("quantifiers-presolve") << "TheoryQuantifiers::presolve()" << endl;
  if( getQuantifiersEngine() ){
    getQuantifiersEngine()->presolve();
  }
}

void TheoryQuantifiers::ppNotifyAssertions( std::vector< Node >& assertions ) {
  Trace("quantifiers-presolve") << "TheoryQuantifiers::ppNotifyAssertions" << std::endl;
  if( getQuantifiersEngine() ){
    getQuantifiersEngine()->ppNotifyAssertions( assertions );
  }
}

Node TheoryQuantifiers::getValue(TNode n) {
  //NodeManager* nodeManager = NodeManager::currentNM();
  switch(n.getKind()) {
  case FORALL:
  case EXISTS:
    bool value;
    if( d_valuation.hasSatValue( n, value ) ){
      return NodeManager::currentNM()->mkConst(value);
    }else{
      return NodeManager::currentNM()->mkConst(false);  //FIX_THIS?
    }
    break;
  default:
    Unhandled(n.getKind());
  }
}

void TheoryQuantifiers::computeCareGraph() {
  //do nothing
}

void TheoryQuantifiers::collectModelInfo(TheoryModel* m, bool fullModel) {
  if(fullModel) {
    for(assertions_iterator i = facts_begin(); i != facts_end(); ++i) {
      if((*i).assertion.getKind() == kind::NOT) {
        Debug("quantifiers::collectModelInfo") << "got quant FALSE: " << (*i).assertion[0] << endl;
        m->assertPredicate((*i).assertion[0], false);
      } else {
        Debug("quantifiers::collectModelInfo") << "got quant TRUE : " << *i << endl;
        m->assertPredicate(*i, true);
      }
    }
  }
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
      assertUniversal( assertion );
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
          assertExistential( assertion );
          break;
        case kind::EQUAL:
          //do nothing
          break;
        case kind::INST_CLOSURE:
        default:
          Unhandled(assertion[0].getKind());
          break;
        }
      }
      break;
    default:
      Unhandled(assertion.getKind());
      break;
    }
  }
  // call the quantifiers engine to check
  getQuantifiersEngine()->check( e );
}

Node TheoryQuantifiers::getNextDecisionRequest( unsigned& priority ){
  return getQuantifiersEngine()->getNextDecisionRequest( priority );
}

void TheoryQuantifiers::assertUniversal( Node n ){
  Assert( n.getKind()==FORALL );
  if( !options::cbqi() || options::recurseCbqi() || !TermDb::hasInstConstAttr(n) ){
    getQuantifiersEngine()->assertQuantifier( n, true );
  }
}

void TheoryQuantifiers::assertExistential( Node n ){
  Assert( n.getKind()== NOT && n[0].getKind()==FORALL );
  if( !options::cbqi() || options::recurseCbqi() || !TermDb::hasInstConstAttr(n[0]) ){
    getQuantifiersEngine()->assertQuantifier( n[0], false );
  }
}

void TheoryQuantifiers::setUserAttribute(const std::string& attr, Node n, std::vector<Node> node_values, std::string str_value){
  QuantifiersAttributes::setUserAttribute( attr, n, node_values, str_value );
}
