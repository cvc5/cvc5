/*********************                                                        */
/*! \file theory_quantifiers.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of quantifiers
 **
 ** Implementation of the theory of quantifiers.
 **/


#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/valuation.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/instantiation_engine.h"
#include "theory/quantifiers/model_engine.h"
#include "expr/kind.h"
#include "util/cvc4_assert.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/quantifiers_attributes.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

TheoryQuantifiers::TheoryQuantifiers(Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo) :
  Theory(THEORY_QUANTIFIERS, c, u, out, valuation, logicInfo),
  d_numRestarts(0),
  d_masterEqualityEngine(0)
{
  d_numInstantiations = 0;
  d_baseDecLevel = -1;
  out.handleUserAttribute( "axiom", this );
  out.handleUserAttribute( "conjecture", this );
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
  if( n.getKind()==FORALL && !TermDb::hasInstConstAttr(n) ){
    getQuantifiersEngine()->registerQuantifier( n );
  }
}


void TheoryQuantifiers::presolve() {
  Debug("quantifiers-presolve") << "TheoryQuantifiers::presolve()" << endl;
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
  CodeTimer codeTimer(d_theoryTime);

  Debug("quantifiers-check") << "quantifiers::check(" << e << ")" << std::endl;
  while(!done()) {
    Node assertion = get();
    Debug("quantifiers-assert") << "quantifiers::assert(): " << assertion << std::endl;
    switch(assertion.getKind()) {
    case kind::FORALL:
      assertUniversal( assertion );
      break;
    case kind::NOT:
      {
        switch( assertion[0].getKind()) {
        case kind::FORALL:
          assertExistential( assertion );
          break;
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

void TheoryQuantifiers::propagate(Effort level){
  //CodeTimer codeTimer(d_theoryTime);
  //getQuantifiersEngine()->propagate( level );
}

Node TheoryQuantifiers::getNextDecisionRequest(){
  return getQuantifiersEngine()->getNextDecisionRequest();
}

void TheoryQuantifiers::assertUniversal( Node n ){
  Assert( n.getKind()==FORALL );
  if( options::recurseCbqi() || !TermDb::hasInstConstAttr(n) ){
    getQuantifiersEngine()->registerQuantifier( n );
    getQuantifiersEngine()->assertNode( n );
  }
}

void TheoryQuantifiers::assertExistential( Node n ){
  Assert( n.getKind()== NOT && n[0].getKind()==FORALL );
  if( options::recurseCbqi() || !TermDb::hasInstConstAttr(n[0]) ){
    if( d_skolemized.find( n )==d_skolemized.end() ){
      Node body = getQuantifiersEngine()->getTermDatabase()->getSkolemizedBody( n[0] );
      NodeBuilder<> nb(kind::OR);
      nb << n[0] << body.notNode();
      Node lem = nb;
      Trace("quantifiers-sk") << "Skolemize lemma : " << lem << std::endl;
      d_out->lemma( lem );
      d_skolemized[n] = true;
    }
  }
}

bool TheoryQuantifiers::flipDecision(){
  //Debug("quantifiers-flip") << "No instantiation given, flip decision, level = " << d_valuation.getDecisionLevel() << std::endl;
  //for( int i=1; i<=(int)d_valuation.getDecisionLevel(); i++ ){
  //  Debug("quantifiers-flip") << "   " << d_valuation.getDecision( i ) << std::endl;
  //}
  //if( d_valuation.getDecisionLevel()>0 ){
  //  double r = double(rand())/double(RAND_MAX);
  //  unsigned decisionLevel = (unsigned)(r*d_valuation.getDecisionLevel());
  //  d_out->flipDecision( decisionLevel );
  //  return true;
  //}else{
  //  return false;
  //}

  if( !d_out->flipDecision() ){
    return restart();
  }
  return true;
}

bool TheoryQuantifiers::restart(){
  static const int restartLimit = 0;
  if( d_numRestarts==restartLimit ){
    Debug("quantifiers-flip") << "No more restarts." << std::endl;
    return false;
  }else{
    d_numRestarts++;
    Debug("quantifiers-flip") << "Do restart." << std::endl;
    return true;
  }
}

void TheoryQuantifiers::setUserAttribute( const std::string& attr, Node n ){
  QuantifiersAttributes::setUserAttribute( attr, n );
}
