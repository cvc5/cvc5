/*********************                                                        */
/*! \file quant_equality_engine.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** Congruence closure with free variables
 **/

#include <vector>

#include "theory/quantifiers/quant_equality_engine.h"
#include "theory/rewriter.h"
#include "theory/quantifiers/term_database.h"

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;

QuantEqualityEngine::QuantEqualityEngine( QuantifiersEngine * qe, context::Context* c ) :
QuantifiersModule( qe ),
d_notify( *this ),
d_uequalityEngine(d_notify, c, "theory::quantifiers::QuantEqualityEngine", true),
d_conflict(c, false),
d_quant_red(c),
d_quant_unproc(c){
  d_uequalityEngine.addFunctionKind( kind::APPLY_UF );
}

void QuantEqualityEngine::conflict(TNode t1, TNode t2) {
  //report conflict through quantifiers engine output channel
  std::vector<TNode> assumptions;
  d_uequalityEngine.explainEquality(t1, t2, true, assumptions, NULL);
  Node conflict;
  if( assumptions.size()==1 ){
    conflict = assumptions[0];
  }else{
    conflict = NodeManager::currentNM()->mkNode( AND, assumptions );
  }
  d_conflict = true;
  Trace("qee-conflict") << "Quantifier equality engine conflict : " << conflict << std::endl;
  d_quantEngine->getOutputChannel().conflict( conflict );
}

void QuantEqualityEngine::eqNotifyNewClass(TNode t){

}
void QuantEqualityEngine::eqNotifyPreMerge(TNode t1, TNode t2){

}
void QuantEqualityEngine::eqNotifyPostMerge(TNode t1, TNode t2){

}
void QuantEqualityEngine::eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {

}

/* whether this module needs to check this round */
bool QuantEqualityEngine::needsCheck( Theory::Effort e ) {
  return e>=Theory::EFFORT_LAST_CALL;
}

/* reset at a round */
void QuantEqualityEngine::reset_round( Theory::Effort e ){
  //TODO
}

/* Call during quantifier engine's check */
void QuantEqualityEngine::check( Theory::Effort e, unsigned quant_e ) {
  //TODO
}

/* Called for new quantifiers */
void QuantEqualityEngine::registerQuantifier( Node q ) {
  //TODO
}

/** called for everything that gets asserted */
void QuantEqualityEngine::assertNode( Node n ) {
  Assert( n.getKind()==FORALL );
  Trace("qee-debug") << "QEE assert : " << n << std::endl;
  Node lit = n[1].getKind()==NOT ? n[1][0] : n[1];
  bool pol = n[1].getKind()!=NOT;
  if( lit.getKind()==APPLY_UF || lit.getKind()==EQUAL ){
    lit = getTermDatabase()->getCanonicalTerm( lit );
    Trace("qee-debug") << "Canonical :  " << lit << ", pol = " << pol << std::endl;
    Node t1 = lit.getKind()==APPLY_UF ? lit : lit[0];
    Node t2;
    if( lit.getKind()==APPLY_UF ){
      t2 = pol ? getTermDatabase()->d_true : getTermDatabase()->d_false;
      pol = true;
    }else{
      t2 = lit[1];
    }
    bool alreadyHolds = false;
    if( pol && areUnivEqual( t1, t2 ) ){
      alreadyHolds = true;
    }else if( !pol && areUnivDisequal( t1, t2 ) ){
      alreadyHolds = true;
    }

    if( alreadyHolds ){
      d_quant_red.push_back( n );
      Trace("qee-debug") << "...add to redundant" << std::endl;
    }else{
      if( lit.getKind()==APPLY_UF ){
        d_uequalityEngine.assertPredicate(lit, pol, n);
      }else{
        d_uequalityEngine.assertEquality(lit, pol, n);
      }
    }
  }else{
    d_quant_unproc[n] = true;
    Trace("qee-debug") << "...add to unprocessed (" << lit.getKind() << ")" << std::endl;
  }
}

bool QuantEqualityEngine::areUnivDisequal( TNode n1, TNode n2 ) {
  return n1!=n2 && d_uequalityEngine.hasTerm( n1 ) && d_uequalityEngine.hasTerm( n2 ) && d_uequalityEngine.areDisequal( n1, n2, false );
}

bool QuantEqualityEngine::areUnivEqual( TNode n1, TNode n2 ) {
  return n1==n2 || ( d_uequalityEngine.hasTerm( n1 ) && d_uequalityEngine.hasTerm( n2 ) && d_uequalityEngine.areEqual( n1, n2 ) );
}

TNode QuantEqualityEngine::getUnivRepresentative( TNode n ) {
  if( d_uequalityEngine.hasTerm( n ) ){
    return d_uequalityEngine.getRepresentative( n );
  }else{
    return n;
  }
}