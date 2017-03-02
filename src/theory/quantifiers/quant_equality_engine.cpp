/*********************                                                        */
/*! \file quant_equality_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
  d_intType = NodeManager::currentNM()->integerType();
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
  if( !d_conflict ){
    Node lit = n[1].getKind()==NOT ? n[1][0] : n[1];
    bool pol = n[1].getKind()!=NOT;
    bool success = true;
    Node t1;
    Node t2;
    if( lit.getKind()==APPLY_UF || lit.getKind()==EQUAL ){
      lit = getTermDatabase()->getCanonicalTerm( lit );
      Trace("qee-debug") << "Canonical :  " << lit << ", pol = " << pol << std::endl;
      if( lit.getKind()==APPLY_UF ){
        t1 = getFunctionAppForPredicateApp( lit );
        t2 = pol ? getTermDatabase()->d_one : getTermDatabase()->d_zero;
        pol = true;
        lit = NodeManager::currentNM()->mkNode( EQUAL, t1, t2 );
      }else if( lit.getKind()==EQUAL ){
        if( lit[0].getType().isBoolean() ){
          if( lit[0].getKind()==NOT ){
            t1 = lit[0][0];
            pol = !pol;
          }else{
            t1 = lit[0];
          }
          if( lit[1].getKind()==NOT ){
            t2 = lit[1][0];
            pol = !pol;
          }else{
            t2 = lit[1];
          }
          if( t1.getKind()==APPLY_UF && t2.getKind()==APPLY_UF ){
            t1 = getFunctionAppForPredicateApp( t1 );
            t2 = getFunctionAppForPredicateApp( t2 );
            lit = NodeManager::currentNM()->mkNode( EQUAL, t1, t2 );
          }else{
            success = false;
          }
        }else{
          t1 = lit[0];
          t2 = lit[1];
        }
      }
    }else{
      success = false;
    }
    if( success ){
      bool alreadyHolds = false;
      if( pol && areUnivEqualInternal( t1, t2 ) ){
        alreadyHolds = true;
      }else if( !pol && areUnivDisequalInternal( t1, t2 ) ){
        alreadyHolds = true;
      }

      if( alreadyHolds ){
        d_quant_red.push_back( n );
        Trace("qee-debug") << "...add to redundant" << std::endl;
      }else{
        Trace("qee-debug") << "...assert" << std::endl;
        Trace("qee-assert") << "QEE : assert : " << lit << ", pol = " << pol << ", kind = " << lit.getKind() << std::endl;
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
}

bool QuantEqualityEngine::areUnivDisequalInternal( TNode n1, TNode n2 ) {
  return n1!=n2 && d_uequalityEngine.hasTerm( n1 ) && d_uequalityEngine.hasTerm( n2 ) && d_uequalityEngine.areDisequal( n1, n2, false );
}

bool QuantEqualityEngine::areUnivEqualInternal( TNode n1, TNode n2 ) {
  return n1==n2 || ( d_uequalityEngine.hasTerm( n1 ) && d_uequalityEngine.hasTerm( n2 ) && d_uequalityEngine.areEqual( n1, n2 ) );
}

TNode QuantEqualityEngine::getUnivRepresentativeInternal( TNode n ) {
  if( d_uequalityEngine.hasTerm( n ) ){
    return d_uequalityEngine.getRepresentative( n );
  }else{
    return n;
  }
}
bool QuantEqualityEngine::areUnivDisequal( TNode n1, TNode n2 ) {
  //TODO: must convert to internal representation
  return areUnivDisequalInternal( n1, n2 );
}

bool QuantEqualityEngine::areUnivEqual( TNode n1, TNode n2 ) {
  //TODO: must convert to internal representation
  return areUnivEqualInternal( n1, n2 );
}

TNode QuantEqualityEngine::getUnivRepresentative( TNode n ) {
  //TODO: must convert to internal representation
  return getUnivRepresentativeInternal( n );
}

Node QuantEqualityEngine::getFunctionForPredicate( Node f ) {
  std::map< Node, Node >::iterator it = d_pred_to_func.find( f );
  if( it==d_pred_to_func.end() ){
    std::vector< TypeNode > argTypes;
    TypeNode tn = f.getType();
    for( unsigned i=0; i<(tn.getNumChildren()-1); i++ ){
      argTypes.push_back( tn[i] );
    }
    TypeNode ftn = NodeManager::currentNM()->mkFunctionType( argTypes, d_intType  );
    std::stringstream ss;
    ss << "ee_" << f;
    Node op = NodeManager::currentNM()->mkSkolem( ss.str(), ftn, "op created for internal ee" );
    d_pred_to_func[f] = op;
    return op;
  }else{
    return it->second;
  }
}

Node QuantEqualityEngine::getFunctionAppForPredicateApp( Node n ) {
  Assert( n.getKind()==APPLY_UF );
  std::vector< Node > children;
  children.push_back( getFunctionForPredicate( n.getOperator() ) );
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    children.push_back( n[i] );
  }
  return NodeManager::currentNM()->mkNode( APPLY_UF, children );
}

