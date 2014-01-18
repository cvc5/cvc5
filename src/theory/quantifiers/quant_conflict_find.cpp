/*********************                                                        */
/*! \file quant_conflict_find.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief quant conflict find class
 **
 **/

#include <vector>

#include "theory/quantifiers/quant_conflict_find.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/theory_engine.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace std;

namespace CVC4 {

Node QcfNodeIndex::existsTerm( TNode n, std::vector< TNode >& reps, int index ) {
  if( index==(int)reps.size() ){
    if( d_children.empty() ){
      return Node::null();
    }else{
      return d_children.begin()->first;
    }
  }else{
    if( d_children.find( reps[index] )==d_children.end() ){
      return Node::null();
    }else{
      return d_children[reps[index]].existsTerm( n, reps, index+1 );
    }
  }
}

Node QcfNodeIndex::addTerm( TNode n, std::vector< TNode >& reps, int index ) {
  if( index==(int)reps.size() ){
    if( d_children.empty() ){
      d_children[ n ].clear();
      return n;
    }else{
      return d_children.begin()->first;
    }
  }else{
    return d_children[reps[index]].addTerm( n, reps, index+1 );
  }
}

bool QcfNodeIndex::addTermEq( TNode n1, TNode n2, std::vector< TNode >& reps1, std::vector< TNode >& reps2, int index ) {
  if( index==(int)reps1.size() ){
    Node n = addTerm( n2, reps2 );
    return n==n2;
  }else{
    return d_children[reps1[index]].addTermEq( n1, n2, reps1, reps2, index+1 );
  }
}



void QcfNodeIndex::debugPrint( const char * c, int t ) {
  for( std::map< TNode, QcfNodeIndex >::iterator it = d_children.begin(); it != d_children.end(); ++it ){
    if( !it->first.isNull() ){
      for( int j=0; j<t; j++ ){ Trace(c) << "  "; }
      Trace(c) << it->first << " : " << std::endl;
      it->second.debugPrint( c, t+1 );
    }
  }
}

EqRegistry::EqRegistry( context::Context* c ) : d_active( c, false ){//: d_t_eqc( c ){

}

void EqRegistry::debugPrint( const char * c, int t ) {
  d_qni.debugPrint( c, t );
}

//QcfNode::QcfNode( context::Context* c ) : d_parent( NULL ){
//  d_reg[0] = NULL;
//  d_reg[1] = NULL;
//}

QuantConflictFind::QuantConflictFind( QuantifiersEngine * qe, context::Context* c ) :
QuantifiersModule( qe ),
d_c( c ),
d_conflict( c, false ),
d_qassert( c ) {
  d_fid_count = 0;
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);
  getFunctionId( d_true );
  getFunctionId( d_false );
}

int QuantConflictFind::getFunctionId( Node f ) {
  std::map< Node, int >::iterator it = d_fid.find( f );
  if( it==d_fid.end() ){
    d_fid[f] = d_fid_count;
    d_fid_count++;
    return d_fid[f];
  }
  return it->second;
}

bool QuantConflictFind::isLessThan( Node a, Node b ) {
  //Assert( a.getKind()==APPLY_UF );
  //Assert( b.getKind()==APPLY_UF );
  /*
  if( a.getOperator()==b.getOperator() ){
    for( unsigned i=0; i<a.getNumChildren(); i++ ){
      Node acr = getRepresentative( a[i] );
      Node bcr = getRepresentative( b[i] );
      if( acr<bcr ){
        return true;
      }else if( acr>bcr ){
        return false;
      }
    }
    return false;
  }else{
    */
  return getFunctionId( a )<getFunctionId( b );
  //}
}

Node QuantConflictFind::getFunction( Node n, int& index, bool isQuant ) {
  if( isQuant && !quantifiers::TermDb::hasBoundVarAttr( n ) ){
    index = 0;
    return n;
  }else if( isHandledUfTerm( n ) ){
    /*
    std::map< Node, Node >::iterator it = d_op_node.find( n.getOperator() );
    if( it==d_op_node.end() ){
      std::vector< Node > children;
      children.push_back( n.getOperator() );
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        children.push_back( getFv( n[i].getType() ) );
      }
      Node nn = NodeManager::currentNM()->mkNode( n.getKind(), children );
      d_op_node[n.getOperator()] = nn;
      return nn;
    }else{
      return it->second;
    }*/
    index = 1;
    return n.getOperator();
  }else{
    return Node::null();
  }
}

Node QuantConflictFind::getFv( TypeNode tn ) {
  if( d_fv.find( tn )==d_fv.end() ){
    std::stringstream ss;
    ss << "_u";
    d_fv[tn] = NodeManager::currentNM()->mkSkolem( ss.str(), tn, "is for QCF" );
  }
  return d_fv[tn];
}

Node QuantConflictFind::mkEqNode( Node a, Node b ) {
  if( a.getType().isBoolean() ){
    return a.iffNode( b );
  }else{
    return a.eqNode( b );
  }
}

//-------------------------------------------------- registration

/*
void QuantConflictFind::registerAssertions( std::vector< Node >& assertions ) {
  for( unsigned i=0; i<assertions.size(); i++ ){
    registerAssertion( assertions[i] );
  }
}

void QuantConflictFind::registerAssertion( Node n ) {
  if( n.getKind()==FORALL ){
    registerNode( Node::null(), n[1], NULL, true, true );
  }else{
    if( n.getType().isBoolean() ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        registerAssertion( n[i] );
      }
    }
  }
}
*/
void QuantConflictFind::registerNode( Node q, Node n, bool hasPol, bool pol ) {
  //qcf->d_node = n;
  bool recurse = true;
  if( n.getKind()!=OR && n.getKind()!=AND && n.getKind()!=IFF && n.getKind()!=ITE && n.getKind()!=NOT ){
    if( quantifiers::TermDb::hasBoundVarAttr( n ) ){
      //literals
      for( unsigned i=0; i<2; i++ ){
        if( !hasPol || ( pol!=(i==0) ) ){
          EqRegistry * eqr = getEqRegistry( i==0, n );
          if( eqr ){
            d_qinfo[q].d_rel_eqr[ eqr ] = true;
          }
        }
      }
      if( n.getKind()==APPLY_UF ||
          ( n.getKind()==EQUAL && ( n[0].getKind()==BOUND_VARIABLE || n[1].getKind()==BOUND_VARIABLE ) ) ){
        flatten( q, n );
      }else{
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          flatten( q, n[i] );
        }
      }
    }else{
      Trace("qcf-qregister") << "    RegisterGroundLit : " << n;
    }
    recurse = false;
  }
  if( recurse ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      bool newHasPol;
      bool newPol;
      QuantPhaseReq::getPolarity( n, i, hasPol, pol, newHasPol, newPol );
      //QcfNode * qcfc = new QcfNode( d_c );
      //qcfc->d_parent = qcf;
      //qcf->d_child[i] = qcfc;
      registerNode( q, n[i], newHasPol, newPol );
    }
  }
}

void QuantConflictFind::flatten( Node q, Node n ) {
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    if( quantifiers::TermDb::hasBoundVarAttr( n[i] ) && n.getKind()!=BOUND_VARIABLE ){
      if( d_qinfo[q].d_var_num.find( n[i] )==d_qinfo[q].d_var_num.end() ){
        //Trace("qcf-qregister") << "    Flatten term " << n[i] << std::endl;
        d_qinfo[q].d_var_num[n[i]] = d_qinfo[q].d_vars.size();
        d_qinfo[q].d_vars.push_back( n[i] );
        flatten( q, n[i] );
      }
    }
  }
}

void QuantConflictFind::registerQuantifier( Node q ) {
  d_quants.push_back( q );
  d_quant_id[q] = d_quants.size();
  Trace("qcf-qregister") << "Register ";
  debugPrintQuant( "qcf-qregister", q );
  Trace("qcf-qregister") << " : " << q << std::endl;

  //register the variables
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    d_qinfo[q].d_var_num[q[0][i]] = i;
    d_qinfo[q].d_vars.push_back( q[0][i] );
  }

  //make QcfNode structure
  Trace("qcf-qregister") << "- Get relevant equality/disequality pairs, calculate flattening..." << std::endl;
  //d_qinfo[q].d_cf = new QcfNode( d_c );
  registerNode( q, q[1], true, true );

  //debug print
  Trace("qcf-qregister") << "- Flattened structure is :" << std::endl;
  Trace("qcf-qregister") << "    ";
  debugPrintQuantBody( "qcf-qregister", q, q[1] );
  Trace("qcf-qregister") << std::endl;
  if( d_qinfo[q].d_vars.size()>q[0].getNumChildren() ){
    Trace("qcf-qregister") << "  with additional constraints : " << std::endl;
    for( unsigned j=q[0].getNumChildren(); j<d_qinfo[q].d_vars.size(); j++ ){
      Trace("qcf-qregister") << "    ?x" << j << " = ";
      debugPrintQuantBody( "qcf-qregister", q, d_qinfo[q].d_vars[j], false );
      Trace("qcf-qregister") << std::endl;
    }
  }

  Trace("qcf-qregister") << "- Make match gen structure..." << std::endl;
  d_qinfo[q].d_mg = new MatchGen( this, q, q[1], true );

  for( unsigned j=q[0].getNumChildren(); j<d_qinfo[q].d_vars.size(); j++ ){
    d_qinfo[q].d_var_mg[j] = new MatchGen( this, q, d_qinfo[q].d_vars[j], false, true );
    if( !d_qinfo[q].d_var_mg[j]->isValid() ){
      d_qinfo[q].d_mg->setInvalid();
      break;
    }
  }

  Trace("qcf-qregister") << "Done registering quantifier." << std::endl;
}

EqRegistry * QuantConflictFind::getEqRegistry( bool polarity, Node lit, bool doCreate ) {
  Assert( quantifiers::TermDb::hasBoundVarAttr( lit ) );
  int i;
  Node f1;
  Node f2;
  int f1Index;
  int f2Index;
  if( lit.getKind()==EQUAL ){
    i = polarity ? 0 : 1;
    f1 = getFunction( lit[0], f1Index, true );
    f2 = getFunction( lit[1], f2Index, true );
  }else if( lit.getKind()==APPLY_UF ){
    i = 0;
    f1 = getFunction( lit, f1Index, true );
    f2 = polarity ? d_true : d_false;
    f2Index = 0;
  }
  if( !f1.isNull() && !f2.isNull() ){
    if( d_eqr[i][f1Index][f1][f2Index].find( f2 )==d_eqr[i][f1Index][f1][f2Index].end() ){
      if( doCreate ){
        Trace("qcf-register") << "RegisterEqr : " << f1 << " " << f2 << ", polarity = " << (i==0) << ", indices : " << f1Index << " " << f2Index << std::endl;
        d_eqr[i][f1Index][f1][f2Index][f2] = new EqRegistry( d_c );
        d_eqr[i][f2Index][f2][f1Index][f1] = d_eqr[i][f1Index][f1][f2Index][f2];
      }else{
        return NULL;
      }
    }
    return d_eqr[i][f1Index][f1][f2Index][f2];
  }else{
    return NULL;
  }
}

void QuantConflictFind::getEqRegistryApps( Node lit, std::vector< Node >& terms ) {
  Assert( quantifiers::TermDb::hasBoundVarAttr( lit ) );
  if( lit.getKind()==EQUAL ){
    for( unsigned i=0; i<2; i++ ){
      if( quantifiers::TermDb::hasBoundVarAttr( lit[i] ) ){
        if( lit[i].getKind()==BOUND_VARIABLE ){
          //do not handle variable equalities
          terms.clear();
          return;
        }else{
          terms.push_back( lit[i] );
        }
      }
    }
    if( terms.size()==2 && isLessThan( terms[1].getOperator(), terms[0].getOperator() ) ){
      Node t = terms[0];
      terms[0] = terms[1];
      terms[1] = t;
    }
  }else if( lit.getKind()==APPLY_UF ){
    terms.push_back( lit );
  }
}

int QuantConflictFind::evaluate( Node n, bool pref, bool hasPref ) {
  int ret = 0;
  if( n.getKind()==EQUAL ){
    Node n1 = getTerm( n[0] );
    Node n2 = getTerm( n[1] );
    Debug("qcf-eval") << "Evaluate : Normalize " << n << " to " << n1 << " = " << n2 << std::endl;
    if( areEqual( n1, n2 ) ){
      ret = 1;
    }else if( areDisequal( n1, n2 ) ){
      ret = -1;
    }
  }else if( n.getKind()==APPLY_UF ){  //predicate
    Node nn = getTerm( n );
    Debug("qcf-eval") << "Evaluate : Normalize " << nn << " to " << n << std::endl;
    if( areEqual( nn, d_true ) ){
      ret = 1;
    }else if( areEqual( nn, d_false ) ){
      ret = -1;
    }
  }else if( n.getKind()==NOT ){
    return -evaluate( n[0] );
  }else if( n.getKind()==ITE ){
    int cev1 = evaluate( n[0] );
    int cevc[2] = { 0, 0 };
    for( unsigned i=0; i<2; i++ ){
      if( ( i==0 && cev1!=-1 ) || ( i==1 && cev1!=1 ) ){
        cevc[i] = evaluate( n[i+1] );
        if( cev1!=0 ){
          ret = cevc[i];
          break;
        }else if( cevc[i]==0 ){
          break;
        }
      }
    }
    if( ret==0 && cevc[0]!=0 && cevc[0]==cevc[1] ){
      ret = cevc[0];
    }
  }else if( n.getKind()==IFF ){
    int cev1 = evaluate( n[0] );
    if( cev1!=0 ){
      int cev2 = evaluate( n[1] );
      if( cev2!=0 ){
        ret = cev1==cev2 ? 1 : -1;
      }
    }

  }else{
    int ssval = 0;
    if( n.getKind()==OR ){
      ssval = 1;
    }else if( n.getKind()==AND ){
      ssval = -1;
    }
    bool isUnk = false;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      int cev = evaluate( n[i] );
      if( cev==ssval ){
        ret = ssval;
        break;
      }else if( cev==0 ){
        isUnk = true;
      }
    }
    if( ret==0 && !isUnk ){
      ret = -ssval;
    }
  }
  Debug("qcf-eval") << "Evaluate " << n << " to " << ret << std::endl;
  return ret;
}

bool QuantConflictFind::isPropagationSet() {
  return !d_prop_eq[0].isNull();
}

bool QuantConflictFind::areMatchEqual( TNode n1, TNode n2 ) {
  return n1==n2;
  /*
  if( n1==n2 ){
    return true;
  }else if( isPropagationSet() && d_prop_pol ){
    return ( d_prop_eq[0]==n1 && d_prop_eq[1]==n2 ) || ( d_prop_eq[0]==n2 && d_prop_eq[1]==n1 );
  }
  */
}

bool QuantConflictFind::areMatchDisequal( TNode n1, TNode n2 ) {
  //return n1!=n2;
  return areDisequal( n1, n2 );
  /*
  if( n1!=n2 ){
    return true;
  }else if( isPropagationSet() && !d_prop_pol ){
    return ( d_prop_eq[0]==n1 && d_prop_eq[1]==n2 ) || ( d_prop_eq[0]==n2 && d_prop_eq[1]==n1 );
  }
  */
}

//-------------------------------------------------- handling assertions / eqc

void QuantConflictFind::assertNode( Node q ) {
  Trace("qcf-proc") << "QCF : assertQuantifier : ";
  debugPrintQuant("qcf-proc", q);
  Trace("qcf-proc") << std::endl;
  d_qassert.push_back( q );
  //set the eqRegistries that this depends on to true
  for( std::map< EqRegistry *, bool >::iterator it = d_qinfo[q].d_rel_eqr.begin(); it != d_qinfo[q].d_rel_eqr.end(); ++it ){
    it->first->d_active.set( true );
  }
}

eq::EqualityEngine * QuantConflictFind::getEqualityEngine() {
  //return ((uf::TheoryUF*)d_quantEngine->getTheoryEngine()->theoryOf( theory::THEORY_UF ))->getEqualityEngine();
  return d_quantEngine->getTheoryEngine()->getMasterEqualityEngine();
}
bool QuantConflictFind::areEqual( Node n1, Node n2 ) {
  return getEqualityEngine()->hasTerm( n1 ) && getEqualityEngine()->hasTerm( n2 ) && getEqualityEngine()->areEqual( n1,n2 );
}
bool QuantConflictFind::areDisequal( Node n1, Node n2 ) {
  return getEqualityEngine()->hasTerm( n1 ) && getEqualityEngine()->hasTerm( n2 ) && getEqualityEngine()->areDisequal( n1,n2, false );
}
Node QuantConflictFind::getRepresentative( Node n ) {
  if( getEqualityEngine()->hasTerm( n ) ){
    return getEqualityEngine()->getRepresentative( n );
  }else{
    return n;
  }
}
Node QuantConflictFind::getTerm( Node n ) {
  if( isHandledUfTerm( n ) ){
    computeArgReps( n );
    Node nn = d_uf_terms[n.getOperator()].existsTerm( n, d_arg_reps[n] );
    if( !nn.isNull() ){
      return nn;
    }
  }
  return n;
}

QuantConflictFind::EqcInfo * QuantConflictFind::getEqcInfo( Node n, bool doCreate ) {
  std::map< Node, EqcInfo * >::iterator it2 = d_eqc_info.find( n );
  if( it2==d_eqc_info.end() ){
    if( doCreate ){
      EqcInfo * eqci = new EqcInfo( d_c );
      d_eqc_info[n] = eqci;
      return eqci;
    }else{
      return NULL;
    }
  }
  return it2->second;
}

QcfNodeIndex * QuantConflictFind::getQcfNodeIndex( Node eqc, Node f ) {
  std::map< TNode, QcfNodeIndex >::iterator itut = d_eqc_uf_terms[ eqc ].find( f );
  if( itut!=d_eqc_uf_terms[ eqc ].end() ){
    return &itut->second;
  }else{
    return NULL;
  }
}

QcfNodeIndex * QuantConflictFind::getQcfNodeIndex( Node f ) {
  std::map< TNode, QcfNodeIndex >::iterator itut = d_uf_terms.find( f );
  if( itut!=d_uf_terms.end() ){
    return &itut->second;
  }else{
    return NULL;
  }
}

/** new node */
void QuantConflictFind::newEqClass( Node n ) {
  Trace("qcf-proc-debug") << "QCF : newEqClass : " << n << std::endl;

  Trace("qcf-proc2-debug") << "QCF : finished newEqClass : " << n << std::endl;
}

/** merge */
void QuantConflictFind::merge( Node a, Node b ) {
  if( b.getKind()==EQUAL ){
    if( a==d_true ){
      //will merge anyways
      //merge( b[0], b[1] );
    }else if( a==d_false ){
      assertDisequal( b[0], b[1] );
    }
  }else{
    Trace("qcf-proc") << "QCF : merge : " << a << " " << b << std::endl;
    EqcInfo * eqc_b = getEqcInfo( b, false );
    EqcInfo * eqc_a = NULL;
    if( eqc_b ){
      eqc_a = getEqcInfo( a );
      //move disequalities of b into a
      for( NodeBoolMap::iterator it = eqc_b->d_diseq.begin(); it != eqc_b->d_diseq.end(); ++it ){
        if( (*it).second ){
          Node n = (*it).first;
          EqcInfo * eqc_n = getEqcInfo( n, false );
          Assert( eqc_n );
          if( !eqc_n->isDisequal( a ) ){
            Assert( !eqc_a->isDisequal( n ) );
            eqc_n->setDisequal( a );
            eqc_a->setDisequal( n );
            //setEqual( eqc_a, eqc_b, a, n, false );
          }
          eqc_n->setDisequal( b, false );
        }
      }
      /*
      //move all previous EqcRegistry's regarding equalities within b
      for( NodeBoolMap::iterator it = eqc_b->d_rel_eqr_e.begin(); it != eqc_b->d_rel_eqr_e.end(); ++it ){
        if( (*it).second ){
          eqc_a->d_rel_eqr_e[(*it).first] = true;
        }
      }
      */
    }
    //process new equalities
    //setEqual( eqc_a, eqc_b, a, b, true );
    Trace("qcf-proc2") << "QCF : finished merge : " << a << " " << b << std::endl;
  }
}

/** assert disequal */
void QuantConflictFind::assertDisequal( Node a, Node b ) {
  a = getRepresentative( a );
  b = getRepresentative( b );
  Trace("qcf-proc") << "QCF : assert disequal : " << a << " " << b << std::endl;
  EqcInfo * eqc_a = getEqcInfo( a );
  EqcInfo * eqc_b = getEqcInfo( b );
  if( !eqc_a->isDisequal( b ) ){
    Assert( !eqc_b->isDisequal( a ) );
    eqc_b->setDisequal( a );
    eqc_a->setDisequal( b );
    //setEqual( eqc_a, eqc_b, a, b, false );
  }
  Trace("qcf-proc2") << "QCF : finished assert disequal : " << a << " " << b << std::endl;
}

//-------------------------------------------------- check function

/** check */
void QuantConflictFind::check( Theory::Effort level ) {
  Trace("qcf-check") << "QCF : check : " << level << std::endl;
  if( d_conflict ){
    Trace("qcf-check2") << "QCF : finished check : already in conflict." << std::endl;
    if( level>=Theory::EFFORT_FULL ){
      Assert( false );
    }
  }else{
    int addedLemmas = 0;
    if( d_performCheck ){
      ++(d_statistics.d_inst_rounds);
      double clSet = 0;
      if( Trace.isOn("qcf-engine") ){
        clSet = double(clock())/double(CLOCKS_PER_SEC);
        Trace("qcf-engine") << "---Conflict Find Engine Round, effort = " << level << "---" << std::endl;
      }
      Trace("qcf-check") << "Compute relevant equalities..." << std::endl;
      computeRelevantEqr();

      if( Trace.isOn("qcf-debug") ){
        Trace("qcf-debug") << std::endl;
        debugPrint("qcf-debug");
        Trace("qcf-debug") << std::endl;
      }

      for( short e = effort_conflict; e<=effort_conflict; e++ ){
        d_effort = e;
        if( e == effort_propagation ){
          for( unsigned i=0; i<2; i++ ){
            d_prop_eq[i] = Node::null();
          }
        }
        Trace("qcf-check") << "Checking quantified formulas..." << std::endl;
        for( unsigned j=0; j<d_qassert.size(); j++ ){
          Node q = d_qassert[j];
          Trace("qcf-check") << "Check quantified formula ";
          debugPrintQuant("qcf-check", q);
          Trace("qcf-check") << " : " << q << "..." << std::endl;

          Assert( d_qinfo.find( q )!=d_qinfo.end() );
          if( d_qinfo[q].d_mg->isValid() ){
            d_qinfo[q].reset_round( this );
            //try to make a matches making the body false
            d_qinfo[q].d_mg->reset( this, false, q );
            while( d_qinfo[q].d_mg->getNextMatch( this, q ) ){

              Trace("qcf-check") << "*** Produced match : " << std::endl;
              d_qinfo[q].debugPrintMatch("qcf-check");
              Trace("qcf-check") << std::endl;

              if( !d_qinfo[q].isMatchSpurious( this ) ){
                std::vector< int > assigned;
                if( d_qinfo[q].completeMatch( this, q, assigned ) ){
                  InstMatch m;
                  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
                    Node cv = d_qinfo[q].getCurrentValue( d_qinfo[q].d_match[i] );
                    Debug("qcf-check-inst") << "INST : " << i << " -> " << cv << ", from " << d_qinfo[q].d_match[i] << std::endl;
                    m.set( d_quantEngine, q, i, cv );
                  }
                  if( Debug.isOn("qcf-check-inst") ){
                    Node inst = d_quantEngine->getInstantiation( q, m );
                    Debug("qcf-check-inst") << "Check instantiation " << inst << "..." << std::endl;
                    Assert( evaluate( inst )==-1 );
                  }
                  if( d_quantEngine->addInstantiation( q, m ) ){
                    Trace("qcf-check") << "   ... Added instantiation" << std::endl;
                    ++addedLemmas;
                    if( e==effort_conflict ){
                      d_conflict.set( true );
                      ++(d_statistics.d_conflict_inst);
                      break;
                    }else if( e==effort_propagation ){
                      ++(d_statistics.d_prop_inst);
                    }
                  }else{
                    Trace("qcf-check") << "   ... Failed to add instantiation" << std::endl;
                    Assert( false );
                  }
                  //clean up assigned
                  for( unsigned i=0; i<assigned.size(); i++ ){
                    d_qinfo[q].d_match.erase( assigned[i] );
                  }
                }else{
                  Trace("qcf-check") << "   ... Spurious instantiation (cannot assign unassigned variables)" << std::endl;
                }
              }else{
                Trace("qcf-check") << "   ... Spurious instantiation (does not meet variable constraints)" << std::endl;
              }
            }
          }
          if( d_conflict ){
            break;
          }
        }
        if( Trace.isOn("qcf-engine") ){
          double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
          Trace("qcf-engine") << "Finished conflict find engine, time = " << (clSet2-clSet) << ", addedLemmas = " << addedLemmas << std::endl;
        }
        if( addedLemmas>0 ){
          d_quantEngine->flushLemmas();
        }
      }
    }
    Trace("qcf-check2") << "QCF : finished check : " << level << std::endl;
  }
}

bool QuantConflictFind::needsCheck( Theory::Effort level ) {
  d_performCheck = false;
  if( !d_conflict ){
    if( level==Theory::EFFORT_FULL ){
      d_performCheck = options::qcfWhenMode()==QCF_WHEN_MODE_DEFAULT;
    }else if( level==Theory::EFFORT_STANDARD ){
      d_performCheck = options::qcfWhenMode()==QCF_WHEN_MODE_STD;
    }
  }
  return d_performCheck;
}

void QuantConflictFind::computeRelevantEqr() {
  //first, reset information
  for( unsigned i=0; i<2; i++ ){
    for( unsigned j=0; j<2; j++ ){
      for( std::map< TNode, std::map< int, std::map< TNode, EqRegistry * > > >::iterator it = d_eqr[i][j].begin(); it != d_eqr[i][j].end(); ++it ){
        for( unsigned jj=0; jj<2; jj++ ){
          for( std::map< TNode, EqRegistry * >::iterator it2 = it->second[jj].begin(); it2 != it->second[jj].end(); ++it2 ){
            it2->second->clear();
          }
        }
      }
    }
  }
  d_uf_terms.clear();
  d_eqc_uf_terms.clear();
  d_eqcs.clear();
  d_arg_reps.clear();
  double clSet = 0;
  if( Trace.isOn("qcf-opt") ){
    clSet = double(clock())/double(CLOCKS_PER_SEC);
  }

  long nTermst = 0;
  long nTerms = 0;
  long nEqc = 0;
  long nEq1 = 0;
  long nEq2 = 0;
  long nEq1t = 0;
  long nEq2t = 0;
  long nComp = 0;
  //relevant nodes for eq registries
  std::map< TNode, std::map< TNode, std::vector< TNode > > > eqr_to_node[2];

  //which nodes are irrelevant for disequality matches
  std::map< TNode, bool > irrelevant_dnode;
  //now, store matches
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( getEqualityEngine() );
  while( !eqcs_i.isFinished() ){
    nEqc++;
    Node r = (*eqcs_i);
    d_eqcs[r.getType()].push_back( r );
    EqcInfo * eqcir = getEqcInfo( r, false );
    //get relevant nodes that we are disequal from
    std::vector< Node > deqc;
    if( eqcir ){
      for( NodeBoolMap::iterator it = eqcir->d_diseq.begin(); it != eqcir->d_diseq.end(); ++it ){
        if( (*it).second ){
          //Node rd = (*it).first;
          //if( rd!=getRepresentative( rd ) ){
          //  std::cout << "Bad rep!" << std::endl;
          //  exit( 0 );
          //}
          deqc.push_back( (*it).first );
        }
      }
    }
    //the relevant nodes in this eqc
    std::vector< Node > eqc;
    //process disequalities
    eq::EqClassIterator eqc_i = eq::EqClassIterator( r, getEqualityEngine() );
    while( !eqc_i.isFinished() ){
      TNode n = (*eqc_i);
      if( n.getKind()!=EQUAL ){
        nTermst++;
        //node_to_rep[n] = r;
        //if( n.getNumChildren()>0 ){
        //  if( n.getKind()!=APPLY_UF ){
        //    std::cout << n.getKind() << " " << n.getOperator() << " " << n << std::endl;
        //  }
        //}

        bool isRedundant;
        std::map< TNode, std::vector< TNode > >::iterator it_na;
        TNode fn;
        if( isHandledUfTerm( n ) ){
          computeArgReps( n );
          it_na = d_arg_reps.find( n );
          Assert( it_na!=d_arg_reps.end() );
          Node nadd = d_eqc_uf_terms[r][n.getOperator()].addTerm( n, d_arg_reps[n] );
          isRedundant = (nadd!=n);
          d_uf_terms[n.getOperator()].addTerm( n, d_arg_reps[n] );
          if( !isRedundant ){
            int jindex;
            fn = getFunction( n, jindex );
          }
        }else{
          isRedundant = false;
        }
        nTerms += isRedundant ? 0 : 1;

        Trace("qcf-reqr") << "^ Process " << n << std::endl;
        //process all relevant equalities and disequalities to n
        for( unsigned index=0; index<2; index++ ){
          std::map< TNode, std::map< int, std::map< TNode, EqRegistry * > > >::iterator itn[2];
          itn[0] = d_eqr[index][0].find( n );
          if( !fn.isNull() ){
            itn[1] = d_eqr[index][1].find( fn );
          }
          //for n, fn...
          bool relevant = false;
          for( unsigned j=0; j<2; j++ ){
            //if this node is relevant as an ground term or f-application
            if( ( j==0 || !fn.isNull() ) && itn[j]!=d_eqr[index][j].end() ){
              relevant = true;
              for( unsigned jj=0; jj<2; jj++ ){
                if( j==1 || jj==1 ){
                  Trace("qcf-reqr") << "^^ " << index << " " << j << " " << jj << std::endl;
                  //check with others
                  for( std::map< TNode, EqRegistry * >::iterator itm = itn[j]->second[jj].begin(); itm != itn[j]->second[jj].end(); ++itm ){
                    std::map< TNode, std::map< TNode, std::vector< TNode > > >::iterator itv = eqr_to_node[index].find( itm->first );
                    if( itv!=eqr_to_node[index].end() ){
                      //for( unsigned k=0; k<itv->second.size(); k++ ){
                      for( std::map< TNode, std::vector< TNode > >::iterator itvr = itv->second.begin(); itvr != itv->second.end(); ++itvr ){
                        TNode mr = itvr->first;
                        //Assert( j==0 || getFunction( m )==itm->first );
                        nComp++;
                        //if it is equal or disequal to this
                        if( ( index==0 && mr==r ) ||
                            ( index==1 && std::find( deqc.begin(), deqc.end(), mr )!=deqc.end() ) ){
                          Debug("qcf-reqr") << "^^ Check with : " << itv->first << ", # = " << itvr->second.size() << std::endl;
                          for( unsigned k=0; k<itvr->second.size(); k++ ){
                            TNode m = itvr->second[k];
                            Debug("qcf-reqr") << "Comparing " << n << " and " << m << ", j = " << j << ", index = " << index << std::endl;
                            Debug("qcf-reqr") << "Meets the criteria of " << itn[j]->first << " " << itm->first << std::endl;
                            //process equality/disequality
                            if( j==0 ){
                              Assert( d_arg_reps.find( m )!=d_arg_reps.end() );
                              //n with fm
                              nEq1t++;
                              if( itm->second->d_qni.addTerm( m, d_arg_reps[m] )==m ){
                                nEq1++;
                                Debug("qcf-reqr") << "Add relevant : " << n << (index==0?"":"!") << "=" << m << " for ";
                                Debug("qcf-reqr") << n << " " << itm->first << std::endl;
                              }
                            }else{
                              if( jj==0 ){
                                //fn with m
                                nEq1t++;
                                if( itm->second->d_qni.addTerm( n, it_na->second )==n ){
                                  nEq1++;
                                  Debug("qcf-reqr") << "Add relevant : " << n << (index==0?"":"!") << "=" << m << " for ";
                                  Debug("qcf-reqr") << fn << " " << m << std::endl;
                                }
                              }else{
                                Assert( d_arg_reps.find( m )!=d_arg_reps.end() );
                                //fn with fm
                                bool mltn = isLessThan( itm->first, fn );
                                for( unsigned i=0; i<2; i++ ){
                                  if( i==0 || itm->first==fn ){
                                    TNode am = ((i==0)==mltn) ? n : m;
                                    TNode an = ((i==0)==mltn) ? m : n;
                                    nEq2t++;
                                    if( itm->second->d_qni.addTermEq( an, am, it_na->second, d_arg_reps[m] ) ){
                                      nEq2++;
                                      Debug("qcf-reqr") << "Add relevant (eq) : " << an << (index==0?"":"!") << "=" << am << " for ";
                                      Debug("qcf-reqr") << fn << " " << itm->first << std::endl;
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
              Trace("qcf-reqr") << "- Node " << n << " is relevant for " << (j==0 ? n : fn) << ", index = " << index << std::endl;
              //add it to relevant
              eqr_to_node[index][j==0 ? n : fn][r].push_back( n );
            }
          }
          if( !relevant ){
            //if not relevant for disequalities, store it
            if( index==1 ){
              irrelevant_dnode[n] = true;
            }
          }else{
            //if relevant for equalities, store it
            if( index==0 ){
              eqc.push_back( n );
            }
          }
        }
      }
      ++eqc_i;
    }
    //process_eqc[r] = true;
    ++eqcs_i;
  }
  if( Trace.isOn("qcf-opt") ){
    double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
    Trace("qcf-opt") << "Compute rel eqc : " << std::endl;
    Trace("qcf-opt") << "   " << nEqc << " equivalence classes. " << std::endl;
    Trace("qcf-opt") << "   " << nTerms << " / " << nTermst << " terms." << std::endl;
    Trace("qcf-opt") << "   " << nEq1 << " / " << nEq1t << " pattern terms." << std::endl;
    Trace("qcf-opt") << "   " << nEq2 << " / " << nEq2t << " pattern equalities." << std::endl;
    Trace("qcf-opt") << "   " << nComp << " compares." << std::endl;
    Trace("qcf-opt") << "   Time : " << (clSet2-clSet) << std::endl;
  }
}

void QuantConflictFind::computeArgReps( TNode n ) {
  if( d_arg_reps.find( n )==d_arg_reps.end() ){
    Assert( isHandledUfTerm( n ) );
    for( unsigned j=0; j<n.getNumChildren(); j++ ){
      d_arg_reps[n].push_back( getRepresentative( n[j] ) );
    }
  }
}
bool QuantConflictFind::isHandledUfTerm( TNode n ) {
  return n.getKind()==APPLY_UF;
}

void QuantConflictFind::QuantInfo::reset_round( QuantConflictFind * p ) {
  d_match.clear();
  d_curr_var_deq.clear();
  //add built-in variable constraints
  for( unsigned r=0; r<2; r++ ){
    for( std::map< int, std::vector< Node > >::iterator it = d_var_constraint[r].begin();
         it != d_var_constraint[r].end(); ++it ){
      for( unsigned j=0; j<it->second.size(); j++ ){
        Node rr = it->second[j];
        if( !isVar( rr ) ){
          rr = p->getRepresentative( rr );
        }
        if( addConstraint( p, it->first, rr, r==0 )==-1 ){
          d_var_constraint[0].clear();
          d_var_constraint[1].clear();
          //quantified formula is actually equivalent to true
          Trace("qcf-qregister") << "Quantifier is equivalent to true!!!" << std::endl;
          d_mg->d_children.clear();
          d_mg->d_n = NodeManager::currentNM()->mkConst( true );
          d_mg->d_type = MatchGen::typ_ground;
          return;
        }
      }
    }
  }
  d_mg->reset_round( p );
  for( std::map< int, MatchGen * >::iterator it = d_var_mg.begin(); it != d_var_mg.end(); ++it ){
    it->second->reset_round( p );
  }
}

int QuantConflictFind::QuantInfo::getCurrentRepVar( int v ) {
  std::map< int, Node >::iterator it = d_match.find( v );
  if( it!=d_match.end() ){
    int vn = getVarNum( it->second );
    if( vn!=-1 ){
      //int vr = getCurrentRepVar( vn );
      //d_match[v] = d_vars[vr];
      //return vr;
      return getCurrentRepVar( vn );
    }
  }
  return v;
}

Node QuantConflictFind::QuantInfo::getCurrentValue( Node n ) {
  int v = getVarNum( n );
  if( v==-1 ){
    return n;
  }else{
    std::map< int, Node >::iterator it = d_match.find( v );
    if( it==d_match.end() ){
      return n;
    }else{
      Assert( getVarNum( it->second )!=v );
      return getCurrentValue( it->second );
    }
  }
}

bool QuantConflictFind::QuantInfo::getCurrentCanBeEqual( QuantConflictFind * p, int v, Node n ) {
  //check disequalities
  for( std::map< Node, int >::iterator it = d_curr_var_deq[v].begin(); it != d_curr_var_deq[v].end(); ++it ){
    Node cv = getCurrentValue( it->first );
    Debug("qcf-ccbe") << "compare " << cv << " " << n << std::endl;
    if( cv==n ){
      return false;
    }else if( !isVar( n ) && !isVar( cv ) ){
      //they must actually be disequal
      if( !p->areMatchDisequal( n, cv ) ){
        return false;
      }
    }
  }
  return true;
}

int QuantConflictFind::QuantInfo::addConstraint( QuantConflictFind * p, int v, Node n, bool polarity ) {
  v = getCurrentRepVar( v );
  int vn = getVarNum( n );
  vn = vn==-1 ? -1 : getCurrentRepVar( vn );
  n = getCurrentValue( n );
  return addConstraint( p, v, n, vn, polarity, false );
}

int QuantConflictFind::QuantInfo::addConstraint( QuantConflictFind * p, int v, Node n, int vn, bool polarity, bool doRemove ) {
  //for handling equalities between variables, and disequalities involving variables
  Debug("qcf-match-debug") << "- " << (doRemove ? "un" : "" ) << "constrain : " << v << " -> " << n << " (cv=" << getCurrentValue( n ) << ")";
  Debug("qcf-match-debug") << ", (vn=" << vn << "), polarity = " << polarity << std::endl;
  Assert( doRemove || n==getCurrentValue( n ) );
  Assert( doRemove || v==getCurrentRepVar( v ) );
  Assert( doRemove || vn==getCurrentRepVar( getVarNum( n ) ) );
  if( polarity ){
    if( vn!=v ){
      if( doRemove ){
        if( vn!=-1 ){
          //if set to this in the opposite direction, clean up opposite instead
          std::map< int, Node >::iterator itmn = d_match.find( vn );
          if( itmn!=d_match.end() && itmn->second==d_vars[v] ){
            return addConstraint( p, vn, d_vars[v], v, true, true );
          }else{
            //unsetting variables equal
            std::map< int, std::map< Node, int > >::iterator itd = d_curr_var_deq.find( vn );
            if( itd!=d_curr_var_deq.end() ){
              //remove disequalities owned by this
              std::vector< Node > remDeq;
              for( std::map< Node, int >::iterator it = itd->second.begin(); it != itd->second.end(); ++it ){
                if( it->second==v ){
                  remDeq.push_back( it->first );
                }
              }
              for( unsigned i=0; i<remDeq.size(); i++ ){
                d_curr_var_deq[vn].erase( remDeq[i] );
              }
            }
          }
        }
        d_match.erase( v );
        return 1;
      }else{
        std::map< int, Node >::iterator itm = d_match.find( v );

        if( vn!=-1 ){
          Debug("qcf-match-debug") << "  ...Variable bound to variable" << std::endl;
          std::map< int, Node >::iterator itmn = d_match.find( vn );
          if( itm==d_match.end() ){
            //setting variables equal
            bool alreadySet = false;
            if( itmn!=d_match.end() ){
              alreadySet = true;
              Assert( !itmn->second.isNull() && !isVar( itmn->second ) );
            }

            //copy or check disequalities
            std::map< int, std::map< Node, int > >::iterator itd = d_curr_var_deq.find( v );
            if( itd!=d_curr_var_deq.end() ){
              for( std::map< Node, int >::iterator it = itd->second.begin(); it != itd->second.end(); ++it ){
                Node dv = getCurrentValue( it->first );
                if( !alreadySet ){
                  if( d_curr_var_deq[vn].find( dv )==d_curr_var_deq[vn].end() ){
                    d_curr_var_deq[vn][dv] = v;
                  }
                }else{
                  if( !p->areMatchDisequal( itmn->second, dv ) ){
                    Debug("qcf-match-debug") << "  -> fail, conflicting disequality" << std::endl;
                    return -1;
                  }
                }
              }
            }
            if( alreadySet ){
              n = getCurrentValue( n );
            }
          }else{
            if( itmn==d_match.end() ){
              Debug("qcf-match-debug") << " ...Reverse direction" << std::endl;
              //set the opposite direction
              return addConstraint( p, vn, d_vars[v], v, true, false );
            }else{
              Debug("qcf-match-debug") << "  -> Both variables bound, compare" << std::endl;
              //are they currently equal
              return p->areMatchEqual( itm->second, itmn->second ) ? 0 : -1;
            }
          }
        }else{
          Debug("qcf-match-debug") << "  ...Variable bound to ground" << std::endl;
          if( itm==d_match.end() ){

          }else{
            //compare ground values
            Debug("qcf-match-debug") << "  -> Ground value, compare " << itm->second << " "<< n << std::endl;
            return p->areMatchEqual( itm->second, n ) ? 0 : -1;
          }
        }
        if( setMatch( p, v, n ) ){
          Debug("qcf-match-debug") << "  -> success" << std::endl;
          return 1;
        }else{
          Debug("qcf-match-debug") << "  -> fail, conflicting disequality" << std::endl;
          return -1;
        }
      }
    }else{
      Debug("qcf-match-debug") << "  -> redundant, variable identity" << std::endl;
      return 0;
    }
  }else{
    if( vn==v ){
      Debug("qcf-match-debug") << "  -> fail, variable identity" << std::endl;
      return -1;
    }else{
      if( doRemove ){
        Assert( d_curr_var_deq[v].find( n )!=d_curr_var_deq[v].end() );
        d_curr_var_deq[v].erase( n );
        return 1;
      }else{
        if( d_curr_var_deq[v].find( n )==d_curr_var_deq[v].end() ){
          //check if it respects equality
          std::map< int, Node >::iterator itm = d_match.find( v );
          if( itm!=d_match.end() ){
            Node nv = getCurrentValue( n );
            if( !p->areMatchDisequal( nv, itm->second ) ){
              Debug("qcf-match-debug") << "  -> fail, conflicting disequality" << std::endl;
              return -1;
            }
          }
          d_curr_var_deq[v][n] = v;
          Debug("qcf-match-debug") << "  -> success" << std::endl;
          return 1;
        }else{
          Debug("qcf-match-debug") << "  -> redundant disequality" << std::endl;
          return 0;
        }
      }
    }
  }
}

bool QuantConflictFind::QuantInfo::setMatch( QuantConflictFind * p, int v, Node n ) {
  if( getCurrentCanBeEqual( p, v, n ) ){
    Debug("qcf-match-debug") << "-- bind : " << v << " -> " << n << ", checked " <<  d_curr_var_deq[v].size() << " disequalities" << std::endl;
    d_match[v] = n;
    return true;
  }else{
    return false;
  }
}

bool QuantConflictFind::QuantInfo::isMatchSpurious( QuantConflictFind * p ) {
  for( int i=0; i<getNumVars(); i++ ){
    std::map< int, Node >::iterator it = d_match.find( i );
    if( it!=d_match.end() ){
      if( !getCurrentCanBeEqual( p, i, it->second ) ){
        return true;
      }
    }
  }
  return false;
}

bool QuantConflictFind::QuantInfo::completeMatch( QuantConflictFind * p, Node q, std::vector< int >& assigned ) {
  //assign values for variables that were unassigned (usually not necessary, but handles corner cases)
  Trace("qcf-check") << std::endl;
  std::vector< int > unassigned[2];
  std::vector< TypeNode > unassigned_tn[2];
  for( int i=0; i<getNumVars(); i++ ){
    if( d_match.find( i )==d_match.end() ){
      //Assert( i<(int)q[0].getNumChildren() );
      int rindex = d_var_mg.find( i )==d_var_mg.end() ? 1 : 0;
      unassigned[rindex].push_back( i );
      unassigned_tn[rindex].push_back( getVar( i ).getType() );
      assigned.push_back( i );
    }
  }
  bool success = true;
  for( unsigned r=0; r<2; r++ ){
    if( success && !unassigned[r].empty() ){
      Trace("qcf-check") << "Assign to unassigned, rep = " << r << "..." << std::endl;
      int index = 0;
      std::vector< int > eqc_count;
      do {
        bool invalidMatch;
        while( ( index>=0 && (int)index<(int)unassigned[r].size() ) || invalidMatch ){
          invalidMatch = false;
          if( index==(int)eqc_count.size() ){
            //check if it has now been assigned
            if( r==0 ){
              d_var_mg[ unassigned[r][index] ]->reset( p, true, q );
            }
            eqc_count.push_back( 0 );
          }else{
            if( r==0 ){
              if( d_var_mg[unassigned[r][index]]->getNextMatch( p, q ) ){
                Trace("qcf-check-unassign") << "Succeeded match with mg" << std::endl;
                index++;
              }else{
                Trace("qcf-check-unassign") << "Failed match with mg" << std::endl;
                eqc_count.pop_back();
                index--;
              }
            }else{
              Assert( index==(int)eqc_count.size()-1 );
              if( eqc_count[index]<(int)p->d_eqcs[unassigned_tn[r][index]].size() ){
                int currIndex = eqc_count[index];
                eqc_count[index]++;
                Trace("qcf-check-unassign") << unassigned[r][index] << "->" << p->d_eqcs[unassigned_tn[r][index]][currIndex] << std::endl;
                if( setMatch( p, unassigned[r][index], p->d_eqcs[unassigned_tn[r][index]][currIndex] ) ){
                  Trace("qcf-check-unassign") << "Succeeded match" << std::endl;
                  index++;
                }else{
                  Trace("qcf-check-unassign") << "Failed match" << std::endl;
                  invalidMatch = true;
                }
              }else{
                Trace("qcf-check-unassign") << "No more matches" << std::endl;
                eqc_count.pop_back();
                index--;
              }
            }
          }
        }
        success = index>=0;
        if( success ){
          index = (int)unassigned[r].size()-1;
          Trace("qcf-check-unassign") << "  Try: " << std::endl;
          for( unsigned i=0; i<unassigned[r].size(); i++ ){
            int ui = unassigned[r][i];
            Trace("qcf-check-unassign") << "  Assigned #" << ui << " : " << d_vars[ui] << " -> " << d_match[ui] << std::endl;
          }
        }
      }while( success && isMatchSpurious( p ) );
    }
  }
  if( success ){
    return true;
  }else{
    for( unsigned i=0; i<assigned.size(); i++ ){
      d_match.erase( assigned[i] );
    }
    assigned.clear();
    return false;
  }
}

void QuantConflictFind::QuantInfo::debugPrintMatch( const char * c ) {
  for( int i=0; i<getNumVars(); i++ ){
    Trace(c) << "  " << d_vars[i] << " -> ";
    if( d_match.find( i )!=d_match.end() ){
      Trace(c) << d_match[i];
    }else{
      Trace(c) << "(unassigned) ";
    }
    if( !d_curr_var_deq[i].empty() ){
      Trace(c) << ", DEQ{ ";
      for( std::map< Node, int >::iterator it = d_curr_var_deq[i].begin(); it != d_curr_var_deq[i].end(); ++it ){
        Trace(c) << it->first << " ";
      }
      Trace(c) << "}";
    }
    Trace(c) << std::endl;
  }
}

/*
struct MatchGenSort {
  QuantConflictFind::MatchGen * d_mg;
  bool operator() (int i,int j) {
    return d_mg->d_children[i].d_type<d_mg->d_children[j].d_type;
  }
};
*/

QuantConflictFind::MatchGen::MatchGen( QuantConflictFind * p, Node q, Node n, bool isTop, bool isVar ){
  Trace("qcf-qregister-debug") << "Make match gen for " << n << ", top/var = " << isTop << " " << isVar << std::endl;
  std::vector< Node > qni_apps;
  d_qni_size = 0;
  if( isVar ){
    Assert( p->d_qinfo[q].d_var_num.find( n )!=p->d_qinfo[q].d_var_num.end() );
    if( p->isHandledUfTerm( n ) ){
      d_type = typ_var;
      //d_type_not = true;  //implicit disequality, in disjunction at top level
      d_type_not = false;
      d_n = n;
      qni_apps.push_back( n );
    }else{
      //for now, unknown term
      d_type = typ_invalid;
    }
  }else{
    if( quantifiers::TermDb::hasBoundVarAttr( n ) ){
      //we handle not immediately
      d_n = n.getKind()==NOT ? n[0] : n;
      d_type_not = n.getKind()==NOT;
      if( d_n.getKind()==OR || d_n.getKind()==AND || d_n.getKind()==IFF || d_n.getKind()==ITE ){
        //non-literals
        d_type = typ_valid;
        for( unsigned i=0; i<d_n.getNumChildren(); i++ ){
          d_children.push_back( MatchGen( p, q, d_n[i] ) );
          if( d_children[d_children.size()-1].d_type==typ_invalid ){
            setInvalid();
            break;
          }else if( isTop && n.getKind()==OR && d_children[d_children.size()-1].d_type==typ_var_eq ){
            Trace("qcf-qregister-debug") << "Remove child, make built-in constraint" << std::endl;
            //if variable equality/disequality at top level, remove immediately
            bool cIsNot = d_children[d_children.size()-1].d_type_not;
            Node cn = d_children[d_children.size()-1].d_n;
            Assert( cn.getKind()==EQUAL );
            Assert( p->d_qinfo[q].isVar( cn[0] ) || p->d_qinfo[q].isVar( cn[1] ) );
            //make it a built-in constraint instead
            for( unsigned i=0; i<2; i++ ){
              if( p->d_qinfo[q].isVar( cn[i] ) ){
                int v = p->d_qinfo[q].getVarNum( cn[i] );
                Node cno = cn[i==0 ? 1 : 0];
                p->d_qinfo[q].d_var_constraint[ cIsNot ? 0 : 1 ][v].push_back( cno );
                break;
              }
            }
            d_children.pop_back();
          }
        }
      }else{
        d_type = typ_invalid;
        //literals
        if( d_n.getKind()==APPLY_UF || d_n.getKind()==EQUAL ){
          //get the applications (in order) that will be matching
          p->getEqRegistryApps( d_n, qni_apps );
          bool isValid = true;
          if( qni_apps.size()>0 ){
            for( unsigned i=0; i<qni_apps.size(); i++ ){
              if( !p->isHandledUfTerm( qni_apps[i] ) ){
                //for now, cannot handle anything besides uf
                isValid = false;
                qni_apps.clear();
                break;
              }
            }
            if( isValid ){
              d_type = typ_valid_lit;
            }
          }else if( d_n.getKind()==EQUAL ){
            for( unsigned i=0; i<2; i++ ){
              if( quantifiers::TermDb::hasBoundVarAttr( d_n[i] ) && !p->d_qinfo[q].isVar( d_n[i] ) ){
                isValid = false;
                break;
              }
            }
            if( isValid ){
              Assert( p->d_qinfo[q].isVar( d_n[0] ) || p->d_qinfo[q].isVar( d_n[1] ) );
              // variable equality
              d_type = typ_var_eq;
            }
          }
        }
      }
    }else{
      //we will just evaluate
      d_n = n;
      d_type = typ_ground;
    }
    //if( d_type!=typ_invalid ){
      //determine an efficient children ordering
      //if( !d_children.empty() ){
        //for( unsigned i=0; i<d_children.size(); i++ ){
        //  d_children_order.push_back( i );
        //}
        //if( !d_n.isNull() && ( d_n.getKind()==OR || d_n.getKind()==AND || d_n.getKind()==IFF ) ){
          //sort based on the type of the constraint : ground comes first, then literals, then others
          //MatchGenSort mgs;
          //mgs.d_mg = this;
          //std::sort( d_children_order.begin(), d_children_order.end(), mgs );
        //}
      //}
    //}
  }
  if( d_type!=typ_invalid ){
    if( !qni_apps.empty() ){
      Trace("qcf-qregister-debug") << "Initialize matching..." << std::endl;
      for( unsigned i=0; i<qni_apps.size(); i++ ){
        for( unsigned j=0; j<qni_apps[i].getNumChildren(); j++ ){
          Node nn = qni_apps[i][j];
          Trace("qcf-qregister-debug") << "  " << d_qni_size;
          if( p->d_qinfo[q].isVar( nn ) ){
            Trace("qcf-qregister-debug") << " is var #" << p->d_qinfo[q].d_var_num[nn] << std::endl;
            d_qni_var_num[d_qni_size] = p->d_qinfo[q].d_var_num[nn];
          }else{
            Trace("qcf-qregister-debug") << " is gterm " << nn << std::endl;
            d_qni_gterm[d_qni_size] = nn;
          }
          d_qni_size++;
        }
      }
    }
  }
  Trace("qcf-qregister-debug")  << "Done make match gen " << n << ", type = ";
  debugPrintType( "qcf-qregister-debug", d_type, true );
  Trace("qcf-qregister-debug") << std::endl;
  //Assert( d_children.size()==d_children_order.size() );
}

void QuantConflictFind::MatchGen::reset_round( QuantConflictFind * p ) {
  for( std::map< int, Node >::iterator it = d_qni_gterm.begin(); it != d_qni_gterm.end(); ++it ){
    d_qni_gterm_rep[it->first] = p->getRepresentative( it->second );
  }
  for( unsigned i=0; i<d_children.size(); i++ ){
    d_children[i].reset_round( p );
  }
}

void QuantConflictFind::MatchGen::reset( QuantConflictFind * p, bool tgt, Node q ) {
  d_tgt = d_type_not ? !tgt : tgt;
  Debug("qcf-match") << "     Reset for : " << d_n << ", type : ";
  debugPrintType( "qcf-match", d_type );
  Debug("qcf-match") << ", tgt = " << d_tgt << ", children = " << d_children.size() << std::endl;
  d_qn.clear();
  d_qni.clear();
  d_qni_bound.clear();
  d_child_counter = -1;

  //set up processing matches
  if( d_type==typ_ground ){
    if( p->evaluate( d_n, d_tgt, true )==( d_tgt ? 1 : -1 ) ){
      //store dummy variable
      d_qn.push_back( NULL );
    }
  }else if( d_type==typ_var ){
    //check if variable is bound by now
    int vi = p->d_qinfo[q].getVarNum( d_n );
    Assert( vi!=-1 );
    int repVar = p->d_qinfo[q].getCurrentRepVar( vi );
    Assert( p->isHandledUfTerm( d_n ) );
    Node f = d_n.getOperator();
    std::map< int, Node >::iterator it = p->d_qinfo[q].d_match.find( repVar );
    if( it!=p->d_qinfo[q].d_match.end() && d_tgt ) {
      Debug("qcf-match") << "       will be matching var within eqc = " << it->second << std::endl;
      //f-applications in the equivalence class in match[ repVar ]
      QcfNodeIndex * qni = p->getQcfNodeIndex( it->second, f );
      if( qni ){
        d_qn.push_back( qni );
      }
    }else{
      Debug("qcf-match") << "       will be matching var within any eqc." << std::endl;
      //we are binding rep var
      d_qni_bound_cons[repVar] = Node::null();
      //must look at all f-applications
      QcfNodeIndex * qni = p->getQcfNodeIndex( f );
      if( qni ){
        d_qn.push_back( qni );
      }
    }
  }else if( d_type==typ_var_eq ){
    bool success = false;
    for( unsigned i=0; i<2; i++ ){
      int var = p->d_qinfo[q].getVarNum( d_n[i] );
      if( var!=-1 ){
        int repVar = p->d_qinfo[q].getCurrentRepVar( var );
        Node o = d_n[ i==0 ? 1 : 0 ];
        o = p->d_qinfo[q].getCurrentValue( o );
        int vo = p->d_qinfo[q].getCurrentRepVar( p->d_qinfo[q].getVarNum( o ) );
        int addCons = p->d_qinfo[q].addConstraint( p, repVar, o, vo, d_tgt, false );
        success = addCons!=-1;
        //if successful and non-redundant, store that we need to cleanup this
        if( addCons==1 ){
          d_qni_bound_cons[repVar] = o;
          d_qni_bound[repVar] = vo;
        }
        break;
      }
    }
    if( success ){
      //store dummy
      d_qn.push_back( NULL );
    }
  }else if( d_type==typ_valid_lit ){
    //literal
    EqRegistry * er = p->getEqRegistry( d_tgt, d_n, false );
    Assert( er );
    d_qn.push_back( &(er->d_qni) );
  }else{
    if( d_children.empty() ){
      //add dummy
      d_qn.push_back( NULL );
    }else{
      //reset the first child to d_tgt
      d_child_counter = 0;
      getChild( d_child_counter )->reset( p, d_tgt, q );
    }
  }
  Debug("qcf-match") << "     Finished reset for " << d_n << ", success = " << ( !d_qn.empty() || d_child_counter!=-1 ) << std::endl;
}

bool QuantConflictFind::MatchGen::getNextMatch( QuantConflictFind * p, Node q ) {
  Debug("qcf-match") << "     Get next match for : " << d_n << ", type = ";
  debugPrintType( "qcf-match", d_type );
  Debug("qcf-match") << ", children = " << d_children.size() << std::endl;
  if( d_children.empty() ){
    bool success = doMatching( p, q );
    if( success ){
      Debug("qcf-match") << "     Produce matches for bound variables..." << std::endl;

      //also need to create match for each variable we bound
      std::map< int, int >::iterator it = d_qni_bound.begin();
      bool doReset = true;
      while( success && it!=d_qni_bound.end() ){
        std::map< int, MatchGen * >::iterator itm = p->d_qinfo[q].d_var_mg.find( it->second );
        if( itm!=p->d_qinfo[q].d_var_mg.end() ){
          Debug("qcf-match-debug") << "       process variable " << it->second << ", reset = " << doReset << std::endl;
          if( doReset ){
            itm->second->reset( p, true, q );
          }
          if( !itm->second->getNextMatch( p, q ) ){
            do {
              if( it==d_qni_bound.begin() ){
                Debug("qcf-match-debug") << "       failed." << std::endl;
                success = false;
              }else{
                Debug("qcf-match-debug") << "       decrement..." << std::endl;
                --it;
              }
            }while( success && p->d_qinfo[q].d_var_mg.find( it->second )==p->d_qinfo[q].d_var_mg.end() );
            doReset = false;
          }else{
            Debug("qcf-match-debug") << "       increment..." << std::endl;
            ++it;
            doReset = true;
          }
        }else{
          Debug("qcf-match-debug") << "       skip..." << std::endl;
          ++it;
          doReset = true;
        }
      }
    }
    //if not successful, clean up the variables you bound
    if( !success ){
      for( std::map< int, Node >::iterator it = d_qni_bound_cons.begin(); it != d_qni_bound_cons.end(); ++it ){
        if( !it->second.isNull() ){
          Debug("qcf-match") << "       Clean up bound var " << it->first << (d_tgt ? "!" : "") << " = " << it->second << std::endl;
          std::map< int, int >::iterator itb = d_qni_bound.find( it->first );
          int vn = itb!=d_qni_bound.end() ? itb->second : -1;
          p->d_qinfo[q].addConstraint( p, it->first, it->second, vn, d_tgt, true );
          if( vn!=-1 ){
            d_qni_bound.erase( vn );
          }
        }
      }
      d_qni_bound_cons.clear();
      //clean up the match : remove equalities/disequalities
      for( std::map< int, int >::iterator it = d_qni_bound.begin(); it != d_qni_bound.end(); ++it ){
        Debug("qcf-match") << "       Clean up bound var " << it->second << std::endl;
        Assert( it->second<p->d_qinfo[q].getNumVars() );
        p->d_qinfo[q].d_match.erase( it->second );
      }
      d_qni_bound.clear();
    }
    Debug("qcf-match") << "    ...finished matching for " << d_n << ", success = " << success << std::endl;
    return success;
  }else{
    if( d_child_counter!=-1 ){
      bool success = false;
      while( !success && d_child_counter>=0 ){
        //transition system based on d_child_counter
        if( d_type==typ_top || d_n.getKind()==OR || d_n.getKind()==AND ){
          if( (d_n.getKind()==AND)==d_tgt ){
            //all children must match simultaneously
            if( getChild( d_child_counter )->getNextMatch( p, q ) ){
              if( d_child_counter<(int)(getNumChildren()-1) ){
                d_child_counter++;
                Debug("qcf-match-debug") << "       Reset child " << d_child_counter << " of " << d_n << std::endl;
                getChild( d_child_counter )->reset( p, d_tgt, q );
              }else{
                success = true;
              }
            }else{
              d_child_counter--;
            }
          }else{
            //one child must match
            if( !getChild( d_child_counter )->getNextMatch( p, q ) ){
              if( d_child_counter<(int)(getNumChildren()-1) ){
                d_child_counter++;
                Debug("qcf-match-debug") << "       Reset child " << d_child_counter << " of " << d_n << ", one match" << std::endl;
                getChild( d_child_counter )->reset( p, d_tgt, q );
              }else{
                d_child_counter = -1;
              }
            }else{
              success = true;
            }
          }
        }else if( d_n.getKind()==IFF ){
          //construct match based on both children
          if( d_child_counter%2==0 ){
            if( getChild( 0 )->getNextMatch( p, q ) ){
              d_child_counter++;
              getChild( 1 )->reset( p, d_child_counter==1, q );
            }else{
              if( d_child_counter==0 ){
                d_child_counter = 2;
                getChild( 0 )->reset( p, !d_tgt, q );
              }else{
                d_child_counter = -1;
              }
            }
          }
          if( d_child_counter%2==1 ){
            if( getChild( 1 )->getNextMatch( p, q ) ){
              success = true;
            }else{
              d_child_counter--;
            }
          }
        }else if( d_n.getKind()==ITE ){
          if( d_child_counter%2==0 ){
            int index1 = d_child_counter==4 ? 1 : 0;
            if( getChild( index1 )->getNextMatch( p, q ) ){
              d_child_counter++;
              getChild( d_child_counter==5 ? 2 : (d_tgt==(d_child_counter==0) ? 1 : 2) )->reset( p, d_tgt, q );
            }else{
              if( d_child_counter==4 ){
                d_child_counter = -1;
              }else{
                d_child_counter +=2;
                getChild( d_child_counter==4 ? 1 : 0 )->reset( p, d_child_counter==2 ? !d_tgt : d_tgt, q );
              }
            }
          }
          if( d_child_counter%2==1 ){
            int index2 = d_child_counter==5 ? 2 : (d_tgt==(d_child_counter==0) ? 1 : 2);
            if( getChild( index2 )->getNextMatch( p, q ) ){
              success = true;
            }else{
              d_child_counter--;
            }
          }
        }
      }
      Debug("qcf-match") << "    ...finished construct match for " << d_n << ", success = " << success << std::endl;
      return success;
    }
  }
  Debug("qcf-match") << "    ...already finished for " << d_n << std::endl;
  return false;
}

bool QuantConflictFind::MatchGen::doMatching( QuantConflictFind * p, Node q ) {
  if( !d_qn.empty() ){
    if( d_qn[0]==NULL ){
      d_qn.clear();
      return true;
    }else{
      Assert( d_qni_size>0 );
      bool invalidMatch;
      do {
        invalidMatch = false;
        Debug("qcf-match-debug") << "       Do matching " << d_qn.size() << " " << d_qni.size() << std::endl;
        if( d_qn.size()==d_qni.size()+1 ) {
          int index = (int)d_qni.size();
          //initialize
          Node val;
          std::map< int, int >::iterator itv = d_qni_var_num.find( index );
          if( itv!=d_qni_var_num.end() ){
            //get the representative variable this variable is equal to
            int repVar = p->d_qinfo[q].getCurrentRepVar( itv->second );
            Debug("qcf-match-debug") << "       Match " << index << " is a variable " << itv->second << ", which is repVar " << repVar << std::endl;
            //get the value the rep variable
            std::map< int, Node >::iterator itm = p->d_qinfo[q].d_match.find( repVar );
            if( itm!=p->d_qinfo[q].d_match.end() ){
              val = itm->second;
              Assert( !val.isNull() );
              Debug("qcf-match-debug") << "       Variable is already bound to " << val << std::endl;
            }else{
              //binding a variable
              d_qni_bound[index] = repVar;
              std::map< TNode, QcfNodeIndex >::iterator it = d_qn[index]->d_children.begin();
              if( it != d_qn[index]->d_children.end() ) {
                d_qni.push_back( it );
                //set the match
                if( p->d_qinfo[q].setMatch( p, d_qni_bound[index], it->first ) ){
                  Debug("qcf-match-debug") << "       Binding variable" << std::endl;
                  if( d_qn.size()<d_qni_size ){
                    d_qn.push_back( &it->second );
                  }
                }else{
                  Debug("qcf-match") << "       Binding variable, currently fail." << std::endl;
                  invalidMatch = true;
                }
              }else{
                Debug("qcf-match-debug") << "       Binding variable, fail, no more variables to bind" << std::endl;
                d_qn.pop_back();
              }
            }
          }else{
            Debug("qcf-match-debug") << "       Match " << index << " is ground term" << std::endl;
            Assert( d_qni_gterm.find( index )!=d_qni_gterm.end() );
            Assert( d_qni_gterm_rep.find( index )!=d_qni_gterm_rep.end() );
            val = d_qni_gterm_rep[index];
            Assert( !val.isNull() );
          }
          if( !val.isNull() ){
            //constrained by val
            std::map< TNode, QcfNodeIndex >::iterator it = d_qn[index]->d_children.find( val );
            if( it!=d_qn[index]->d_children.end() ){
              Debug("qcf-match-debug") << "       Match" << std::endl;
              d_qni.push_back( it );
              if( d_qn.size()<d_qni_size ){
                d_qn.push_back( &it->second );
              }
            }else{
              Debug("qcf-match-debug") << "       Failed to match" << std::endl;
              d_qn.pop_back();
            }
            //TODO : if it is equal to something else, also try that
          }
        }else{
          Assert( d_qn.size()==d_qni.size() );
          int index = d_qni.size()-1;
          //increment if binding this variable
          bool success = false;
          std::map< int, int >::iterator itb = d_qni_bound.find( index );
          if( itb!=d_qni_bound.end() ){
            d_qni[index]++;
            if( d_qni[index]!=d_qn[index]->d_children.end() ){
              success = true;
              if( p->d_qinfo[q].setMatch( p, itb->second, d_qni[index]->first ) ){
                Debug("qcf-match-debug") << "       Bind next variable" << std::endl;
                if( d_qn.size()<d_qni_size ){
                  d_qn.push_back( &d_qni[index]->second );
                }
              }else{
                Debug("qcf-match-debug") << "       Bind next variable, currently fail" << std::endl;
                invalidMatch = true;
              }
            }else{
              Debug("qcf-match-debug") << "       Bind next variable, no more variables to bind" << std::endl;
            }
          }else{
            //TODO : if it equal to something else, also try that
          }
          //if not incrementing, move to next
          if( !success ){
            d_qn.pop_back();
            d_qni.pop_back();
          }
        }
        if( d_type==typ_var ){
          if( !invalidMatch && d_qni.size()==d_qni_size ){
            //if in the act of binding the variable by this term, bind the variable
            std::map< int, Node >::iterator itb = d_qni_bound_cons.begin();
            if( itb!=d_qni_bound_cons.end() ){
              QcfNodeIndex * v_qni = &d_qni[d_qni.size()-1]->second;
              Assert( v_qni->d_children.begin()!=v_qni->d_children.end() );
              Node vb = v_qni->d_children.begin()->first;
              Assert( !vb.isNull() );
              vb = p->getRepresentative( vb );
              Debug("qcf-match-debug") << "       For var, require binding " << itb->first << " to " << vb << ", d_tgt = " << d_tgt << std::endl;
              if( !itb->second.isNull() ){
                p->d_qinfo[q].addConstraint( p, itb->first, itb->second, -1, d_tgt, true );
              }
              int addCons = p->d_qinfo[q].addConstraint( p, itb->first, vb, -1, d_tgt, false );
              if( addCons==-1 ){
                Debug("qcf-match-debug") << "       Failed set for var." << std::endl;
                invalidMatch = true;
                d_qni_bound_cons[itb->first] = Node::null();
              }else{
                Debug("qcf-match-debug") << "       Succeeded set for var." << std::endl;
                if( addCons==1 ){
                  d_qni_bound_cons[itb->first] = vb;
                }
              }
            }
          }
        }
      }while( ( !d_qn.empty() && d_qni.size()!=d_qni_size ) || invalidMatch );
    }
  }
  return !d_qn.empty();
}

void QuantConflictFind::MatchGen::debugPrintType( const char * c, short typ, bool isTrace ) {
  if( isTrace ){
    switch( typ ){
    case typ_invalid: Trace(c) << "invalid";break;
    case typ_ground: Trace(c) << "ground";break;
    case typ_valid_lit: Trace(c) << "valid_lit";break;
    case typ_valid: Trace(c) << "valid";break;
    case typ_var: Trace(c) << "var";break;
    case typ_var_eq: Trace(c) << "var_eq";break;
    case typ_top: Trace(c) << "top";break;
    }
  }else{
    switch( typ ){
    case typ_invalid: Debug(c) << "invalid";break;
    case typ_ground: Debug(c) << "ground";break;
    case typ_valid_lit: Debug(c) << "valid_lit";break;
    case typ_valid: Debug(c) << "valid";break;
    case typ_var: Debug(c) << "var";break;
    case typ_var_eq: Debug(c) << "var_eq";break;
    case typ_top: Debug(c) << "top";break;
    }
  }
}

void QuantConflictFind::MatchGen::setInvalid() {
  d_type = typ_invalid;
  d_children.clear();
}


//-------------------------------------------------- debugging


void QuantConflictFind::debugPrint( const char * c ) {
  //print the equivalance classes
  Trace(c) << "----------EQ classes" << std::endl;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( getEqualityEngine() );
  while( !eqcs_i.isFinished() ){
    Node n = (*eqcs_i);
    if( !n.getType().isInteger() ){
      Trace(c) << "  - " << n << " : {";
      eq::EqClassIterator eqc_i = eq::EqClassIterator( n, getEqualityEngine() );
      bool pr = false;
      while( !eqc_i.isFinished() ){
        Node nn = (*eqc_i);
        if( nn.getKind()!=EQUAL && nn!=n ){
          Trace(c) << (pr ? "," : "" ) << " " << nn;
          pr = true;
        }
        ++eqc_i;
      }
      Trace(c) << (pr ? " " : "" ) << "}" << std::endl;
      EqcInfo * eqcn = getEqcInfo( n, false );
      if( eqcn ){
        Trace(c) << "    DEQ : {";
        pr = false;
        for( NodeBoolMap::iterator it = eqcn->d_diseq.begin(); it != eqcn->d_diseq.end(); ++it ){
          if( (*it).second ){
            Trace(c) << (pr ? "," : "" ) << " " << (*it).first;
            pr = true;
          }
        }
        Trace(c) << (pr ? " " : "" ) << "}" << std::endl;
      }
    }
    ++eqcs_i;
  }
  std::map< Node, std::map< Node, bool > > printed;
  //print the equality registries
  for( unsigned i=0; i<2; i++ ){
    printed.clear();
    Trace(c) << "----------EQR, polarity = " << (i==0) << std::endl;
    for( unsigned j=0; j<2; j++ ){
      for( std::map< TNode, std::map< int, std::map< TNode, EqRegistry * > > >::iterator it = d_eqr[i][j].begin(); it != d_eqr[i][j].end(); ++it ){
        bool prHead = false;
        for( unsigned jj=0; jj<2; jj++ ){
          for( std::map< TNode, EqRegistry * >::iterator it2 = it->second[jj].begin(); it2 != it->second[jj].end(); ++it2 ){
            bool print;
            if( isHandledUfTerm( it->first ) && isHandledUfTerm( it2->first ) &&
                it->first.getOperator()!=it2->first.getOperator() ){
              print = isLessThan( it->first.getOperator(), it2->first.getOperator() );
            }else{
              print = printed[it->first].find( it2->first )==printed[it->first].end();
            }
            if( print ){
              printed[it->first][it2->first] = true;
              printed[it2->first][it->first] = true;
              if( !prHead ){
                Trace(c) << "- " << it->first << std::endl;
                prHead = true;
              }
              Trace(c) << "    " << it2->first << ", terms : " << std::endl;

              /*
              Trace(c) << "    " << it2->first << " : {";
              bool pr = false;
              for( NodeBoolMap::iterator it3 = it2->second->d_t_eqc.begin(); it3 != it2->second->d_t_eqc.end(); ++it3 ){
                if( (*it3).second ){
                  Trace(c) << (pr ? "," : "" ) << " " << (*it3).first;
                  pr = true;
                }
              }
              Trace(c) << (pr ? " " : "" ) << "}" << std::endl;
              */
              //print qni structure
              it2->second->debugPrint( c, 3 );
            }
          }
        }
      }
    }
  }
}

void QuantConflictFind::debugPrintQuant( const char * c, Node q ) {
  Trace(c) << "Q" << d_quant_id[q];
}

void QuantConflictFind::debugPrintQuantBody( const char * c, Node q, Node n, bool doVarNum ) {
  if( n.getNumChildren()==0 ){
    Trace(c) << n;
  }else if( doVarNum && d_qinfo[q].d_var_num.find( n )!=d_qinfo[q].d_var_num.end() ){
    Trace(c) << "?x" << d_qinfo[q].d_var_num[n];
  }else{
    Trace(c) << "(";
    if( n.getKind()==APPLY_UF ){
      Trace(c) << n.getOperator();
    }else{
      Trace(c) << n.getKind();
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      Trace(c) << " ";
      debugPrintQuantBody( c, q, n[i] );
    }
    Trace(c) << ")";
  }
}

QuantConflictFind::Statistics::Statistics():
  d_inst_rounds("QuantConflictFind::Inst_Rounds", 0),
  d_conflict_inst("QuantConflictFind::Instantiations_Conflict_Find", 0 ),
  d_prop_inst("QuantConflictFind::Instantiations_Prop", 0 )
{
  StatisticsRegistry::registerStat(&d_inst_rounds);
  StatisticsRegistry::registerStat(&d_conflict_inst);
  StatisticsRegistry::registerStat(&d_prop_inst);
}

QuantConflictFind::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_inst_rounds);
  StatisticsRegistry::unregisterStat(&d_conflict_inst);
  StatisticsRegistry::unregisterStat(&d_prop_inst);
}

}