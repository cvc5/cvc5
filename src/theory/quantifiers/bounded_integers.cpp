/*********************                                                        */
/*! \file bounded_integers.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bounded integers module
 **
 ** This class manages integer bounds for quantifiers
 **/

#include "theory/quantifiers/bounded_integers.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/model_engine.h"

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;

void BoundedIntegers::RangeModel::initialize() {
  //add initial split lemma
  Node ltr = NodeManager::currentNM()->mkNode( LT, d_range, NodeManager::currentNM()->mkConst( Rational(0) ) );
  ltr = Rewriter::rewrite( ltr );
  Trace("bound-int-lemma") << " *** bound int: initial split on " << ltr << std::endl;
  d_bi->getQuantifiersEngine()->getOutputChannel().split( ltr );
  Node ltr_lit = ltr.getKind()==NOT ? ltr[0] : ltr;
  d_range_literal[-1] = ltr_lit;
  d_lit_to_range[ltr_lit] = -1;
  d_lit_to_pol[ltr_lit] = ltr.getKind()!=NOT;
  //register with bounded integers
  Trace("bound-int-debug") << "Literal " << ltr_lit << " is literal for " << d_range << std::endl;
  d_bi->addLiteralFromRange(ltr_lit, d_range);
}

void BoundedIntegers::RangeModel::assertNode(Node n) {
  bool pol = n.getKind()!=NOT;
  Node nlit = n.getKind()==NOT ? n[0] : n;
  if( d_lit_to_range.find( nlit )!=d_lit_to_range.end() ){
    Trace("bound-int-assert") << "With polarity = " << pol << " (req "<< d_lit_to_pol[nlit] << ")";
    Trace("bound-int-assert") << ", found literal " << nlit;
    Trace("bound-int-assert") << ", it is bound literal " << d_lit_to_range[nlit] << " for " << d_range << std::endl;
    d_range_assertions[nlit] = (pol==d_lit_to_pol[nlit]);
    if( pol!=d_lit_to_pol[nlit] ){
      //check if we need a new split?
      if( !d_has_range ){
        bool needsRange = true;
        for( std::map< Node, int >::iterator it = d_lit_to_range.begin(); it != d_lit_to_range.end(); ++it ){
          if( d_range_assertions.find( it->first )==d_range_assertions.end() ){
            needsRange = false;
            break;
          }
        }
        if( needsRange ){
          allocateRange();
        }
      }
    }else{
      if (!d_has_range || d_lit_to_range[nlit]<d_curr_range ){
        Trace("bound-int-bound") << "Successfully bound " << d_range << " to " << d_lit_to_range[nlit] << std::endl;
        d_curr_range = d_lit_to_range[nlit];
      }
      //set the range
      d_has_range = true;
    }
  }else{
    Message() << "Could not find literal " << nlit << " for range " << d_range << std::endl;
    exit(0);
  }
}

void BoundedIntegers::RangeModel::allocateRange() {
  d_curr_max++;
  int newBound = d_curr_max;
  Trace("bound-int-proc") << "Allocate range bound " << newBound << " for " << d_range << std::endl;
  //TODO: newBound should be chosen in a smarter way
  Node ltr = NodeManager::currentNM()->mkNode( LEQ, d_range, NodeManager::currentNM()->mkConst( Rational(newBound) ) );
  ltr = Rewriter::rewrite( ltr );
  Trace("bound-int-lemma") << " *** bound int: split on " << ltr << std::endl;
  d_bi->getQuantifiersEngine()->getOutputChannel().split( ltr );
  Node ltr_lit = ltr.getKind()==NOT ? ltr[0] : ltr;
  d_range_literal[newBound] = ltr_lit;
  d_lit_to_range[ltr_lit] = newBound;
  d_lit_to_pol[ltr_lit] = ltr.getKind()!=NOT;
  //register with bounded integers
  d_bi->addLiteralFromRange(ltr_lit, d_range);
}

Node BoundedIntegers::RangeModel::getNextDecisionRequest() {
  //request the current cardinality as a decision literal, if not already asserted
  for( std::map< Node, int >::iterator it = d_lit_to_range.begin(); it != d_lit_to_range.end(); ++it ){
    int i = it->second;
    if( !d_has_range || i<d_curr_range ){
      Node rn = it->first;
      Assert( !rn.isNull() );
      if( d_range_assertions.find( rn )==d_range_assertions.end() ){
        if (!d_lit_to_pol[it->first]) {
          rn = rn.negate();
        }
        Trace("bound-int-dec") << "For " << d_range << ", make decision " << rn << " to make range " << i << std::endl;
        return rn;
      }
    }
  }
  return Node::null();
}


BoundedIntegers::BoundedIntegers(context::Context* c, QuantifiersEngine* qe) :
QuantifiersModule(qe), d_assertions(c){

}

bool BoundedIntegers::isBound( Node f, Node v ) {
  return std::find( d_set[f].begin(), d_set[f].end(), v )!=d_set[f].end();
}

bool BoundedIntegers::hasNonBoundVar( Node f, Node b ) {
  if( b.getKind()==BOUND_VARIABLE ){
    if( !isBound( f, b ) ){
      return true;
    }
  }else{
    for( unsigned i=0; i<b.getNumChildren(); i++ ){
      if( hasNonBoundVar( f, b[i] ) ){
        return true;
      }
    }
  }
  return false;
}

void BoundedIntegers::processLiteral( Node f, Node lit, bool pol,
                                      std::map< int, std::map< Node, Node > >& bound_lit_map,
                                      std::map< int, std::map< Node, bool > >& bound_lit_pol_map ) {
  if( lit.getKind()==GEQ && lit[0].getType().isInteger() ){
    std::map< Node, Node > msum;
    if (QuantArith::getMonomialSumLit( lit, msum )){
      Trace("bound-int-debug") << "Literal (polarity = " << pol << ") " << lit << " is monomial sum : " << std::endl;
      for(std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
        Trace("bound-int-debug") << "  ";
        if( !it->second.isNull() ){
          Trace("bound-int-debug") << it->second;
          if( !it->first.isNull() ){
            Trace("bound-int-debug") << " * ";
          }
        }
        if( !it->first.isNull() ){
          Trace("bound-int-debug") << it->first;
        }
        Trace("bound-int-debug") << std::endl;
      }
      Trace("bound-int-debug") << std::endl;
      for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
        if ( !it->first.isNull() && it->first.getKind()==BOUND_VARIABLE && !isBound( f, it->first ) ){
          Node veq;
          if( QuantArith::isolate( it->first, msum, veq, GEQ ) ){
            Node n1 = veq[0];
            Node n2 = veq[1];
            if(pol){
              //flip
              n1 = veq[1];
              n2 = veq[0];
              if( n1.getKind()==BOUND_VARIABLE ){
                n2 = QuantArith::offset( n2, 1 );
              }else{
                n1 = QuantArith::offset( n1, -1 );
              }
              veq = NodeManager::currentNM()->mkNode( GEQ, n1, n2 );
            }
            Trace("bound-int-debug") << "Isolated for " << it->first << " : (" << n1 << " >= " << n2 << ")" << std::endl;
            Node t = n1==it->first ? n2 : n1;
            if( !hasNonBoundVar( f, t ) ) {
              Trace("bound-int-debug") << "The bound is relevant." << std::endl;
              int loru = n1==it->first ? 0 : 1;
              d_bounds[loru][f][it->first] = t;
              bound_lit_map[loru][it->first] = lit;
              bound_lit_pol_map[loru][it->first] = pol;
            }else{
              Trace("bound-int-debug") << "The term " << t << " has non-bound variable." << std::endl;
            }
          }
        }
      }
    }
  }else if( lit.getKind()==LEQ || lit.getKind()==LT || lit.getKind()==GT ) {
    Message() << "BoundedIntegers : Bad kind for literal : " << lit << std::endl;
  }
}

void BoundedIntegers::process( Node f, Node n, bool pol,
                               std::map< int, std::map< Node, Node > >& bound_lit_map,
                               std::map< int, std::map< Node, bool > >& bound_lit_pol_map ){
  if( (( n.getKind()==IMPLIES || n.getKind()==OR) && pol) || (n.getKind()==AND && !pol) ){
    for( unsigned i=0; i<n.getNumChildren(); i++) {
      bool newPol = n.getKind()==IMPLIES && i==0 ? !pol : pol;
      process( f, n[i], newPol, bound_lit_map, bound_lit_pol_map );
    }
  }else if( n.getKind()==NOT ){
    process( f, n[0], !pol, bound_lit_map, bound_lit_pol_map );
  }else {
    processLiteral( f, n, pol, bound_lit_map, bound_lit_pol_map );
  }
}

void BoundedIntegers::check( Theory::Effort e ) {

}


void BoundedIntegers::addLiteralFromRange( Node lit, Node r ) {
  d_lit_to_ranges[lit].push_back(r);
  //check if it is already asserted?
  if(d_assertions.find(lit)!=d_assertions.end()){
    d_rms[r]->assertNode( d_assertions[lit] ? lit : lit.negate() );
  }
}

void BoundedIntegers::registerQuantifier( Node f ) {
  Trace("bound-int") << "Register quantifier " << f << std::endl;
  bool hasIntType = false;
  int finiteTypes = 0;
  std::map< Node, int > numMap;
  for( unsigned i=0; i<f[0].getNumChildren(); i++) {
    numMap[f[0][i]] = i;
    if( f[0][i].getType().isInteger() ){
      hasIntType = true;
    }
    else if( f[0][i].getType().isSort() || f[0][i].getType().getCardinality().isFinite() ){
      finiteTypes++;
    }
  }
  if( hasIntType ){
    bool success;
    do{
      std::map< int, std::map< Node, Node > > bound_lit_map;
      std::map< int, std::map< Node, bool > > bound_lit_pol_map;
      success = false;
      process( f, f[1], true, bound_lit_map, bound_lit_pol_map );
      for( std::map< Node, Node >::iterator it = d_bounds[0][f].begin(); it != d_bounds[0][f].end(); ++it ){
        Node v = it->first;
        if( !isBound(f,v) ){
          if( d_bounds[1][f].find(v)!=d_bounds[1][f].end() ){
            d_set[f].push_back(v);
            d_set_nums[f].push_back(numMap[v]);
            success = true;
            //set Attributes on literals
            for( unsigned b=0; b<2; b++ ){
              Assert( bound_lit_map[b].find( v )!=bound_lit_map[b].end() );
              Assert( bound_lit_pol_map[b].find( v )!=bound_lit_pol_map[b].end() );
              BoundIntLitAttribute bila;
              bound_lit_map[b][v].setAttribute( bila, bound_lit_pol_map[b][v] ? 1 : 0 );
            }
            Trace("bound-int") << "Variable " << v << " is bound because of literals " << bound_lit_map[0][v] << " and " << bound_lit_map[1][v] << std::endl;
          }
        }
      }
    }while( success );
    Trace("bound-int") << "Bounds are : " << std::endl;
    for( unsigned i=0; i<d_set[f].size(); i++) {
      Node v = d_set[f][i];
      Node r = NodeManager::currentNM()->mkNode( MINUS, d_bounds[1][f][v], d_bounds[0][f][v] );
      d_range[f][v] = Rewriter::rewrite( r );
      Trace("bound-int") << "  " << d_bounds[0][f][v] << " <= " << v << " <= " << d_bounds[1][f][v] << " (range is " << d_range[f][v] << ")" << std::endl;
    }
    if( d_set[f].size()==(f[0].getNumChildren()-finiteTypes) ){
      d_bound_quants.push_back( f );
      for( unsigned i=0; i<d_set[f].size(); i++) {
        Node v = d_set[f][i];
        Node r = d_range[f][v];
        if( quantifiers::TermDb::hasBoundVarAttr(r) ){
          //introduce a new bound
          Node new_range = NodeManager::currentNM()->mkSkolem( "bir_$$", r.getType(), "bound for term" );
          d_nground_range[f][v] = d_range[f][v];
          d_range[f][v] = new_range;
          r = new_range;
        }
        if( r.getKind()!=CONST_RATIONAL ){
          if( std::find(d_ranges.begin(), d_ranges.end(), r)==d_ranges.end() ){
            Trace("bound-int") << "For " << v << ", bounded Integer Module will try to minimize : " << r << " " << r.getKind() << std::endl;
            d_ranges.push_back( r );
            d_rms[r] = new RangeModel(this, r, d_quantEngine->getSatContext() );
            d_rms[r]->initialize();
          }
        }
      }
    }else{
      Trace("bound-int-warn") << "Warning : Bounded Integers : Could not find bounds for " << f << std::endl;
      //Message() << "Bound integers : Cannot infer bounds of " << f << std::endl;
    }
  }
}

void BoundedIntegers::assertNode( Node n ) {
  Trace("bound-int-assert") << "Assert " << n << std::endl;
  Node nlit = n.getKind()==NOT ? n[0] : n;
  if( d_lit_to_ranges.find(nlit)!=d_lit_to_ranges.end() ){
    Trace("bound-int-assert") << "This is the bounding literal for " << d_lit_to_ranges[nlit].size() << " ranges." << std::endl;
    for( unsigned i=0; i<d_lit_to_ranges[nlit].size(); i++) {
      Node r = d_lit_to_ranges[nlit][i];
      Trace("bound-int-assert") << "  ...this is a bounding literal for " << r << std::endl;
      d_rms[r]->assertNode( n );
    }
  }
  d_assertions[nlit] = n.getKind()!=NOT;
}

Node BoundedIntegers::getNextDecisionRequest() {
  Trace("bound-int-dec") << "bi: Get next decision request?" << std::endl;
  for( unsigned i=0; i<d_ranges.size(); i++) {
    Node d = d_rms[d_ranges[i]]->getNextDecisionRequest();
    if (!d.isNull()) {
      return d;
    }
  }
  return Node::null();
}

void BoundedIntegers::getBounds( Node f, Node v, RepSetIterator * rsi, Node & l, Node & u ) {
  l = d_bounds[0][f][v];
  u = d_bounds[1][f][v];
  if( d_nground_range[f].find(v)!=d_nground_range[f].end() ){
    //must create substitution
    std::vector< Node > vars;
    std::vector< Node > subs;
    Trace("bound-int-rsi") << "Get bound value in model of variable " << v << std::endl;
    for( unsigned i=0; i<d_set[f].size(); i++) {
      if( d_set[f][i]!=v ){
        Trace("bound-int-rsi") << "Look up the value for " << d_set[f][i] << " " << rsi->d_var_order[d_set_nums[f][i]] << std::endl;
        Trace("bound-int-rsi") << "term : " << rsi->getTerm(rsi->d_var_order[d_set_nums[f][i]]) << std::endl;
        vars.push_back(d_set[f][i]);
        subs.push_back(rsi->getTerm(rsi->d_var_order[d_set_nums[f][i]]));
      }else{
        break;
      }
    }
    Trace("bound-int-rsi") << "Do substitution..." << std::endl;
    //check if it has been instantiated
    if (!vars.empty() && !d_bnd_it[f][v].hasInstantiated(subs)){
      //must add the lemma
      Node nn = d_nground_range[f][v];
      nn = nn.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
      Node lem = NodeManager::currentNM()->mkNode( LEQ, nn, d_range[f][v] );
      Trace("bound-int-lemma") << "*** Add lemma to minimize instantiated non-ground term " << lem << std::endl;
      d_quantEngine->getOutputChannel().lemma(lem);
      l = Node::null();
      u = Node::null();
      return;
    }else{
      u = u.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
      l = l.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
    }
  }
}

void BoundedIntegers::getBoundValues( Node f, Node v, RepSetIterator * rsi, Node & l, Node & u ) {
  getBounds( f, v, rsi, l, u );
  Trace("bound-int-rsi") << "Get value in model for..." << l << " and " << u << std::endl;
  l = d_quantEngine->getModel()->getCurrentModelValue( l );
  u = d_quantEngine->getModel()->getCurrentModelValue( u );
  Trace("bound-int-rsi") << "Value is " << l << " ... " << u << std::endl;
  return;
}

bool BoundedIntegers::isGroundRange(Node f, Node v) {
  return isBoundVar(f,v) && !quantifiers::TermDb::hasBoundVarAttr(getLowerBound(f,v)) && !quantifiers::TermDb::hasBoundVarAttr(getUpperBound(f,v));
}
