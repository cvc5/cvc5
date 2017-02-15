/*********************                                                        */
/*! \file bounded_integers.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bounded integers module
 **
 ** This class manages integer bounds for quantifiers
 **/

#include "options/quantifiers_options.h"
#include "theory/quantifiers/bounded_integers.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/term_database.h"
#include "theory/theory_engine.h"

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;


BoundedIntegers::IntRangeModel::IntRangeModel(BoundedIntegers * bi, Node r, context::Context* c, context::Context* u, bool isProxy) : d_bi(bi),
      d_range(r), d_curr_max(-1), d_lit_to_range(u), d_range_assertions(c), d_has_range(c,false), d_curr_range(c,-1), d_ranges_proxied(u) { 
  if( options::fmfBoundLazy() ){
    d_proxy_range = isProxy ? r : NodeManager::currentNM()->mkSkolem( "pbir", r.getType() );
  }else{
    d_proxy_range = r;
  }
  if( !isProxy ){
    Trace("bound-int") << "Introduce proxy " << d_proxy_range << " for " << d_range << std::endl;
  }
}

void BoundedIntegers::IntRangeModel::initialize() {
  //add initial split lemma
  Node ltr = NodeManager::currentNM()->mkNode( LT, d_proxy_range, NodeManager::currentNM()->mkConst( Rational(0) ) );
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

void BoundedIntegers::IntRangeModel::assertNode(Node n) {
  bool pol = n.getKind()!=NOT;
  Node nlit = n.getKind()==NOT ? n[0] : n;
  if( d_lit_to_range.find( nlit )!=d_lit_to_range.end() ){
    int vrange = d_lit_to_range[nlit];
    Trace("bound-int-assert") << "With polarity = " << pol << " (req "<< d_lit_to_pol[nlit] << ")";
    Trace("bound-int-assert") << ", found literal " << nlit;
    Trace("bound-int-assert") << ", it is bound literal " << vrange << " for " << d_range << std::endl;
    d_range_assertions[nlit] = (pol==d_lit_to_pol[nlit]);
    if( pol!=d_lit_to_pol[nlit] ){
      //check if we need a new split?
      if( !d_has_range ){
        bool needsRange = true;
        for( NodeIntMap::iterator it = d_lit_to_range.begin(); it != d_lit_to_range.end(); ++it ){
          if( d_range_assertions.find( (*it).first )==d_range_assertions.end() ){
            Trace("bound-int-debug") << "Does not need range because of " << (*it).first << std::endl;
            needsRange = false;
            break;
          }
        }
        if( needsRange ){
          allocateRange();
        }
      }
    }else{
      if (!d_has_range || vrange<d_curr_range ){
        Trace("bound-int-bound") << "Successfully bound " << d_range << " to " << vrange << std::endl;
        d_curr_range = vrange;
      }
      //set the range
      d_has_range = true;
    }
  }else{
    Message() << "Could not find literal " << nlit << " for range " << d_range << std::endl;
    exit(0);
  }
}

void BoundedIntegers::IntRangeModel::allocateRange() {
  d_curr_max++;
  int newBound = d_curr_max;
  Trace("bound-int-proc") << "Allocate range bound " << newBound << " for " << d_range << std::endl;
  //TODO: newBound should be chosen in a smarter way
  Node ltr = NodeManager::currentNM()->mkNode( LEQ, d_proxy_range, NodeManager::currentNM()->mkConst( Rational(newBound) ) );
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

Node BoundedIntegers::IntRangeModel::getNextDecisionRequest() {
  //request the current cardinality as a decision literal, if not already asserted
  for( NodeIntMap::iterator it = d_lit_to_range.begin(); it != d_lit_to_range.end(); ++it ){
    int i = (*it).second;
    if( !d_has_range || i<d_curr_range ){
      Node rn = (*it).first;
      Assert( !rn.isNull() );
      if( d_range_assertions.find( rn )==d_range_assertions.end() ){
        if (!d_lit_to_pol[rn]) {
          rn = rn.negate();
        }
        Trace("bound-int-dec-debug") << "For " << d_range << ", make decision " << rn << " to make range " << i << std::endl;
        return rn;
      }
    }
  }
  return Node::null();
}

bool BoundedIntegers::IntRangeModel::proxyCurrentRange() {
  //Trace("model-engine") << "Range(" << d_range << ") currently is " << d_curr_max.get() << std::endl;
  if( d_range!=d_proxy_range ){
    //int curr = d_curr_range.get();
    int curr = d_curr_max;
    if( d_ranges_proxied.find( curr )==d_ranges_proxied.end() ){
      d_ranges_proxied[curr] = true;
      Assert( d_range_literal.find( curr )!=d_range_literal.end() );
      Node lem = NodeManager::currentNM()->mkNode( IFF, d_range_literal[curr].negate(),
                   NodeManager::currentNM()->mkNode( LEQ, d_range, NodeManager::currentNM()->mkConst( Rational(curr) ) ) );
      Trace("bound-int-lemma") << "*** bound int : proxy lemma : " << lem << std::endl;
      d_bi->getQuantifiersEngine()->addLemma( lem );
      return true;
    }
  }
  return false;
}





BoundedIntegers::BoundedIntegers(context::Context* c, QuantifiersEngine* qe) :
QuantifiersModule(qe), d_assertions(c){

}

BoundedIntegers::~BoundedIntegers() { 
  for( std::map< Node, RangeModel * >::iterator it = d_rms.begin(); it != d_rms.end(); ++it ){
    delete it->second;
  }
}

void BoundedIntegers::presolve() {
  d_bnd_it.clear();
}

bool BoundedIntegers::isBound( Node f, Node v ) {
  return std::find( d_set[f].begin(), d_set[f].end(), v )!=d_set[f].end();
}

bool BoundedIntegers::hasNonBoundVar( Node f, Node b, std::map< Node, bool >& visited ) {
  if( visited.find( b )==visited.end() ){
    visited[b] = true;
    if( b.getKind()==BOUND_VARIABLE ){
      if( !isBound( f, b ) ){
        return true;
      }
    }else{
      for( unsigned i=0; i<b.getNumChildren(); i++ ){
        if( hasNonBoundVar( f, b[i], visited ) ){
          return true;
        }
      }
    }
  }
  return false;
}
bool BoundedIntegers::hasNonBoundVar( Node f, Node b ) {
  std::map< Node, bool > visited;
  return hasNonBoundVar( f, b, visited );
}

bool BoundedIntegers::processEqDisjunct( Node q, Node n, Node& v, std::vector< Node >& v_cases ) {
  if( n.getKind()==EQUAL ){
    for( unsigned i=0; i<2; i++ ){
      Node t = n[i];
      if( !hasNonBoundVar( q, n[1-i] ) ){
        if( t==v ){
          v_cases.push_back( n[1-i] );
          return true;
        }else if( v.isNull() && t.getKind()==BOUND_VARIABLE ){
          v = t;
          v_cases.push_back( n[1-i] );
          return true;
        }
      }
    }
  }
  return false;
}

void BoundedIntegers::processMatchBoundVars( Node q, Node n, std::vector< Node >& bvs, std::map< Node, bool >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==BOUND_VARIABLE && !isBound( q, n ) ){
      bvs.push_back( n );
    //injective operators
    }else if( n.getKind()==kind::APPLY_CONSTRUCTOR ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        processMatchBoundVars( q, n[i], bvs, visited );
      }
    }    
  }
}

void BoundedIntegers::process( Node q, Node n, bool pol,
                               std::map< Node, unsigned >& bound_lit_type_map,
                               std::map< int, std::map< Node, Node > >& bound_lit_map,
                               std::map< int, std::map< Node, bool > >& bound_lit_pol_map,
                               std::map< int, std::map< Node, Node > >& bound_int_range_term,
                               std::map< Node, std::vector< Node > >& bound_fixed_set ){
  if( n.getKind()==OR || n.getKind()==AND ){
    if( (n.getKind()==OR)==pol ){
      for( unsigned i=0; i<n.getNumChildren(); i++) {
        process( q, n[i], pol, bound_lit_type_map, bound_lit_map, bound_lit_pol_map, bound_int_range_term, bound_fixed_set );
      }
    }else{
      //if we are ( x != t1 ^ ...^ x != tn ), then x can be bound to { t1...tn }
      Node conj = n;
      if( !pol ){
        conj = TermDb::simpleNegate( conj );
      }
      Trace("bound-int-debug") << "Process possible finite disequality conjunction : " << conj << std::endl;
      Assert( conj.getKind()==AND );
      Node v;
      std::vector< Node > v_cases;
      bool success = true;
      for( unsigned i=0; i<conj.getNumChildren(); i++ ){
        if( conj[i].getKind()==NOT && processEqDisjunct( q, conj[i][0], v, v_cases ) ){
          //continue
        }else{
          Trace("bound-int-debug") << "...failed due to " << conj[i] << std::endl;
          success = false;
          break;
        }
      }
      if( success && !isBound( q, v ) ){
        Trace("bound-int-debug") << "Success with variable " << v << std::endl;
        bound_lit_type_map[v] = BOUND_FIXED_SET;
        bound_lit_map[3][v] = n;
        bound_lit_pol_map[3][v] = pol;
        bound_fixed_set[v].clear();
        bound_fixed_set[v].insert( bound_fixed_set[v].end(), v_cases.begin(), v_cases.end() );
      }
    }
  }else if( n.getKind()==EQUAL ){
    if( !pol ){
      // non-applied DER on x != t, x can be bound to { t }
      Node v;
      std::vector< Node > v_cases;
      if( processEqDisjunct( q, n, v, v_cases ) ){
        if( !isBound( q, v ) ){
          bound_lit_type_map[v] = BOUND_FIXED_SET;
          bound_lit_map[3][v] = n;
          bound_lit_pol_map[3][v] = pol;
          Assert( v_cases.size()==1 );
          bound_fixed_set[v].clear();
          bound_fixed_set[v].push_back( v_cases[0] );
        }
      }
    }  
  }else if( n.getKind()==NOT ){
    process( q, n[0], !pol, bound_lit_type_map, bound_lit_map, bound_lit_pol_map, bound_int_range_term, bound_fixed_set );
  }else if( n.getKind()==GEQ ){
    if( n[0].getType().isInteger() ){
      std::map< Node, Node > msum;
      if( QuantArith::getMonomialSumLit( n, msum ) ){
        Trace("bound-int-debug") << "literal (polarity = " << pol << ") " << n << " is monomial sum : " << std::endl;
        QuantArith::debugPrintMonomialSum( msum, "bound-int-debug" );
        for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
          if ( !it->first.isNull() && it->first.getKind()==BOUND_VARIABLE && !isBound( q, it->first ) ){
            //if not bound in another way
            if( bound_lit_type_map.find( it->first )==bound_lit_type_map.end() || bound_lit_type_map[it->first] == BOUND_INT_RANGE ){
              Node veq;
              if( QuantArith::isolate( it->first, msum, veq, GEQ )!=0 ){
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
                if( !hasNonBoundVar( q, t ) ) {
                  Trace("bound-int-debug") << "The bound is relevant." << std::endl;
                  int loru = n1==it->first ? 0 : 1;
                  bound_lit_type_map[it->first] = BOUND_INT_RANGE;
                  bound_int_range_term[loru][it->first] = t;
                  bound_lit_map[loru][it->first] = n;
                  bound_lit_pol_map[loru][it->first] = pol;
                }else{
                  Trace("bound-int-debug") << "The term " << t << " has non-bound variable." << std::endl;
                }
              }
            }
          }
        }
      }
    }
  }else if( n.getKind()==MEMBER ){
    if( !pol && !hasNonBoundVar( q, n[1] ) ){
      std::vector< Node > bound_vars;
      std::map< Node, bool > visited;
      processMatchBoundVars( q, n[0], bound_vars, visited );
      for( unsigned i=0; i<bound_vars.size(); i++ ){
        Node v = bound_vars[i];
        Trace("bound-int-debug") << "literal (polarity = " << pol << ") " << n << " is membership." << std::endl;
        bound_lit_type_map[v] = BOUND_SET_MEMBER;
        bound_lit_map[2][v] = n;
        bound_lit_pol_map[2][v] = pol;
      }
    }
  }else{
    Assert( n.getKind()!=LEQ && n.getKind()!=LT && n.getKind()!=GT );
  }
}

bool BoundedIntegers::needsCheck( Theory::Effort e ) {
  return e==Theory::EFFORT_LAST_CALL;
}

void BoundedIntegers::check( Theory::Effort e, unsigned quant_e ) {
  if( quant_e==QuantifiersEngine::QEFFORT_STANDARD ){
    Trace("bint-engine") << "---Bounded Integers---" << std::endl;
    bool addedLemma = false;
    //make sure proxies are up-to-date with range
    for( unsigned i=0; i<d_ranges.size(); i++) {
      if( d_rms[d_ranges[i]]->proxyCurrentRange() ){
        addedLemma = true;
      }
    }
    Trace("bint-engine") << "   addedLemma = " << addedLemma << std::endl;
  }
}


void BoundedIntegers::addLiteralFromRange( Node lit, Node r ) {
  d_lit_to_ranges[lit].push_back(r);
  //check if it is already asserted?
  if(d_assertions.find(lit)!=d_assertions.end()){
    d_rms[r]->assertNode( d_assertions[lit] ? lit : lit.negate() );
  }
}

void BoundedIntegers::setBoundedVar( Node q, Node v, unsigned bound_type ) {
  d_bound_type[q][v] = bound_type;
  d_set_nums[q][v] = d_set[q].size();
  d_set[q].push_back( v );
  Trace("bound-int-var") << "Bound variable #" << d_set_nums[q][v] << " : " << v << std::endl; 
}

void BoundedIntegers::preRegisterQuantifier( Node f ) {
  //this needs to be done at preregister since it affects e.g. QuantDSplit's preregister
  Trace("bound-int") << "preRegister quantifier " << f << std::endl;
  
  bool success;
  do{
    std::map< Node, unsigned > bound_lit_type_map;
    std::map< int, std::map< Node, Node > > bound_lit_map;
    std::map< int, std::map< Node, bool > > bound_lit_pol_map;
    std::map< int, std::map< Node, Node > > bound_int_range_term;
    std::map< Node, std::vector< Node > > bound_fixed_set;
    success = false;
    process( f, f[1], true, bound_lit_type_map, bound_lit_map, bound_lit_pol_map, bound_int_range_term, bound_fixed_set );
    //for( std::map< Node, Node >::iterator it = d_bounds[0][f].begin(); it != d_bounds[0][f].end(); ++it ){
    for( std::map< Node, unsigned >::iterator it = bound_lit_type_map.begin(); it != bound_lit_type_map.end(); ++it ){
      Node v = it->first;
      if( !isBound( f, v ) ){
        bool setBoundVar = false;
        if( it->second==BOUND_INT_RANGE ){
          //must have both
          if( bound_lit_map[0].find( v )!=bound_lit_map[0].end() && bound_lit_map[1].find( v )!=bound_lit_map[1].end() ){
            setBoundedVar( f, v, BOUND_INT_RANGE );
            setBoundVar = true;
            for( unsigned b=0; b<2; b++ ){
              //set the bounds
              Assert( bound_int_range_term[b].find( v )!=bound_int_range_term[b].end() );
              d_bounds[b][f][v] = bound_int_range_term[b][v];
            }
            if( options::fmfBoundMinMode()==FMF_BOUND_MIN_ALL || options::fmfBoundMinMode()==FMF_BOUND_MIN_INT_RANGE ){
              Node r = NodeManager::currentNM()->mkNode( MINUS, d_bounds[1][f][v], d_bounds[0][f][v] );
              d_range[f][v] = Rewriter::rewrite( r );
            }
            Trace("bound-int") << "Variable " << v << " is bound because of int range literals " << bound_lit_map[0][v] << " and " << bound_lit_map[1][v] << std::endl;
          }
        }else if( it->second==BOUND_SET_MEMBER ){
          setBoundedVar( f, v, BOUND_SET_MEMBER );
          setBoundVar = true;
          d_setm_range[f][v] = bound_lit_map[2][v][1];
          d_setm_range_lit[f][v] = bound_lit_map[2][v];
          if( options::fmfBoundMinMode()==FMF_BOUND_MIN_ALL || options::fmfBoundMinMode()==FMF_BOUND_MIN_SET_CARD ){
            d_range[f][v] = NodeManager::currentNM()->mkNode( CARD, d_setm_range[f][v] );
          }
          Trace("bound-int") << "Variable " << v << " is bound because of set membership literal " << bound_lit_map[2][v] << std::endl;
        }else if( it->second==BOUND_FIXED_SET ){
          setBoundedVar( f, v, BOUND_FIXED_SET );
          setBoundVar = true;
          for( unsigned i=0; i<bound_fixed_set[v].size(); i++ ){
            Node t = bound_fixed_set[v][i];
            if( t.hasBoundVar() ){
              d_fixed_set_ngr_range[f][v].push_back( t ); 
            }else{
              d_fixed_set_gr_range[f][v].push_back( t ); 
            }
          } 
          Trace("bound-int") << "Variable " << v << " is bound because of disequality conjunction " << bound_lit_map[3][v] << std::endl;
        }
        if( setBoundVar ){
          success = true;
          //set Attributes on literals
          for( unsigned b=0; b<2; b++ ){
            if( bound_lit_map[b].find( v )!=bound_lit_map[b].end() ){
              Assert( bound_lit_pol_map[b].find( v )!=bound_lit_pol_map[b].end() );
              BoundIntLitAttribute bila;
              bound_lit_map[b][v].setAttribute( bila, bound_lit_pol_map[b][v] ? 1 : 0 );
            }else{
              Assert( it->second!=BOUND_INT_RANGE );
            }
          }
        }
      }
    }
    if( !success ){
      //resort to setting a finite bound on a variable
      for( unsigned i=0; i<f[0].getNumChildren(); i++) {
        if( d_bound_type[f].find( f[0][i] )==d_bound_type[f].end() ){
          TypeNode tn = f[0][i].getType();
          if( tn.isSort() || getTermDatabase()->mayComplete( tn ) ){
            success = true;
            setBoundedVar( f, f[0][i], BOUND_FINITE );
            break;
          }
        }
      }
    }
  }while( success );
  
  if( Trace.isOn("bound-int") ){
    Trace("bound-int") << "Bounds are : " << std::endl;
    for( unsigned i=0; i<f[0].getNumChildren(); i++) {
      Node v = f[0][i];
      if( std::find( d_set[f].begin(), d_set[f].end(), v )!=d_set[f].end() ){
        Assert( d_bound_type[f].find( v )!=d_bound_type[f].end() );
        if( d_bound_type[f][v]==BOUND_INT_RANGE ){
          Trace("bound-int") << "  " << d_bounds[0][f][v] << " <= " << v << " <= " << d_bounds[1][f][v] << " (range is " << d_range[f][v] << ")" << std::endl;
        }else if( d_bound_type[f][v]==BOUND_SET_MEMBER ){
          if( d_setm_range_lit[f][v][0]==v ){
            Trace("bound-int") << "  " << v << " in " << d_setm_range[f][v] << std::endl;
          }else{
            Trace("bound-int") << "  " << v << " unifiable in " << d_setm_range_lit[f][v] << std::endl;
          }
        }else if( d_bound_type[f][v]==BOUND_FIXED_SET ){
          Trace("bound-int") << "  " << v << " in { ";
          for( unsigned i=0; i<d_fixed_set_ngr_range[f][v].size(); i++ ){ 
            Trace("bound-int") << d_fixed_set_ngr_range[f][v][i] << " ";
          }
          for( unsigned i=0; i<d_fixed_set_gr_range[f][v].size(); i++ ){ 
            Trace("bound-int") << d_fixed_set_gr_range[f][v][i] << " ";
          }
          Trace("bound-int") << "}" << std::endl;
        }else if( d_bound_type[f][v]==BOUND_FINITE ){
          Trace("bound-int") << "  " << v << " has small finite type." << std::endl;
        }else{
          Trace("bound-int") << "  " << v << " has unknown bound." << std::endl;
          Assert( false );
        }
      }else{
        Trace("bound-int") << "  " << "*** " << v << " is unbounded." << std::endl;
      }
    }
  }
  
  bool bound_success = true;
  for( unsigned i=0; i<f[0].getNumChildren(); i++) {
    if( d_bound_type[f].find( f[0][i] )==d_bound_type[f].end() ){
      Trace("bound-int-warn") << "Warning : Bounded Integers : Due to quantification on " << f[0][i] << ", could not find bounds for " << f << std::endl;
      bound_success = false;
      break;
    }
  }
  
  if( bound_success ){
    d_bound_quants.push_back( f );
    for( unsigned i=0; i<d_set[f].size(); i++) {
      Node v = d_set[f][i];
      std::map< Node, Node >::iterator itr = d_range[f].find( v );
      if( itr != d_range[f].end() ){
        Node r = itr->second;
        Assert( !r.isNull() );
        bool isProxy = false;
        if( r.hasBoundVar() ){
          //introduce a new bound
          Node new_range = NodeManager::currentNM()->mkSkolem( "bir", r.getType(), "bound for term" );
          d_nground_range[f][v] = r;
          d_range[f][v] = new_range;
          r = new_range;
          isProxy = true;
        }
        if( !r.isConst() ){
          if( std::find(d_ranges.begin(), d_ranges.end(), r)==d_ranges.end() ){
            Trace("bound-int") << "For " << v << ", bounded Integer Module will try to minimize : " << r << std::endl;
            d_ranges.push_back( r );
            d_rms[r] = new IntRangeModel( this, r, d_quantEngine->getSatContext(), d_quantEngine->getUserContext(), isProxy );
            d_rms[r]->initialize();
          }
        }
      }
    }
  }
}

void BoundedIntegers::registerQuantifier( Node q ) {

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

Node BoundedIntegers::getNextDecisionRequest( unsigned& priority ) {
  Trace("bound-int-dec-debug") << "bi: Get next decision request?" << std::endl;
  for( unsigned i=0; i<d_ranges.size(); i++) {
    Node d = d_rms[d_ranges[i]]->getNextDecisionRequest();
    if (!d.isNull()) {
      bool polLit = d.getKind()!=NOT;
      Node lit = d.getKind()==NOT ? d[0] : d;
      bool value;
      if( d_quantEngine->getValuation().hasSatValue( lit, value ) ) {
        if( value==polLit ){
          Trace("bound-int-dec-debug") << "...already asserted properly." << std::endl;
          //already true, we're already fine
        }else{
          Trace("bound-int-dec-debug") << "...already asserted with wrong polarity, re-assert." << std::endl;
          assertNode( d.negate() );
          i--;
        }
      }else{
        priority = 1;
        Trace("bound-int-dec") << "Bounded Integers : Decide " << d << std::endl;
        return d;
      }
    }
  }
  Trace("bound-int-dec-debug") << "No decision request." << std::endl;
  return Node::null();
}

unsigned BoundedIntegers::getBoundVarType( Node q, Node v ) {
  std::map< Node, unsigned >::iterator it = d_bound_type[q].find( v );
  if( it==d_bound_type[q].end() ){
    return BOUND_NONE;
  }else{
    return it->second;
  }
}

void BoundedIntegers::getBounds( Node f, Node v, RepSetIterator * rsi, Node & l, Node & u ) {
  l = d_bounds[0][f][v];
  u = d_bounds[1][f][v];
  if( d_nground_range[f].find(v)!=d_nground_range[f].end() ){
    //get the substitution
    std::vector< Node > vars;
    std::vector< Node > subs;
    if( getRsiSubsitution( f, v, vars, subs, rsi ) ){
      u = u.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
      l = l.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
    }else{
      u = Node::null();
      l = Node::null();
    }
  }
}

void BoundedIntegers::getBoundValues( Node f, Node v, RepSetIterator * rsi, Node & l, Node & u ) {
  getBounds( f, v, rsi, l, u );
  Trace("bound-int-rsi") << "Get value in model for..." << l << " and " << u << std::endl;
  if( !l.isNull() ){
    l = d_quantEngine->getModel()->getCurrentModelValue( l );
  }
  if( !u.isNull() ){
    u = d_quantEngine->getModel()->getCurrentModelValue( u );
  }
  Trace("bound-int-rsi") << "Value is " << l << " ... " << u << std::endl;
  return;
}

bool BoundedIntegers::isGroundRange( Node q, Node v ) {
  if( isBoundVar(q,v) ){
    if( d_bound_type[q][v]==BOUND_INT_RANGE ){
      return !getLowerBound(q,v).hasBoundVar() && !getUpperBound(q,v).hasBoundVar();
    }else if( d_bound_type[q][v]==BOUND_SET_MEMBER ){
      return !d_setm_range[q][v].hasBoundVar();
    }else if( d_bound_type[q][v]==BOUND_FIXED_SET ){
      return !d_fixed_set_ngr_range[q][v].empty();
    }
  }
  return false;
}

Node BoundedIntegers::getSetRange( Node q, Node v, RepSetIterator * rsi ) {
  Node sr = d_setm_range[q][v];
  if( d_nground_range[q].find(v)!=d_nground_range[q].end() ){
    //get the substitution
    std::vector< Node > vars;
    std::vector< Node > subs;
    if( getRsiSubsitution( q, v, vars, subs, rsi ) ){
      sr = sr.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
    }else{
      sr = Node::null();
    }
  }
  return sr;
}

Node BoundedIntegers::getSetRangeValue( Node q, Node v, RepSetIterator * rsi ) {
  Node sr = getSetRange( q, v, rsi );
  if( !sr.isNull() ){
    Trace("bound-int-rsi") << "Get value in model for..." << sr << std::endl;
    sr = d_quantEngine->getModel()->getCurrentModelValue( sr );
    Trace("bound-int-rsi") << "Value is " << sr << std::endl;
    //as heuristic, map to term model
    if( sr.getKind()!=EMPTYSET ){
      std::map< Node, Node > val_to_term;
      while( sr.getKind()==UNION ){
        Assert( sr[1].getKind()==kind::SINGLETON );
        val_to_term[ sr[1][0] ] = sr[1][0];
        sr = sr[0];
      }
      Assert( sr.getKind()==kind::SINGLETON );
      val_to_term[ sr[0] ] = sr[0];
      //must look back at assertions, not term database (theory of sets introduces extraneous terms internally)
      Theory* theory = d_quantEngine->getTheoryEngine()->theoryOf( THEORY_SETS );
      if( theory ){
        context::CDList<Assertion>::const_iterator it = theory->facts_begin(), it_end = theory->facts_end();
        for( unsigned i = 0; it != it_end; ++ it, ++i ){
          Node lit = (*it).assertion;
          if( lit.getKind()==kind::MEMBER ){
            Node vr = d_quantEngine->getModel()->getCurrentModelValue( lit[0] );
            Trace("bound-int-rsi-debug") << "....membership for " << lit << " ==> " << vr << std::endl;
            Trace("bound-int-rsi-debug") << "  " << (val_to_term.find( vr )!=val_to_term.end()) << " " << d_quantEngine->getEqualityQuery()->areEqual( d_setm_range_lit[q][v][1], lit[1] ) << std::endl;
            if( val_to_term.find( vr )!=val_to_term.end() ){
              if( d_quantEngine->getEqualityQuery()->areEqual( d_setm_range_lit[q][v][1], lit[1] ) ){
                Trace("bound-int-rsi") << "  Map value to term : " << vr << " -> " << lit[0] << std::endl;
                val_to_term[ vr ] = lit[0];
              }
            }
          }
        }
      }
      //rebuild value
      Node nsr;
      for( std::map< Node, Node >::iterator it = val_to_term.begin(); it != val_to_term.end(); ++it ){
        Node nv = NodeManager::currentNM()->mkNode( kind::SINGLETON, it->second );
        if( nsr.isNull() ){
          nsr = nv;
        }else{
          nsr = NodeManager::currentNM()->mkNode( kind::UNION, nsr, nv );
        }
      }
      Trace("bound-int-rsi") << "...reconstructed " << nsr << std::endl;
      return nsr;
      
      /*
      Node lit = d_setm_range_lit[q][v];
      Trace("bound-int-rsi-debug") << "Bounded from lit " << lit << std::endl;
      Node f = d_quantEngine->getTermDatabase()->getMatchOperator( lit );
      TermArgTrie * ta = d_quantEngine->getTermDatabase()->getTermArgTrie( f );
      if( ta ){
        Trace("bound-int-rsi-debug") << "Got term index for " << f << std::endl;
        for( std::map< TNode, TermArgTrie >::iterator it = ta->d_data.begin(); it != ta->d_data.end(); ++it ){

        }

      }
      */
    }
    
  }
  return sr;
}

bool BoundedIntegers::getRsiSubsitution( Node q, Node v, std::vector< Node >& vars, std::vector< Node >& subs, RepSetIterator * rsi ) {

  Trace("bound-int-rsi") << "Get bound value in model of variable " << v << std::endl;
  Assert( d_set_nums[q].find( v )!=d_set_nums[q].end() );
  int vindex = d_set_nums[q][v];
  Assert( d_set_nums[q][v]==vindex );
  Trace("bound-int-rsi-debug") << "  index order is " << vindex << std::endl;
  //must take substitution for all variables that are iterating at higher level
  for( int i=0; i<vindex; i++) {
    Assert( d_set_nums[q][d_set[q][i]]==i );
    Trace("bound-int-rsi") << "Look up the value for " << d_set[q][i] << " " << i << std::endl;
    int v = rsi->getVariableOrder( i );
    Assert( q[0][v]==d_set[q][i] );
    Node t = rsi->getCurrentTerm( v );
    Trace("bound-int-rsi") << "term : " << t << std::endl;
    if( rsi->d_rep_set->d_values_to_terms.find( t )!=rsi->d_rep_set->d_values_to_terms.end() ){
      t = rsi->d_rep_set->d_values_to_terms[t];
      Trace("bound-int-rsi") << "term (post-rep) : " << t << std::endl;
    }
    vars.push_back( d_set[q][i] );
    subs.push_back( t );
  }
  
  //check if it has been instantiated
  if( !vars.empty() && !d_bnd_it[q][v].hasInstantiated(subs) ){
    if( d_bound_type[q][v]==BOUND_INT_RANGE || d_bound_type[q][v]==BOUND_SET_MEMBER ){
      //must add the lemma
      Node nn = d_nground_range[q][v];
      nn = nn.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
      Node lem = NodeManager::currentNM()->mkNode( LEQ, nn, d_range[q][v] );
      Trace("bound-int-lemma") << "*** Add lemma to minimize instantiated non-ground term " << lem << std::endl;
      d_quantEngine->getOutputChannel().lemma(lem, false, true);
    }
    return false;
  }else{
    return true;
  }
}

Node BoundedIntegers::matchBoundVar( Node v, Node t, Node e ){
  if( t==v ){
    return e;
  }else if( t.getKind()==kind::APPLY_CONSTRUCTOR ){
    if( e.getKind()==kind::APPLY_CONSTRUCTOR ){
      if( t.getOperator() != e.getOperator() ) {
        return Node::null();
      }
    }
    const Datatype& dt = Datatype::datatypeOf( t.getOperator().toExpr() );
    unsigned index = Datatype::indexOf( t.getOperator().toExpr() );
    for( unsigned i=0; i<t.getNumChildren(); i++ ){
      Node u;
      if( e.getKind()==kind::APPLY_CONSTRUCTOR ){
        u = matchBoundVar( v, t[i], e[i] );
      }else{
        Node se = NodeManager::currentNM()->mkNode( kind::APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[index][i].getSelector() ), e );
        u = matchBoundVar( v, t[i], se );
      }
      if( !u.isNull() ){
        return u;
      }
    }
  }
  return Node::null();
}

bool BoundedIntegers::getBoundElements( RepSetIterator * rsi, bool initial, Node q, Node v, std::vector< Node >& elements ) {
  if( initial || !isGroundRange( q, v ) ){
    elements.clear();
    unsigned bvt = getBoundVarType( q, v );
    if( bvt==BOUND_INT_RANGE ){
      Node l, u;
      getBoundValues( q, v, rsi, l, u );
      if( l.isNull() || u.isNull() ){
        //failed, abort the iterator
        return false;
      }else{
        Trace("bound-int-rsi") << "Can limit bounds of " << v << " to " << l << "..." << u << std::endl;
        Node range = Rewriter::rewrite( NodeManager::currentNM()->mkNode( MINUS, u, l ) );
        Node ra = Rewriter::rewrite( NodeManager::currentNM()->mkNode( LEQ, range, NodeManager::currentNM()->mkConst( Rational( 9999 ) ) ) );
        Node tl = l;
        Node tu = u;
        getBounds( q, v, rsi, tl, tu );
        Assert( !tl.isNull() && !tu.isNull() );
        if( ra==d_quantEngine->getTermDatabase()->d_true ){
          long rr = range.getConst<Rational>().getNumerator().getLong()+1;
          Trace("bound-int-rsi")  << "Actual bound range is " << rr << std::endl;
          for( unsigned k=0; k<rr; k++ ){
            Node t = NodeManager::currentNM()->mkNode(PLUS, tl, NodeManager::currentNM()->mkConst( Rational(k) ) );
            t = Rewriter::rewrite( t );
            elements.push_back( t );
          }
          return true;
        }else{
          Trace("fmf-incomplete") << "Incomplete because of integer quantification, bounds are too big for " << v << "." << std::endl;
          return false;
        }
      }
    }else if( bvt==BOUND_SET_MEMBER  ){ 
      Node srv = getSetRangeValue( q, v, rsi );
      if( srv.isNull() ){
        return false;
      }else{
        Trace("bound-int-rsi") << "Bounded by set membership : " << srv << std::endl;
        if( srv.getKind()!=EMPTYSET ){
          //collect the elements
          while( srv.getKind()==UNION ){
            Assert( srv[1].getKind()==kind::SINGLETON );
            elements.push_back( srv[1][0] );
            srv = srv[0];
          }
          Assert( srv.getKind()==kind::SINGLETON );
          elements.push_back( srv[0] );
          //check if we need to do matching, for literals like ( tuple( v ) in S )
          Node t = d_setm_range_lit[q][v][0];
          if( t!=v ){
            std::vector< Node > elements_tmp;
            elements_tmp.insert( elements_tmp.end(), elements.begin(), elements.end() );
            elements.clear();
            for( unsigned i=0; i<elements_tmp.size(); i++ ){
              //do matching to determine v -> u
              Node u = matchBoundVar( v, t, elements_tmp[i] );
              Trace("bound-int-rsi-debug") << "  unification : " << elements_tmp[i] << " = " << t << " yields " << v << " -> " << u << std::endl;
              if( !u.isNull() ){
                elements.push_back( u );
              }
            }
          }
        }
        return true;
      }
    }else if( bvt==BOUND_FIXED_SET ){
      std::map< Node, std::vector< Node > >::iterator it = d_fixed_set_gr_range[q].find( v );
      if( it!=d_fixed_set_gr_range[q].end() ){
        for( unsigned i=0; i<it->second.size(); i++ ){
          elements.push_back( it->second[i] );
        }
      }
      it = d_fixed_set_ngr_range[q].find( v );
      if( it!=d_fixed_set_ngr_range[q].end() ){
        std::vector< Node > vars;
        std::vector< Node > subs;
        if( getRsiSubsitution( q, v, vars, subs, rsi ) ){
          for( unsigned i=0; i<it->second.size(); i++ ){
            Node t = it->second[i].substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
            elements.push_back( t );
          }
          return true;
        }else{
          return false;
        }
      }else{
        return true;
      }
    }else{
      return false;
    }
  }else{
    //no change required
    return true;
  }
}

