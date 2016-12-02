/*********************                                                        */
/*! \file rep_set.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of representative set
 **/

#include "theory/rep_set.h"
#include "theory/type_enumerator.h"
#include "theory/quantifiers/bounded_integers.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/first_order_model.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

void RepSet::clear(){
  d_type_reps.clear();
  d_type_complete.clear();
  d_tmap.clear();
  d_values_to_terms.clear();
}

bool RepSet::hasRep( TypeNode tn, Node n ) {
  std::map< TypeNode, std::vector< Node > >::iterator it = d_type_reps.find( tn );
  if( it==d_type_reps.end() ){
    return false;
  }else{
    return std::find( it->second.begin(), it->second.end(), n )!=it->second.end();
  }
}

int RepSet::getNumRepresentatives( TypeNode tn ) const{
  std::map< TypeNode, std::vector< Node > >::const_iterator it = d_type_reps.find( tn );
  if( it!=d_type_reps.end() ){
    return (int)it->second.size();
  }else{
    return 0;
  }
}

bool containsStoreAll( Node n, std::vector< Node >& cache ){
  if( std::find( cache.begin(), cache.end(), n )==cache.end() ){
    cache.push_back( n );
    if( n.getKind()==STORE_ALL ){
      return true;
    }else{
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( containsStoreAll( n[i], cache ) ){
          return true;
        }
      }
    }
  }
  return false;
}

void RepSet::add( TypeNode tn, Node n ){
  //for now, do not add array constants FIXME
  if( tn.isArray() ){
    std::vector< Node > cache;
    if( containsStoreAll( n, cache ) ){
      return;
    }
  }
  Trace("rsi-debug") << "Add rep #" << d_type_reps[tn].size() << " for " << tn << " : " << n << std::endl;
  Assert( n.getType().isSubtypeOf( tn ) );
  d_tmap[ n ] = (int)d_type_reps[tn].size();
  d_type_reps[tn].push_back( n );
}

int RepSet::getIndexFor( Node n ) const {
  std::map< Node, int >::const_iterator it = d_tmap.find( n );
  if( it!=d_tmap.end() ){
    return it->second;
  }else{
    return -1;
  }
}

bool RepSet::complete( TypeNode t ){
  std::map< TypeNode, bool >::iterator it = d_type_complete.find( t );
  if( it==d_type_complete.end() ){
    //remove all previous
    for( unsigned i=0; i<d_type_reps[t].size(); i++ ){
      d_tmap.erase( d_type_reps[t][i] );
    }
    d_type_reps[t].clear();
    //now complete the type
    d_type_complete[t] = true;
    TypeEnumerator te(t);
    while( !te.isFinished() ){
      Node n = *te;
      if( std::find( d_type_reps[t].begin(), d_type_reps[t].end(), n )==d_type_reps[t].end() ){
        add( t, n );
      }
      ++te;
    }
    for( size_t i=0; i<d_type_reps[t].size(); i++ ){
      Trace("reps-complete") << d_type_reps[t][i] << " ";
    }
    Trace("reps-complete") << std::endl;
    return true;
  }else{
    return it->second;
  }
}

void RepSet::toStream(std::ostream& out){
  for( std::map< TypeNode, std::vector< Node > >::iterator it = d_type_reps.begin(); it != d_type_reps.end(); ++it ){
    if( !it->first.isFunction() && !it->first.isPredicate() ){
      out << "(" << it->first << " " << it->second.size();
      out << " (";
      for( unsigned i=0; i<it->second.size(); i++ ){
        if( i>0 ){ out << " "; }
        out << it->second[i];
      }
      out << ")";
      out << ")" << std::endl;
    }
  }
}


RepSetIterator::RepSetIterator( QuantifiersEngine * qe, RepSet* rs ) : d_qe(qe), d_rep_set( rs ){
  d_incomplete = false;
}

int RepSetIterator::domainSize( int i ) {
  Assert(i>=0);
  int v = d_var_order[i];
  if( d_enum_type[v]==ENUM_DOMAIN_ELEMENTS ){
    return d_domain[v].size();
  }else{
    return d_domain[v][0];
  }
}

bool RepSetIterator::setQuantifier( Node f ){
  Trace("rsi") << "Make rsi for " << f << std::endl;
  Assert( d_types.empty() );
  //store indicies
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    d_types.push_back( f[0][i].getType() );
  }
  d_owner = f;
  return initialize();
}

bool RepSetIterator::setFunctionDomain( Node op ){
  Trace("rsi") << "Make rsi for " << op << std::endl;
  Assert( d_types.empty() );
  TypeNode tn = op.getType();
  for( size_t i=0; i<tn.getNumChildren()-1; i++ ){
    d_types.push_back( tn[i] );
  }
  d_owner = op;
  return initialize();
}

bool RepSetIterator::initialize(){
  Trace("rsi") << "Initialize rep set iterator..." << std::endl;
  for( unsigned v=0; v<d_types.size(); v++ ){
    d_index.push_back( 0 );
    //store default index order
    d_index_order.push_back( v );
    d_var_order[v] = v;
    //store default domain
    d_domain.push_back( RepDomain() );
    TypeNode tn = d_types[v];
    Trace("rsi") << "Var #" << v << " is type " << tn << "..." << std::endl;
    if( tn.isSort() ){
      //must ensure uninterpreted type is non-empty.
      if( !d_rep_set->hasType( tn ) ){
        //FIXME:
        // terms in rep_set are now constants which mapped to terms through TheoryModel
        // thus, should introduce a constant and a term.  for now, just a term.

        //Node c = d_qe->getTermDatabase()->getEnumerateTerm( tn, 0 );
        Node var = d_qe->getModel()->getSomeDomainElement( tn );
        Trace("mkVar") << "RepSetIterator:: Make variable " << var << " : " << tn << std::endl;
        d_rep_set->add( tn, var );
      }
    }else{
      bool inc = true;
      //check if it is bound by bounded integer module
      if( d_owner.getKind()==FORALL && d_qe && d_qe->getBoundedIntegers() ){
        unsigned bvt = d_qe->getBoundedIntegers()->getBoundVarType( d_owner, d_owner[0][v] );
        if( bvt==quantifiers::BoundedIntegers::BOUND_INT_RANGE ){
          Trace("rsi") << "  variable is bounded integer." << std::endl;
          d_enum_type.push_back( ENUM_INT_RANGE );
          inc = false;
        }else if( bvt==quantifiers::BoundedIntegers::BOUND_SET_MEMBER ){
          Trace("rsi") << "  variable is bounded by set membership." << std::endl;
          d_enum_type.push_back( ENUM_SET_MEMBERS );
          inc = false;
        }
      }
      if( inc ){
        //check if it is otherwise bound
        if( d_bounds[0].find( v )!=d_bounds[0].end() && d_bounds[1].find( v )!=d_bounds[1].end() ){
          Trace("rsi") << "  variable is bounded." << std::endl;
          d_enum_type.push_back( ENUM_INT_RANGE );
        }else if( d_qe->getTermDatabase()->mayComplete( tn ) ){
          Trace("rsi") << "  do complete, since cardinality is small (" << tn.getCardinality() << ")..." << std::endl;
          d_rep_set->complete( tn );
          //must have succeeded
          Assert( d_rep_set->hasType( tn ) );
        }else{
          Trace("rsi") << "  variable cannot be bounded." << std::endl;
          Trace("fmf-incomplete") << "Incomplete because of quantification of type " << tn << std::endl;
          d_incomplete = true;
        }
      }
    }
    //if we have yet to determine the type of enumeration
    if( d_enum_type.size()<=v ){
      d_enum_type.push_back( ENUM_DOMAIN_ELEMENTS );
      if( d_rep_set->hasType( tn ) ){
        for( unsigned j=0; j<d_rep_set->d_type_reps[tn].size(); j++ ){
          d_domain[v].push_back( j );
        }
      }else{
        Assert( d_incomplete );
        return false;
      }
    }
  }
  //must set a variable index order based on bounded integers
  if( d_owner.getKind()==FORALL && d_qe && d_qe->getBoundedIntegers() ){
    Trace("bound-int-rsi") << "Calculating variable order..." << std::endl;
    std::vector< int > varOrder;
    for( unsigned i=0; i<d_qe->getBoundedIntegers()->getNumBoundVars( d_owner ); i++ ){
      Node v = d_qe->getBoundedIntegers()->getBoundVar( d_owner, i );
      Trace("bound-int-rsi") << "  bound var #" << i << " is " << v << std::endl;
      varOrder.push_back( d_qe->getTermDatabase()->getVariableNum( d_owner, v ) );
    }
    for( unsigned i=0; i<d_owner[0].getNumChildren(); i++) {
      if( !d_qe->getBoundedIntegers()->isBoundVar(d_owner, d_owner[0][i])) {
        varOrder.push_back(i);
      }
    }
    Trace("bound-int-rsi") << "Variable order : ";
    for( unsigned i=0; i<varOrder.size(); i++) {
      Trace("bound-int-rsi") << varOrder[i] << " ";
    }
    Trace("bound-int-rsi") << std::endl;
    std::vector< int > indexOrder;
    indexOrder.resize(varOrder.size());
    for( unsigned i=0; i<varOrder.size(); i++){
      indexOrder[varOrder[i]] = i;
    }
    Trace("bound-int-rsi") << "Will use index order : ";
    for( unsigned i=0; i<indexOrder.size(); i++) {
      Trace("bound-int-rsi") << indexOrder[i] << " ";
    }
    Trace("bound-int-rsi") << std::endl;
    setIndexOrder( indexOrder );
  }
  //now reset the indices
  do_reset_increment( -1, true );
  return true;
}

void RepSetIterator::setIndexOrder( std::vector< int >& indexOrder ){
  d_index_order.clear();
  d_index_order.insert( d_index_order.begin(), indexOrder.begin(), indexOrder.end() );
  //make the d_var_order mapping
  for( unsigned i=0; i<d_index_order.size(); i++ ){
    d_var_order[d_index_order[i]] = i;
  }
}

int RepSetIterator::resetIndex( int i, bool initial ) {
  d_index[i] = 0;
  int v = d_var_order[i];
  Trace("bound-int-rsi") << "Reset " << i << ", var order = " << v << ", initial = " << initial << std::endl;
  //determine the current range
  if( initial || ( d_owner.getKind()==FORALL && d_qe && d_qe->getBoundedIntegers() && 
                   d_qe->getBoundedIntegers()->isBoundVar( d_owner, d_owner[0][v] ) &&
                   !d_qe->getBoundedIntegers()->isGroundRange( d_owner, d_owner[0][v] ) ) ){
    Trace("bound-int-rsi") << "Getting range of " << d_owner[0][v] << std::endl;
    if( d_enum_type[v]==ENUM_INT_RANGE ){
      Node actual_l;
      Node l, u;
      if( d_qe->getBoundedIntegers() ){
        unsigned bvt = d_qe->getBoundedIntegers()->getBoundVarType( d_owner, d_owner[0][v] );
        if( bvt==quantifiers::BoundedIntegers::BOUND_INT_RANGE ){
          d_qe->getBoundedIntegers()->getBoundValues( d_owner, d_owner[0][v], this, l, u );
        }
      }
      for( unsigned b=0; b<2; b++ ){
        if( d_bounds[b].find(v)!=d_bounds[b].end() ){
          Trace("bound-int-rsi") << "May further limit bound(" << b << ") based on " << d_bounds[b][v] << std::endl;
          if( b==0 && (l.isNull() || d_bounds[b][v].getConst<Rational>() > l.getConst<Rational>()) ){
            if( !l.isNull() ){
              //bound was limited externally, record that the value lower bound is not equal to the term lower bound
              actual_l = NodeManager::currentNM()->mkNode( MINUS, d_bounds[b][v], l );
            }
            l = d_bounds[b][v];
          }else if( b==1 && (u.isNull() || d_bounds[b][v].getConst<Rational>() <= u.getConst<Rational>()) ){
            u = NodeManager::currentNM()->mkNode( MINUS, d_bounds[b][v],
                                                  NodeManager::currentNM()->mkConst( Rational(1) ) );
            u = Rewriter::rewrite( u );
          }
        }
      }

      if( l.isNull() || u.isNull() ){
        //failed, abort the iterator
        return -1;
      }else{
        Trace("bound-int-rsi") << "Can limit bounds of " << d_owner[0][v] << " to " << l << "..." << u << std::endl;
        Node range = Rewriter::rewrite( NodeManager::currentNM()->mkNode( MINUS, u, l ) );
        Node ra = Rewriter::rewrite( NodeManager::currentNM()->mkNode( LEQ, range, NodeManager::currentNM()->mkConst( Rational( 9999 ) ) ) );
        d_domain[v].clear();
        Node tl = l;
        Node tu = u;
        if( d_qe->getBoundedIntegers() && d_qe->getBoundedIntegers()->isBoundVar( d_owner, d_owner[0][v] ) ){
          d_qe->getBoundedIntegers()->getBounds( d_owner, d_owner[0][v], this, tl, tu );
        }
        d_lower_bounds[v] = tl;
        if( !actual_l.isNull() ){
          //if bound was limited externally, must consider the offset
          d_lower_bounds[v] = Rewriter::rewrite( NodeManager::currentNM()->mkNode( PLUS, tl, actual_l ) );
        }
        if( ra==d_qe->getTermDatabase()->d_true ){
          long rr = range.getConst<Rational>().getNumerator().getLong()+1;
          Trace("bound-int-rsi")  << "Actual bound range is " << rr << std::endl;
          d_domain[v].push_back( (int)rr );
          if( rr<=0 ){
            return 0;
          }
        }else{
          Trace("fmf-incomplete") << "Incomplete because of integer quantification, bounds are too big for " << d_owner[0][v] << "." << std::endl;
          return -1;
        }
      }
    }else if( d_enum_type[v]==ENUM_SET_MEMBERS ){ 
      Assert( d_qe->getBoundedIntegers()->getBoundVarType( d_owner, d_owner[0][v] )==quantifiers::BoundedIntegers::BOUND_SET_MEMBER );
      Node srv = d_qe->getBoundedIntegers()->getSetRangeValue( d_owner, d_owner[0][v], this );
      if( srv.isNull() ){
        return -1;
      }
      Trace("bound-int-rsi") << "Bounded by set membership : " << srv << std::endl;
      d_domain[v].clear();
      d_setm_bounds[v].clear();
      if( srv.getKind()!=EMPTYSET ){
        while( srv.getKind()==UNION ){
          Assert( srv[1].getKind()==kind::SINGLETON );
          d_setm_bounds[v].push_back( srv[1][0] );
          srv = srv[0];
        }
        Assert( srv.getKind()==kind::SINGLETON );
        d_setm_bounds[v].push_back( srv[0] );
        d_domain[v].push_back( d_setm_bounds[v].size() );
      }else{
        d_domain[v].push_back( 0 );
        return 0;
      }
    }
  }
  return 1;
}

int RepSetIterator::increment2( int i ){
  Assert( !isFinished() );
#ifdef DISABLE_EVAL_SKIP_MULTIPLE
  i = (int)d_index.size()-1;
#endif
  //increment d_index
  if( i>=0){
    Trace("rsi-debug") << "domain size of " << i << " is " << domainSize(i) << std::endl;
  }
  while( i>=0 && d_index[i]>=(int)(domainSize(i)-1) ){
    i--;
    if( i>=0){
      Trace("rsi-debug") << "domain size of " << i << " is " << domainSize(i) << std::endl;
    }
  }
  if( i==-1 ){
    d_index.clear();
    return -1;
  }else{
    Trace("rsi-debug") << "increment " << i << std::endl;
    d_index[i]++;
    return do_reset_increment( i );
  }
}

int RepSetIterator::do_reset_increment( int i, bool initial ) {
  bool emptyDomain = false;
  for( unsigned ii=(i+1); ii<d_index.size(); ii++ ){
    int ri_res = resetIndex( ii, initial );
    if( ri_res==-1 ){
      //failed
      d_index.clear();
      d_incomplete = true;
      break;
    }else if( ri_res==0 ){
      emptyDomain = true;
    }
    //force next iteration if currently an empty domain
    if( emptyDomain ){
      d_index[ii] = domainSize(ii)-1;
    }
  }
  if( emptyDomain ){
    Trace("rsi-debug") << "This is an empty domain, increment." << std::endl;
    return increment();
  }else{
    return i;
  }
}

int RepSetIterator::increment(){
  if( !isFinished() ){
    return increment2( (int)d_index.size()-1 );
  }else{
    return -1;
  }
}

bool RepSetIterator::isFinished(){
  return d_index.empty();
}

Node RepSetIterator::getCurrentTerm( int v ){
  Trace("rsi-debug") << "rsi : get term " << v << ", index order = " << d_index_order[v] << std::endl;
  int ii = d_index_order[v];
  int curr = d_index[ii];
  if( d_enum_type[v]==ENUM_DOMAIN_ELEMENTS ){
    TypeNode tn = d_types[v];
    Assert( d_rep_set->d_type_reps.find( tn )!=d_rep_set->d_type_reps.end() );
    Assert( 0<=d_domain[v][curr] && d_domain[v][curr]<(int)d_rep_set->d_type_reps[tn].size() );
    return d_rep_set->d_type_reps[tn][d_domain[v][curr]];
  }else if( d_enum_type[v]==ENUM_SET_MEMBERS ){
    Assert( 0<=curr && curr<(int)d_setm_bounds[v].size() );
    return d_setm_bounds[v][curr];
  }else{
    Trace("rsi-debug") << "Get, with offset : " << v << " " << d_lower_bounds[v] << " " << curr << std::endl;
    Assert( !d_lower_bounds[v].isNull() );
    Node t = NodeManager::currentNM()->mkNode(PLUS, d_lower_bounds[v], NodeManager::currentNM()->mkConst( Rational(curr) ) );
    t = Rewriter::rewrite( t );
    return t;
  }
}

void RepSetIterator::debugPrint( const char* c ){
  for( unsigned v=0; v<d_index.size(); v++ ){
    Debug( c ) << v << " : " << getCurrentTerm( v ) << std::endl;
  }
}

void RepSetIterator::debugPrintSmall( const char* c ){
  Debug( c ) << "RI: ";
  for( unsigned v=0; v<d_index.size(); v++ ){
    Debug( c ) << v << ": " << getCurrentTerm( v ) << " ";
  }
  Debug( c ) << std::endl;
}

