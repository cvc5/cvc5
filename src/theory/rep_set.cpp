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
  d_type_rlv_rep.clear();
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

int RepSet::getNumRelevantGroundReps( TypeNode t ) {
  std::map< TypeNode, int >::iterator it = d_type_rlv_rep.find( t );
  if( it==d_type_rlv_rep.end() ){
    return 0;
  }else{
    return it->second;
  }
}

void RepSet::toStream(std::ostream& out){
#if 0
  for( std::map< TypeNode, std::vector< Node > >::iterator it = d_type_reps.begin(); it != d_type_reps.end(); ++it ){
    out << it->first << " : " << std::endl;
    for( int i=0; i<(int)it->second.size(); i++ ){
      out << "   " << i << ": " << it->second[i] << std::endl;
    }
  }
#else
  for( std::map< TypeNode, std::vector< Node > >::iterator it = d_type_reps.begin(); it != d_type_reps.end(); ++it ){
    if( !it->first.isFunction() && !it->first.isPredicate() ){
      out << "(" << it->first << " " << it->second.size();
      out << " (";
      for( int i=0; i<(int)it->second.size(); i++ ){
        if( i>0 ){ out << " "; }
        out << it->second[i];
      }
      out << ")";
      out << ")" << std::endl;
    }
  }
#endif
}


RepSetIterator::RepSetIterator( QuantifiersEngine * qe, RepSet* rs ) : d_qe(qe), d_rep_set( rs ){
  d_incomplete = false;
}

int RepSetIterator::domainSize( int i ) {
  Assert(i>=0);
  if( d_enum_type[i]==ENUM_DOMAIN_ELEMENTS ){
    return d_domain[i].size();
  }else{
    return d_domain[i][0];
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
  for( size_t i=0; i<d_types.size(); i++ ){
    d_index.push_back( 0 );
    //store default index order
    d_index_order.push_back( i );
    d_var_order[i] = i;
    //store default domain
    d_domain.push_back( RepDomain() );
    TypeNode tn = d_types[i];
    Trace("rsi") << "Var #" << i << " is type " << tn << "..." << std::endl;
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
    }else if( tn.isInteger() ){
      bool inc = false;
      //check if it is bound
      if( d_owner.getKind()==FORALL && d_qe && d_qe->getBoundedIntegers() ){
        if( d_qe->getBoundedIntegers()->isBoundVar( d_owner, d_owner[0][i] ) ){
          Trace("rsi") << "  variable is bounded integer." << std::endl;
          d_enum_type.push_back( ENUM_RANGE );
        }else{
          inc = true;
        }
      }else{
        inc = true;
      }
      if( inc ){
        //check if it is otherwise bound
        if( d_bounds[0].find(i)!=d_bounds[0].end() && d_bounds[1].find(i)!=d_bounds[1].end() ){
          Trace("rsi") << "  variable is bounded." << std::endl;
          d_enum_type.push_back( ENUM_RANGE );
        }else{
          Trace("rsi") << "  variable cannot be bounded." << std::endl;
          Trace("fmf-incomplete") << "Incomplete because of integer quantification of " << d_owner[0][i] << "." << std::endl;
          d_incomplete = true;
        }
      }
    //enumerate if the sort is reasonably small
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
    //if we have yet to determine the type of enumeration
    if( d_enum_type.size()<=i ){
      d_enum_type.push_back( ENUM_DOMAIN_ELEMENTS );
      if( d_rep_set->hasType( tn ) ){
        for( size_t j=0; j<d_rep_set->d_type_reps[tn].size(); j++ ){
          d_domain[i].push_back( j );
        }
      }else{
        return false;
      }
    }
  }
  //must set a variable index order based on bounded integers
  if (d_owner.getKind()==FORALL && d_qe && d_qe->getBoundedIntegers()) {
    Trace("bound-int-rsi") << "Calculating variable order..." << std::endl;
    std::vector< int > varOrder;
    for( unsigned i=0; i<d_qe->getBoundedIntegers()->getNumBoundVars(d_owner); i++ ){
      varOrder.push_back(d_qe->getBoundedIntegers()->getBoundVarNum(d_owner,i));
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
    setIndexOrder(indexOrder);
  }
  //now reset the indices
  for (unsigned i=0; i<d_index.size(); i++) {
    if (!resetIndex(i, true)){
      break;
    }
  }
  return true;
}

void RepSetIterator::setIndexOrder( std::vector< int >& indexOrder ){
  d_index_order.clear();
  d_index_order.insert( d_index_order.begin(), indexOrder.begin(), indexOrder.end() );
  //make the d_var_order mapping
  for( int i=0; i<(int)d_index_order.size(); i++ ){
    d_var_order[d_index_order[i]] = i;
  }
}
/*
void RepSetIterator::setDomain( std::vector< RepDomain >& domain ){
  d_domain.clear();
  d_domain.insert( d_domain.begin(), domain.begin(), domain.end() );
  //we are done if a domain is empty
  for( int i=0; i<(int)d_domain.size(); i++ ){
    if( d_domain[i].empty() ){
      d_index.clear();
    }
  }
}
*/
bool RepSetIterator::resetIndex( int i, bool initial ) {
  d_index[i] = 0;
  int ii = d_index_order[i];
  Trace("bound-int-rsi") << "Reset " << i << " " << ii << " " << initial << std::endl;
  //determine the current range
  if( d_enum_type[ii]==ENUM_RANGE ){
    if( initial || ( d_qe->getBoundedIntegers() && !d_qe->getBoundedIntegers()->isGroundRange( d_owner, d_owner[0][ii] ) ) ){
      Trace("bound-int-rsi") << "Getting range of " << d_owner[0][ii] << std::endl;
      Node actual_l;
      Node l, u;
      if( d_qe->getBoundedIntegers() && d_qe->getBoundedIntegers()->isBoundVar( d_owner, d_owner[0][ii] ) ){
        d_qe->getBoundedIntegers()->getBoundValues( d_owner, d_owner[0][ii], this, l, u );
      }
      for( unsigned b=0; b<2; b++ ){
        if( d_bounds[b].find(ii)!=d_bounds[b].end() ){
          Trace("bound-int-rsi") << "May further limit bound(" << b << ") based on " << d_bounds[b][ii] << std::endl;
          if( b==0 && (l.isNull() || d_bounds[b][ii].getConst<Rational>() > l.getConst<Rational>()) ){
            if( !l.isNull() ){
              //bound was limited externally, record that the value lower bound is not equal to the term lower bound
              actual_l = NodeManager::currentNM()->mkNode( MINUS, d_bounds[b][ii], l );
            }
            l = d_bounds[b][ii];
          }else if( b==1 && (u.isNull() || d_bounds[b][ii].getConst<Rational>() <= u.getConst<Rational>()) ){
            u = NodeManager::currentNM()->mkNode( MINUS, d_bounds[b][ii],
                                                  NodeManager::currentNM()->mkConst( Rational(1) ) );
            u = Rewriter::rewrite( u );
          }
        }
      }

      if( l.isNull() || u.isNull() ){
        //failed, abort the iterator
        d_index.clear();
        return false;
      }else{
        Trace("bound-int-rsi") << "Can limit bounds of " << d_owner[0][ii] << " to " << l << "..." << u << std::endl;
        Node range = Rewriter::rewrite( NodeManager::currentNM()->mkNode( MINUS, u, l ) );
        Node ra = Rewriter::rewrite( NodeManager::currentNM()->mkNode( LEQ, range, NodeManager::currentNM()->mkConst( Rational( 9999 ) ) ) );
        d_domain[ii].clear();
        Node tl = l;
        Node tu = u;
        if( d_qe->getBoundedIntegers() && d_qe->getBoundedIntegers()->isBoundVar( d_owner, d_owner[0][ii] ) ){
          d_qe->getBoundedIntegers()->getBounds( d_owner, d_owner[0][ii], this, tl, tu );
        }
        d_lower_bounds[ii] = tl;
        if( !actual_l.isNull() ){
          //if bound was limited externally, must consider the offset
          d_lower_bounds[ii] = Rewriter::rewrite( NodeManager::currentNM()->mkNode( PLUS, tl, actual_l ) );
        }
        if( ra==NodeManager::currentNM()->mkConst(true) ){
          long rr = range.getConst<Rational>().getNumerator().getLong()+1;
          Trace("bound-int-rsi")  << "Actual bound range is " << rr << std::endl;
          d_domain[ii].push_back( (int)rr );
        }else{
          Trace("fmf-incomplete") << "Incomplete because of integer quantification, bounds are too big for " << d_owner[0][ii] << "." << std::endl;
          d_incomplete = true;
          d_domain[ii].push_back( 0 );
        }
      }
    }else{
      Trace("bound-int-rsi") << d_owner[0][ii] << " has ground range, skip." << std::endl;
    }
  }
  return true;
}

int RepSetIterator::increment2( int counter ){
  Assert( !isFinished() );
#ifdef DISABLE_EVAL_SKIP_MULTIPLE
  counter = (int)d_index.size()-1;
#endif
  //increment d_index
  if( counter>=0){
    Trace("rsi-debug") << "domain size of " << counter << " is " << domainSize(counter) << std::endl;
  }
  while( counter>=0 && d_index[counter]>=(int)(domainSize(counter)-1) ){
    counter--;
    if( counter>=0){
      Trace("rsi-debug") << "domain size of " << counter << " is " << domainSize(counter) << std::endl;
    }
  }
  if( counter==-1 ){
    d_index.clear();
  }else{
    d_index[counter]++;
    bool emptyDomain = false;
    for( int i=(int)d_index.size()-1; i>counter; i-- ){
      if (!resetIndex(i)){
        break;
      }else if( domainSize(i)<=0 ){
        emptyDomain = true;
      }
    }
    if( emptyDomain ){
      Trace("rsi-debug") << "This is an empty domain, increment again." << std::endl;
      return increment();
    }
  }
  return counter;
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

Node RepSetIterator::getTerm( int i ){
  Trace("rsi-debug") << "rsi : get term " << i << ", index order = " << d_index_order[i] << std::endl;
  //int index = d_index_order[i];
  int index = i;
  if( d_enum_type[index]==ENUM_DOMAIN_ELEMENTS ){
    TypeNode tn = d_types[index];
    Assert( d_rep_set->d_type_reps.find( tn )!=d_rep_set->d_type_reps.end() );
    return d_rep_set->d_type_reps[tn][d_domain[index][d_index[index]]];
  }else{
    Trace("rsi-debug") << "Get, with offset : " << index << " " << d_lower_bounds[index] << " " << d_index[index] << std::endl;
    Node t = NodeManager::currentNM()->mkNode(PLUS, d_lower_bounds[index],
                                                    NodeManager::currentNM()->mkConst( Rational(d_index[index]) ) );
    t = Rewriter::rewrite( t );
    return t;
  }
}

void RepSetIterator::debugPrint( const char* c ){
  for( int i=0; i<(int)d_index.size(); i++ ){
    Debug( c ) << i << " : " << d_index[i] << " : " << getTerm( i ) << std::endl;
  }
}

void RepSetIterator::debugPrintSmall( const char* c ){
  Debug( c ) << "RI: ";
  for( int i=0; i<(int)d_index.size(); i++ ){
    Debug( c ) << d_index[i] << ": " << getTerm( i ) << " ";
  }
  Debug( c ) << std::endl;
}
