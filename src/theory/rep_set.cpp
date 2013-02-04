/*********************                                                        */
/*! \file rep_set.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds <andrew.j.reynolds@gmail.com>
 ** Major contributors: Morgan Deters <mdeters@cs.nyu.edu>
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of representative set
 **/

#include "theory/rep_set.h"
#include "theory/type_enumerator.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

void RepSet::clear(){
  d_type_reps.clear();
  d_type_complete.clear();
  d_tmap.clear();
}

int RepSet::getNumRepresentatives( TypeNode tn ) const{
  std::map< TypeNode, std::vector< Node > >::const_iterator it = d_type_reps.find( tn );
  if( it!=d_type_reps.end() ){
    return (int)it->second.size();
  }else{
    return 0;
  }
}

void RepSet::add( Node n ){
  TypeNode t = n.getType();
  d_tmap[ n ] = (int)d_type_reps[t].size();
  d_type_reps[t].push_back( n );
}

int RepSet::getIndexFor( Node n ) const {
  std::map< Node, int >::const_iterator it = d_tmap.find( n );
  if( it!=d_tmap.end() ){
    return it->second;
  }else{
    return -1;
  }
}

void RepSet::complete( TypeNode t ){
  if( d_type_complete.find( t )==d_type_complete.end() ){
    d_type_complete[t] = true;
    TypeEnumerator te(t);
    while( !te.isFinished() ){
      Node n = *te;
      if( std::find( d_type_reps[t].begin(), d_type_reps[t].end(), n )==d_type_reps[t].end() ){
        add( n );
      }
      ++te;
    }
    for( size_t i=0; i<d_type_reps[t].size(); i++ ){
      Trace("reps-complete") << d_type_reps[t][i] << " ";
    }
    Trace("reps-complete") << std::endl;
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


RepSetIterator::RepSetIterator( RepSet* rs ) : d_rep_set( rs ){
  d_incomplete = false;

}

bool RepSetIterator::setQuantifier( Node f ){
  Assert( d_types.empty() );
  //store indicies
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    d_types.push_back( f[0][i].getType() );
  }
  return initialize();
}

bool RepSetIterator::setFunctionDomain( Node op ){
  Assert( d_types.empty() );
  TypeNode tn = op.getType();
  for( size_t i=0; i<tn.getNumChildren()-1; i++ ){
    d_types.push_back( tn[i] );
  }
  return initialize();
}

bool RepSetIterator::initialize(){
  for( size_t i=0; i<d_types.size(); i++ ){
    d_index.push_back( 0 );
    //store default index order
    d_index_order.push_back( i );
    d_var_order[i] = i;
    //store default domain
    d_domain.push_back( RepDomain() );
    TypeNode tn = d_types[i];
    if( tn.isSort() ){
      if( !d_rep_set->hasType( tn ) ){
        Node var = NodeManager::currentNM()->mkSkolem( "repSet_$$", tn, "is a variable created by the RepSetIterator" );
        Trace("mkVar") << "RepSetIterator:: Make variable " << var << " : " << tn << std::endl;
        d_rep_set->add( var );
      }
    }else if( tn.isInteger() || tn.isReal() ){
      Trace("fmf-incomplete") << "Incomplete because of infinite type " << tn << std::endl;
      d_incomplete = true;
    }else if( tn.isDatatype() ){
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      //if finite, then complete all values of the domain
      if( dt.isFinite() ){
        d_rep_set->complete( tn );
        //d_incomplete = true;
      }else{
        Trace("fmf-incomplete") << "Incomplete because of infinite datatype " << tn << std::endl;
        d_incomplete = true;
      }
    }else{
      Trace("fmf-incomplete") << "Incomplete because of unknown type " << tn << std::endl;
      d_incomplete = true;
    }
    if( d_rep_set->hasType( tn ) ){
      for( size_t j=0; j<d_rep_set->d_type_reps[tn].size(); j++ ){
        d_domain[i].push_back( j );
      }
    }else{
      return false;
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

void RepSetIterator::increment2( int counter ){
  Assert( !isFinished() );
#ifdef DISABLE_EVAL_SKIP_MULTIPLE
  counter = (int)d_index.size()-1;
#endif
  //increment d_index
  while( counter>=0 && d_index[counter]==(int)(d_domain[counter].size()-1) ){
    counter--;
  }
  if( counter==-1 ){
    d_index.clear();
  }else{
    for( int i=(int)d_index.size()-1; i>counter; i-- ){
      d_index[i] = 0;
    }
    d_index[counter]++;
  }
}

void RepSetIterator::increment(){
  if( !isFinished() ){
    increment2( (int)d_index.size()-1 );
  }
}

bool RepSetIterator::isFinished(){
  return d_index.empty();
}

Node RepSetIterator::getTerm( int i ){
  TypeNode tn = d_types[d_index_order[i]];
  Assert( d_rep_set->d_type_reps.find( tn )!=d_rep_set->d_type_reps.end() );
  int index = d_index_order[i];
  return d_rep_set->d_type_reps[tn][d_domain[index][d_index[index]]];
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
