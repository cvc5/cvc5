/*********************                                                        */
/*! \file inst_match.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inst match class
 **/

#include "theory/quantifiers/inst_match.h"

#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

namespace CVC4 {
namespace theory {
namespace inst {

InstMatch::InstMatch( TNode f ) {
  for( unsigned i=0; i<f[0].getNumChildren(); i++ ){
    d_vals.push_back( Node::null() );
  }
}

InstMatch::InstMatch( InstMatch* m ) {
  d_vals.insert( d_vals.end(), m->d_vals.begin(), m->d_vals.end() );
}

bool InstMatch::add( InstMatch& m ){
  for( unsigned i=0; i<d_vals.size(); i++ ){
    if( d_vals[i].isNull() ){
      d_vals[i] = m.d_vals[i];
    }
  }
  return true;
}

bool InstMatch::merge( EqualityQuery* q, InstMatch& m ){
  for( unsigned i=0; i<m.d_vals.size(); i++ ){
    if( !m.d_vals[i].isNull() ){
      if( d_vals[i].isNull() ){
        d_vals[i] = m.d_vals[i];
      }else{
        if( !q->areEqual( d_vals[i], m.d_vals[i]) ){
          clear();
          return false;
        }
      }
    }
  }
  return true;
}

void InstMatch::debugPrint( const char* c ){
  for( unsigned i=0; i<d_vals.size(); i++ ){
    if( !d_vals[i].isNull() ){
      Debug( c ) << "   " << i << " -> " << d_vals[i] << std::endl;
    }
  }
}

bool InstMatch::isComplete() {
  for( unsigned i=0; i<d_vals.size(); i++ ){
    if( d_vals[i].isNull() ){
      return false;
    }
  }
  return true;
}

bool InstMatch::empty() {
  for( unsigned i=0; i<d_vals.size(); i++ ){
    if( !d_vals[i].isNull() ){
      return false;
    }
  }
  return true;
}

void InstMatch::makeRepresentative( QuantifiersEngine* qe ){
  for( unsigned i=0; i<d_vals.size(); i++ ){
    if( !d_vals[i].isNull() ){
      if( qe->getEqualityQuery()->getEngine()->hasTerm( d_vals[i] ) ){
        d_vals[i] = qe->getEqualityQuery()->getEngine()->getRepresentative( d_vals[i] );
      }
    }
  }
}

void InstMatch::applyRewrite(){
  for( unsigned i=0; i<d_vals.size(); i++ ){
    if( !d_vals[i].isNull() ){
      d_vals[i] = Rewriter::rewrite( d_vals[i] );
    }
  }
}

void InstMatch::clear() {
  for( unsigned i=0; i<d_vals.size(); i++ ){
    d_vals[i] = Node::null();
  }
}

/** get value */

Node InstMatch::get( int i ) {
  return d_vals[i];
}

void InstMatch::getTerms( Node f, std::vector< Node >& inst ){
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    inst.push_back( d_vals[i] );
  }
}

void InstMatch::setValue( int i, TNode n ) {
  d_vals[i] = n;
}

bool InstMatch::set( QuantifiersEngine* qe, int i, TNode n ) {
  Assert( i>=0 );
  if( !d_vals[i].isNull() ){
    if( qe->getEqualityQuery()->areEqual( d_vals[i], n ) ){
      return true;
    }else{
      return false;
    }
  }else{
    d_vals[i] = n;
    return true;
  }
}

}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
