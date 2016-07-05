/*********************                                                        */
/*! \file inst_match.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inst match class
 **/

#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/quant_util.h"
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

bool InstMatchTrie::addInstMatch( QuantifiersEngine* qe, Node f, std::vector< Node >& m, bool modEq,
                                  ImtIndexOrder* imtio, bool onlyExist, int index ) {
  if( index==(int)f[0].getNumChildren() || ( imtio && index==(int)imtio->d_order.size() ) ){
    return false;
  }else{
    int i_index = imtio ? imtio->d_order[index] : index;
    Node n = m[i_index];
    std::map< Node, InstMatchTrie >::iterator it = d_data.find( n );
    if( it!=d_data.end() ){
      bool ret = it->second.addInstMatch( qe, f, m, modEq, imtio, onlyExist, index+1 );
      if( !onlyExist || !ret ){
        return ret;
      }
    }
    if( modEq ){
      //check modulo equality if any other instantiation match exists
      if( !n.isNull() && qe->getEqualityQuery()->getEngine()->hasTerm( n ) ){
        eq::EqClassIterator eqc( qe->getEqualityQuery()->getEngine()->getRepresentative( n ),
                                 qe->getEqualityQuery()->getEngine() );
        while( !eqc.isFinished() ){
          Node en = (*eqc);
          if( en!=n ){
            std::map< Node, InstMatchTrie >::iterator itc = d_data.find( en );
            if( itc!=d_data.end() ){
              if( itc->second.addInstMatch( qe, f, m, modEq, imtio, true, index+1 ) ){
                return false;
              }
            }
          }
          ++eqc;
        }
      }
    }
    if( !onlyExist ){
      d_data[n].addInstMatch( qe, f, m, modEq, imtio, false, index+1 );
    }
    return true;
  }
}

bool InstMatchTrie::removeInstMatch( QuantifiersEngine* qe, Node q, std::vector< Node >& m, ImtIndexOrder* imtio, int index ) {
  Assert( index<(int)q[0].getNumChildren() );
  Assert( !imtio || index<(int)imtio->d_order.size() );
  int i_index = imtio ? imtio->d_order[index] : index;
  Node n = m[i_index];
  std::map< Node, InstMatchTrie >::iterator it = d_data.find( n );
  if( it!=d_data.end() ){
    if( (index+1)==(int)q[0].getNumChildren() || ( imtio && (index+1)==(int)imtio->d_order.size() ) ){
      d_data.erase( n );
      return true;
    }else{
      return it->second.removeInstMatch( qe, q, m, imtio, index+1 );
    }
  }else{
    return false;
  }
}

void InstMatchTrie::print( std::ostream& out, Node q, std::vector< TNode >& terms ) const {
  if( terms.size()==q[0].getNumChildren() ){
    out << "  ( ";
    for( unsigned i=0; i<terms.size(); i++ ){
      if( i>0 ){ out << ", ";}
      out << terms[i];
    }
    out << " )" << std::endl;
  }else{
    for( std::map< Node, InstMatchTrie >::const_iterator it = d_data.begin(); it != d_data.end(); ++it ){
      terms.push_back( it->first );
      it->second.print( out, q, terms );
      terms.pop_back();
    }
  }
}

void InstMatchTrie::getInstantiations( std::vector< Node >& insts, Node q, std::vector< Node >& terms, QuantifiersEngine * qe ) const {
  if( terms.size()==q[0].getNumChildren() ){
    //insts.push_back( q[1].substitute( vars.begin(), vars.end(), terms.begin(), terms.end() ) );
    insts.push_back( qe->getInstantiation( q, terms, true ) );
  }else{
    for( std::map< Node, InstMatchTrie >::const_iterator it = d_data.begin(); it != d_data.end(); ++it ){
      terms.push_back( it->first );
      it->second.getInstantiations( insts, q, terms, qe );
      terms.pop_back();
    }
  }
}

CDInstMatchTrie::~CDInstMatchTrie() {
  for(std::map< Node, CDInstMatchTrie* >::iterator i = d_data.begin(),
          iend = d_data.end(); i != iend; ++i) {
    CDInstMatchTrie* current = (*i).second;
    delete current;
  }
  d_data.clear();
}


bool CDInstMatchTrie::addInstMatch( QuantifiersEngine* qe, Node f, std::vector< Node >& m,
                                    context::Context* c, bool modEq, int index, bool onlyExist ){
  bool reset = false;
  if( !d_valid.get() ){
    if( onlyExist ){
      return true;
    }else{
      d_valid.set( true );
      reset = true;
    }
  }
  if( index==(int)f[0].getNumChildren() ){
    return reset;
  }else{
    Node n = m[ index ];
    std::map< Node, CDInstMatchTrie* >::iterator it = d_data.find( n );
    if( it!=d_data.end() ){
      bool ret = it->second->addInstMatch( qe, f, m, c, modEq, index+1, onlyExist );
      if( !onlyExist || !ret ){
        return reset || ret;
      }
    }
    if( modEq ){
      //check modulo equality if any other instantiation match exists
      if( !n.isNull() && qe->getEqualityQuery()->getEngine()->hasTerm( n ) ){
        eq::EqClassIterator eqc( qe->getEqualityQuery()->getEngine()->getRepresentative( n ),
                                 qe->getEqualityQuery()->getEngine() );
        while( !eqc.isFinished() ){
          Node en = (*eqc);
          if( en!=n ){
            std::map< Node, CDInstMatchTrie* >::iterator itc = d_data.find( en );
            if( itc!=d_data.end() ){
              if( itc->second->addInstMatch( qe, f, m, c, modEq, index+1, true ) ){
                return false;
              }
            }
          }
          ++eqc;
        }
      }
    }

    if( !onlyExist ){
      // std::map< Node, CDInstMatchTrie* >::iterator it = d_data.find( n );
      CDInstMatchTrie* imt = new CDInstMatchTrie( c );
      Assert(d_data.find(n) == d_data.end());
      d_data[n] = imt;
      imt->addInstMatch( qe, f, m, c, modEq, index+1, false );
    }
    return true;
  }
}

bool CDInstMatchTrie::removeInstMatch( QuantifiersEngine* qe, Node q, std::vector< Node >& m, int index ) {
  if( index==(int)q[0].getNumChildren() ){
    if( d_valid.get() ){
      d_valid.set( false );
      return true;
    }else{
      return false;
    }
  }else{
    Node n = m[index];
    std::map< Node, CDInstMatchTrie* >::iterator it = d_data.find( n );
    if( it!=d_data.end() ){
      return it->second->removeInstMatch( qe, q, m, index+1 );
    }else{
      return false;
    }
  }
}

void CDInstMatchTrie::print( std::ostream& out, Node q, std::vector< TNode >& terms ) const{
  if( d_valid.get() ){
    if( terms.size()==q[0].getNumChildren() ){
      out << "  ( ";
      for( unsigned i=0; i<terms.size(); i++ ){
        if( i>0 ) out << ", ";
        out << terms[i];
      }
      out << " )" << std::endl;
    }else{
      for( std::map< Node, CDInstMatchTrie* >::const_iterator it = d_data.begin(); it != d_data.end(); ++it ){
        terms.push_back( it->first );
        it->second->print( out, q, terms );
        terms.pop_back();
      }
    }
  }
}

void CDInstMatchTrie::getInstantiations( std::vector< Node >& insts, Node q, std::vector< Node >& terms, QuantifiersEngine * qe ) const{
  if( d_valid.get() ){
    if( terms.size()==q[0].getNumChildren() ){
      //insts.push_back( q[1].substitute( vars.begin(), vars.end(), terms.begin(), terms.end() ) );
      insts.push_back( qe->getInstantiation( q, terms, true ) );
    }else{
      for( std::map< Node, CDInstMatchTrie* >::const_iterator it = d_data.begin(); it != d_data.end(); ++it ){
        terms.push_back( it->first );
        it->second->getInstantiations( insts, q, terms, qe );
        terms.pop_back();
      }
    }
  }
}

}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
