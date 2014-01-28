/*********************                                                        */
/*! \file inst_match.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Clark Barrett, Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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

InstMatch::InstMatch( Node f ) {
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

void InstMatch::makeComplete( Node f, QuantifiersEngine* qe ){
  for( unsigned i=0; i<d_vals.size(); i++ ){
    if( d_vals[i].isNull() ){
      Node ic = qe->getTermDatabase()->getInstantiationConstant( f, i );
      d_vals[i] = qe->getTermDatabase()->getFreeVariableForInstConstant( ic );
    }
  }
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
                                  bool modInst, ImtIndexOrder* imtio, bool onlyExist, int index ) {
  if( index==(int)f[0].getNumChildren() || ( imtio && index==(int)imtio->d_order.size() ) ){
    return false;
  }else{
    int i_index = imtio ? imtio->d_order[index] : index;
    Node n = m[i_index];
    std::map< Node, InstMatchTrie >::iterator it = d_data.find( n );
    if( it!=d_data.end() ){
      bool ret = it->second.addInstMatch( qe, f, m, modEq, modInst, imtio, onlyExist, index+1 );
      if( !onlyExist || !ret ){
        return ret;
      }
    }
    /*
    //check if m is an instance of another instantiation if modInst is true
    if( modInst ){
      if( !n.isNull() ){
        Node nl;
        std::map< Node, InstMatchTrie >::iterator itm = d_data.find( nl );
        if( itm!=d_data.end() ){
          if( !itm->second.addInstMatch( qe, f, m, modEq, modInst, imtio, true, index+1 ) ){
            return false;
          }
        }
      }
    }
    */
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
              if( itc->second.addInstMatch( qe, f, m, modEq, modInst, imtio, true, index+1 ) ){
                return false;
              }
            }
          }
          ++eqc;
        }
      }
    }
    if( !onlyExist ){
      d_data[n].addInstMatch( qe, f, m, modEq, modInst, imtio, false, index+1 );
    }
    return true;
  }
}

bool CDInstMatchTrie::addInstMatch( QuantifiersEngine* qe, Node f, std::vector< Node >& m,
                                    context::Context* c, bool modEq, bool modInst, int index, bool onlyExist ){
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
    return false;
  }else{
    Node n = m[ index ];
    std::map< Node, CDInstMatchTrie* >::iterator it = d_data.find( n );
    if( it!=d_data.end() ){
      bool ret = it->second->addInstMatch( qe, f, m, c, modEq, modInst, index+1, onlyExist );
      if( !onlyExist || !ret ){
        return reset || ret;
      }
    }
    //check if m is an instance of another instantiation if modInst is true
    /*
    if( modInst ){
      if( !n.isNull() ){
        Node nl;
        std::map< Node, CDInstMatchTrie* >::iterator itm = d_data.find( nl );
        if( itm!=d_data.end() ){
          if( !itm->second->addInstMatch( qe, f, m, c, modEq, modInst, index+1, true ) ){
            return false;
          }
        }
      }
    }
    */
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
              if( itc->second->addInstMatch( qe, f, m, c, modEq, modInst, index+1, true ) ){
                return false;
              }
            }
          }
          ++eqc;
        }
      }
    }

    if( !onlyExist ){
      std::map< Node, CDInstMatchTrie* >::iterator it = d_data.find( n );
      CDInstMatchTrie* imt = new CDInstMatchTrie( c );
      d_data[n] = imt;
      imt->addInstMatch( qe, f, m, c, modEq, modInst, index+1, false );
    }
    return true;
  }
}

}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
