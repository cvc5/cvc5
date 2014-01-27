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

InstMatch::InstMatch() {
}

InstMatch::InstMatch( InstMatch* m ) {
  d_map = m->d_map;
}

bool InstMatch::setMatch( EqualityQuery* q, TNode v, TNode m, bool & st ){
  std::map< Node, Node >::iterator vn = d_map.find( v );
  if( !m.isNull() && !m.getType().isSubtypeOf( v.getType() ) ){
    st = false;
    return false;
  }else if( vn==d_map.end() || vn->second.isNull() ){
    st = true;
    set(v,m);
    Debug("matching-debug") << "Add partial " << v << "->" << m << std::endl;
    return true;
  }else{
    st = false;
    return q->areEqual( vn->second, m );
  }
}

bool InstMatch::setMatch( EqualityQuery* q, TNode v, TNode m ){
  bool set;
  return setMatch(q,v,m,set);
}

bool InstMatch::add( InstMatch& m ){
  for( std::map< Node, Node >::iterator it = m.d_map.begin(); it != m.d_map.end(); ++it ){
    if( !it->second.isNull() ){
      std::map< Node, Node >::iterator itf = d_map.find( it->first );
      if( itf==d_map.end() || itf->second.isNull() ){
        d_map[it->first] = it->second;
      }
    }
  }
  return true;
}

bool InstMatch::merge( EqualityQuery* q, InstMatch& m ){
  for( std::map< Node, Node >::iterator it = m.d_map.begin(); it != m.d_map.end(); ++it ){
    if( !it->second.isNull() ){
      std::map< Node, Node >::iterator itf = d_map.find( it->first );
      if( itf==d_map.end() || itf->second.isNull() ){
        d_map[ it->first ] = it->second;
      }else{
        if( !q->areEqual( it->second, itf->second ) ){
          d_map.clear();
          return false;
        }
      }
    }
  }
  return true;
}

void InstMatch::debugPrint( const char* c ){
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    Debug( c ) << "   " << it->first << " -> " << it->second << std::endl;
  }
}

void InstMatch::makeComplete( Node f, QuantifiersEngine* qe ){
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    Node ic = qe->getTermDatabase()->getInstantiationConstant( f, i );
    if( d_map.find( ic )==d_map.end() ){
      d_map[ ic ] = qe->getTermDatabase()->getFreeVariableForInstConstant( ic );
    }
  }
}

void InstMatch::makeRepresentative( QuantifiersEngine* qe ){
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    if( qe->getEqualityQuery()->getEngine()->hasTerm( it->second ) ){
      d_map[ it->first ] = qe->getEqualityQuery()->getEngine()->getRepresentative( it->second );
    }
  }
}

void InstMatch::applyRewrite(){
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    it->second = Rewriter::rewrite(it->second);
  }
}

/** get value */
Node InstMatch::getValue( Node var ) const{
  std::map< Node, Node >::const_iterator it = d_map.find( var );
  if( it!=d_map.end() ){
    return it->second;
  }else{
    return Node::null();
  }
}

Node InstMatch::get( QuantifiersEngine* qe, Node f, int i ) {
  return get( qe->getTermDatabase()->getInstantiationConstant( f, i ) );
}

void InstMatch::set(TNode var, TNode n){
  Assert( !var.isNull() );
  if (Trace.isOn("inst-match-warn")) {
    if( !n.isNull() && !n.getType().isSubtypeOf( var.getType() ) ){
      Trace("inst-match-warn") << quantifiers::TermDb::getInstConstAttr(var) << std::endl;
      Trace("inst-match-warn") << var << " " << var.getType() << " " << n << " " << n.getType() << std::endl ;
    }
  }
  Assert( n.isNull() || n.getType().isSubtypeOf( var.getType() ) );
  d_map[var] = n;
}

void InstMatch::set( QuantifiersEngine* qe, Node f, int i, TNode n ) {
  set( qe->getTermDatabase()->getInstantiationConstant( f, i ), n );
}



bool InstMatchTrie::addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m,
                                  bool modEq, bool modInst, ImtIndexOrder* imtio, bool onlyExist, int index ){
  if( index==(int)f[0].getNumChildren() || ( imtio && index==(int)imtio->d_order.size() ) ){
    return false;
  }else{
    int i_index = imtio ? imtio->d_order[index] : index;
    Node n = m.getValue( qe->getTermDatabase()->getInstantiationConstant( f, i_index ) );
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
    /*
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
*/
    if( !onlyExist ){
      d_data[n].addInstMatch( qe, f, m, modEq, modInst, imtio, false, index+1 );
    }
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
    /*
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
    */
    if( !onlyExist ){
      d_data[n].addInstMatch( qe, f, m, modEq, modInst, imtio, false, index+1 );
    }
    return true;
  }
}

/** exists match */
bool CDInstMatchTrie::addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m,
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
    Node n = m.getValue( qe->getTermDatabase()->getInstantiationConstant( f, index ) );
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
