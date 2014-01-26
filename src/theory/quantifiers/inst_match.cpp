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

bool InstMatch::setMatch( EqualityQuery* q, TNode v, TNode m, bool & set ){
  std::map< Node, Node >::iterator vn = d_map.find( v );
  if( !m.isNull() && !m.getType().isSubtypeOf( v.getType() ) ){
    set = false;
    return false;
  }else if( vn==d_map.end() || vn->second.isNull() ){
    set = true;
    this->set(v,m);
    Debug("matching-debug") << "Add partial " << v << "->" << m << std::endl;
    return true;
  }else{
    set = false;
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
  //if( !d_splits.empty() ){
  //  Debug( c ) << "   Conditions: ";
  //  for( std::map< Node, Node >::iterator it = d_splits.begin(); it !=d_splits.end(); ++it ){
  //    Debug( c ) << it->first << " = " << it->second << " ";
  //  }
  //  Debug( c ) << std::endl;
  //}
}

void InstMatch::makeComplete( Node f, QuantifiersEngine* qe ){
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    Node ic = qe->getTermDatabase()->getInstantiationConstant( f, i );
    if( d_map.find( ic )==d_map.end() ){
      d_map[ ic ] = qe->getTermDatabase()->getFreeVariableForInstConstant( ic );
    }
  }
}

//void InstMatch::makeInternalRepresentative( QuantifiersEngine* qe ){
//  EqualityQueryQuantifiersEngine* eqqe = (EqualityQueryQuantifiersEngine*)qe->getEqualityQuery();
//  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
//    d_map[ it->first ] = eqqe->getInternalRepresentative( it->second );
//  }
//}

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
    // For a strange use in inst_match.cpp InstMatchGeneratorSimple::addInstantiations
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




/*
void InstMatchTrie::addInstMatch2( QuantifiersEngine* qe, Node f, InstMatch& m, int index, ImtIndexOrder* imtio ){
  if( long(index)<long(f[0].getNumChildren()) && ( !imtio || long(index)<long(imtio->d_order.size()) ) ){
    int i_index = imtio ? imtio->d_order[index] : index;
    Node n = m.getValue( qe->getTermDatabase()->getInstantiationConstant( f, i_index ) );
    d_data[n].addInstMatch2( qe, f, m, index+1, imtio );
  }
}

bool InstMatchTrie::existsInstMatch2( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, bool modInst, int index, ImtIndexOrder* imtio ){
  if( long(index)==long(f[0].getNumChildren()) || ( imtio && long(index)==long(imtio->d_order.size()) ) ){
    return true;
  }else{
    int i_index = imtio ? imtio->d_order[index] : index;
    Node n = m.getValue( qe->getTermDatabase()->getInstantiationConstant( f, i_index ) );
    std::map< Node, InstMatchTrie >::iterator it = d_data.find( n );
    if( it!=d_data.end() ){
      if( it->second.existsInstMatch2( qe, f, m, modEq, modInst, index+1, imtio ) ){
        return true;
      }
    }
    //check if m is an instance of another instantiation if modInst is true
    if( modInst ){
      if( !n.isNull() ){
        Node nl;
        it = d_data.find( nl );
        if( it!=d_data.end() ){
          if( it->second.existsInstMatch2( qe, f, m, modEq, modInst, index+1, imtio ) ){
            return true;
          }
        }
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
              if( itc->second.existsInstMatch2( qe, f, m, modEq, modInst, index+1, imtio ) ){
                return true;
              }
            }
          }
          ++eqc;
        }
      }
    }
    return false;
  }
}

bool InstMatchTrie::existsInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, bool modInst, ImtIndexOrder* imtio ){
  return existsInstMatch2( qe, f, m, modEq, modInst, 0, imtio );
}

bool InstMatchTrie::addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, bool modInst, ImtIndexOrder* imtio ){
  if( !existsInstMatch( qe, f, m, modEq, modInst, imtio ) ){
    addInstMatch2( qe, f, m, 0, imtio );
    return true;
  }else{
    return false;
  }
}
*/




bool InstMatchTrie::addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, bool modInst, ImtIndexOrder* imtio, bool onlyExist, int index ){
  if( index==(int)f[0].getNumChildren() || ( imtio && index==(int)imtio->d_order.size() ) ){
    return false;
  }else{
    int i_index = imtio ? imtio->d_order[index] : index;
    Node n = m.getValue( qe->getTermDatabase()->getInstantiationConstant( f, i_index ) );
    std::map< Node, InstMatchTrie >::iterator it = d_data.find( n );
    if( it!=d_data.end() ){
      return it->second.addInstMatch( qe, f, m, modEq, modInst, imtio, onlyExist, index+1 );
    }else{

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
}



/** exists match */
bool CDInstMatchTrie::addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, context::Context* c, bool modEq, bool modInst, int index, bool onlyExist ){
  if( !d_valid.get() ){
    if( onlyExist ){
      return false;
    }else{
      d_valid.set( true );
    }
  }
  if( index==(int)f[0].getNumChildren() ){
    return true;
  }else{
    Node n = m.getValue( qe->getTermDatabase()->getInstantiationConstant( f, index ) );
    if( onlyExist ){
      std::map< Node, CDInstMatchTrie* >::iterator it = d_data.find( n );
      if( it!=d_data.end() ){
        if( !it->second->addInstMatch( qe, f, m, c, modEq, modInst, index+1, true ) ){
          return false;
        }
      }
    }
    //check if m is an instance of another instantiation if modInst is true
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
      CDInstMatchTrie* imt;
      if( it!=d_data.end() ){
        imt = it->second;
        it->second->d_valid.set( true );
      }else{
        imt = new CDInstMatchTrie( c );
        d_data[n] = imt;
      }
      return imt->addInstMatch( qe, f, m, c, modEq, modInst, index+1, false );
    }
    return false;
  }
}

}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
