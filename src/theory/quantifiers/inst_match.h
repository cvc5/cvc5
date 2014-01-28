/*********************                                                        */
/*! \file inst_match.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Francois Bobot, Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief inst match class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INST_MATCH_H
#define __CVC4__THEORY__QUANTIFIERS__INST_MATCH_H

#include "util/hash.h"
#include "context/cdo.h"

#include <ext/hash_set>
#include <map>

#include "context/cdlist.h"
#include "expr/node.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;
class EqualityQuery;

namespace inst {

/** basic class defining an instantiation */
class InstMatch {
public:
  /* map from variable to ground terms */
  std::vector< Node > d_vals;
public:
  InstMatch(){}
  InstMatch( Node f );
  InstMatch( InstMatch* m );

  /** fill all unfilled values with m */
  bool add( InstMatch& m );
  /** if compatible, fill all unfilled values with m and return true
      return false otherwise */
  bool merge( EqualityQuery* q, InstMatch& m );
  /** debug print method */
  void debugPrint( const char* c );
  /** is complete? */
  bool isComplete();
  /** make complete */
  void makeComplete( Node f, QuantifiersEngine* qe );
  /** make representative */
  void makeRepresentative( QuantifiersEngine* qe );
  /** empty */
  bool empty();
  /** clear */
  void clear();
  /** to stream */
  inline void toStream(std::ostream& out) const {
    out << "INST_MATCH( ";
    bool printed = false;
    for( unsigned i=0; i<d_vals.size(); i++ ){
      if( !d_vals[i].isNull() ){
        if( printed ){ out << ", "; }
        out << i << " -> " << d_vals[i];
        printed = true;
      }
    }
    out << " )";
  }
  /** apply rewrite */
  void applyRewrite();
  /** get */
  Node get( int i );
  /** set */
  void setValue( int i, TNode n );
  bool set( QuantifiersEngine* qe, int i, TNode n );
  /* Node used for matching the trigger */
  Node d_matched;
};/* class InstMatch */

inline std::ostream& operator<<(std::ostream& out, const InstMatch& m) {
  m.toStream(out);
  return out;
}

/** trie for InstMatch objects */
class InstMatchTrie {
public:
  class ImtIndexOrder {
  public:
    std::vector< int > d_order;
  };/* class InstMatchTrie ImtIndexOrder */
public:
  /** the data */
  std::map< Node, InstMatchTrie > d_data;
public:
  InstMatchTrie(){}
  ~InstMatchTrie(){}
public:
  /** return true if m exists in this trie
        modEq is if we check modulo equality
        modInst is if we return true if m is an instance of a match that exists
   */
  bool existsInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq = false,
                        bool modInst = false, ImtIndexOrder* imtio = NULL, int index = 0 ) {
    return !addInstMatch( qe, f, m, modEq, modInst, imtio, true, index );
  }
  bool existsInstMatch( QuantifiersEngine* qe, Node f, std::vector< Node >& m, bool modEq = false,
                        bool modInst = false, ImtIndexOrder* imtio = NULL, int index = 0 ) {
    return !addInstMatch( qe, f, m, modEq, modInst, imtio, true, index );
  }
  /** add match m for quantifier f, take into account equalities if modEq = true,
      if imtio is non-null, this is the order to add to trie
      return true if successful
  */
  bool addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq = false,
                     bool modInst = false, ImtIndexOrder* imtio = NULL, bool onlyExist = false, int index = 0 ){
    return addInstMatch( qe, f, m.d_vals, modEq, modInst, imtio, onlyExist, index );
  }
  bool addInstMatch( QuantifiersEngine* qe, Node f, std::vector< Node >& m, bool modEq = false,
                     bool modInst = false, ImtIndexOrder* imtio = NULL, bool onlyExist = false, int index = 0 );
};/* class InstMatchTrie */

/** trie for InstMatch objects */
class CDInstMatchTrie {
public:
  /** the data */
  std::map< Node, CDInstMatchTrie* > d_data;
  /** is valid */
  context::CDO< bool > d_valid;
public:
  CDInstMatchTrie( context::Context* c ) : d_valid( c, false ){}
  ~CDInstMatchTrie(){}
public:
  /** return true if m exists in this trie
        modEq is if we check modulo equality
        modInst is if we return true if m is an instance of a match that exists
   */
  bool existsInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, context::Context* c, bool modEq = false,
                        bool modInst = false, int index = 0 ) {
    return !addInstMatch( qe, f, m, c, modEq, modInst, index, true );
  }
  bool existsInstMatch( QuantifiersEngine* qe, Node f, std::vector< Node >& m, context::Context* c, bool modEq = false,
                        bool modInst = false, int index = 0 ) {
    return !addInstMatch( qe, f, m, c, modEq, modInst, index, true );
  }
  /** add match m for quantifier f, take into account equalities if modEq = true,
      if imtio is non-null, this is the order to add to trie
      return true if successful
  */
  bool addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, context::Context* c, bool modEq = false,
                     bool modInst = false, int index = 0, bool onlyExist = false ) {
    return addInstMatch( qe, f, m.d_vals, c, modEq, modInst, index, onlyExist );
  }
  bool addInstMatch( QuantifiersEngine* qe, Node f, std::vector< Node >& m, context::Context* c, bool modEq = false,
                     bool modInst = false, int index = 0, bool onlyExist = false );
};/* class CDInstMatchTrie */


class InstMatchTrieOrdered{
private:
  InstMatchTrie::ImtIndexOrder* d_imtio;
  InstMatchTrie d_imt;
public:
  InstMatchTrieOrdered( InstMatchTrie::ImtIndexOrder* imtio ) : d_imtio( imtio ){}
  ~InstMatchTrieOrdered(){}
  /** get ordering */
  InstMatchTrie::ImtIndexOrder* getOrdering() { return d_imtio; }
  /** get trie */
  InstMatchTrie* getTrie() { return &d_imt; }
public:
  /** add match m, return true if successful */
  bool addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq = false, bool modInst = false ){
    return d_imt.addInstMatch( qe, f, m, modEq, modInst, d_imtio );
  }
  bool existsInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq = false, bool modInst = false ){
    return d_imt.existsInstMatch( qe, f, m, modEq, modInst, d_imtio );
  }
};/* class InstMatchTrieOrdered */

}/* CVC4::theory::inst namespace */

typedef CVC4::theory::inst::InstMatch InstMatch;

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INST_MATCH_H */
