/*********************                                                        */
/*! \file inst_match.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
  explicit InstMatch( TNode f );
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
  void getTerms( Node f, std::vector< Node >& inst );
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
  /** the data */
  std::map< Node, InstMatchTrie > d_data;
private:
  void print( std::ostream& out, Node q, std::vector< TNode >& terms, bool& firstTime, bool useActive, std::vector< Node >& active ) const;
  void getInstantiations( std::vector< Node >& insts, Node q, std::vector< Node >& terms, QuantifiersEngine * qe, bool useActive, std::vector< Node >& active ) const;
  void getExplanationForInstLemmas( Node q, std::vector< Node >& terms, std::vector< Node >& lems, std::map< Node, Node >& quant, std::map< Node, std::vector< Node > >& tvec ) const;
private:
  void setInstLemma( Node n ){ 
    d_data.clear();
    d_data[n].clear(); 
  }
  bool hasInstLemma() const { return !d_data.empty(); }
  Node getInstLemma() const { return d_data.begin()->first; }
public:
  InstMatchTrie(){}
  ~InstMatchTrie(){}
public:
  /** return true if m exists in this trie
        modEq is if we check modulo equality
        modInst is if we return true if m is an instance of a match that exists
   */
  bool existsInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq = false,
                        ImtIndexOrder* imtio = NULL, int index = 0 ) {
    return !addInstMatch( qe, f, m, modEq, imtio, true, index );
  }
  bool existsInstMatch( QuantifiersEngine* qe, Node f, std::vector< Node >& m, bool modEq = false,
                        ImtIndexOrder* imtio = NULL, int index = 0 ) {
    return !addInstMatch( qe, f, m, modEq, imtio, true, index );
  }
  /** add match m for quantifier f, take into account equalities if modEq = true,
      if imtio is non-null, this is the order to add to trie
      return true if successful
  */
  bool addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq = false,
                     ImtIndexOrder* imtio = NULL, bool onlyExist = false, int index = 0 ){
    return addInstMatch( qe, f, m.d_vals, modEq, imtio, onlyExist, index );
  }
  bool addInstMatch( QuantifiersEngine* qe, Node f, std::vector< Node >& m, bool modEq = false,
                     ImtIndexOrder* imtio = NULL, bool onlyExist = false, int index = 0 );
  bool removeInstMatch( QuantifiersEngine* qe, Node f, std::vector< Node >& m, ImtIndexOrder* imtio = NULL, int index = 0 );
  bool recordInstLemma( Node q, std::vector< Node >& m, Node lem, ImtIndexOrder* imtio = NULL, int index = 0 );
  void print( std::ostream& out, Node q, bool& firstTime, bool useActive, std::vector< Node >& active ) const{
    std::vector< TNode > terms;
    print( out, q, terms, firstTime, useActive, active );
  }
  void getInstantiations( std::vector< Node >& insts, Node q, QuantifiersEngine * qe, bool useActive, std::vector< Node >& active ) {
    std::vector< Node > terms;
    getInstantiations( insts, q, terms, qe, useActive, active );
  }
  void getExplanationForInstLemmas( Node q, std::vector< Node >& lems, std::map< Node, Node >& quant, std::map< Node, std::vector< Node > >& tvec ) const {
    std::vector< Node > terms;
    getExplanationForInstLemmas( q, terms, lems, quant, tvec );
  }  
  void clear() { d_data.clear(); }
};/* class InstMatchTrie */

/** trie for InstMatch objects */
class CDInstMatchTrie {
private:
  /** the data */
  std::map< Node, CDInstMatchTrie* > d_data;
  /** is valid */
  context::CDO< bool > d_valid;
private:
  void print( std::ostream& out, Node q, std::vector< TNode >& terms, bool& firstTime, bool useActive, std::vector< Node >& active ) const;
  void getInstantiations( std::vector< Node >& insts, Node q, std::vector< Node >& terms, QuantifiersEngine * qe, bool useActive, std::vector< Node >& active ) const;
  void getExplanationForInstLemmas( Node q, std::vector< Node >& terms, std::vector< Node >& lems, std::map< Node, Node >& quant, std::map< Node, std::vector< Node > >& tvec ) const;
private:
  void setInstLemma( Node n ){ 
    d_data.clear();
    d_data[n] = NULL; 
  }
  bool hasInstLemma() const { return !d_data.empty(); }
  Node getInstLemma() const { return d_data.begin()->first; }
public:
  CDInstMatchTrie( context::Context* c ) : d_valid( c, false ){}
  ~CDInstMatchTrie();

  /** return true if m exists in this trie
        modEq is if we check modulo equality
        modInst is if we return true if m is an instance of a match that exists
   */
  bool existsInstMatch( QuantifiersEngine* qe, Node q, InstMatch& m, context::Context* c, bool modEq = false,
                        int index = 0 ) {
    return !addInstMatch( qe, q, m, c, modEq, index, true );
  }
  bool existsInstMatch( QuantifiersEngine* qe, Node q, std::vector< Node >& m, context::Context* c, bool modEq = false,
                        int index = 0 ) {
    return !addInstMatch( qe, q, m, c, modEq, index, true );
  }
  /** add match m for quantifier f, take into account equalities if modEq = true,
      if imtio is non-null, this is the order to add to trie
      return true if successful
  */
  bool addInstMatch( QuantifiersEngine* qe, Node q, InstMatch& m, context::Context* c, bool modEq = false,
                     int index = 0, bool onlyExist = false ) {
    return addInstMatch( qe, q, m.d_vals, c, modEq, index, onlyExist );
  }
  bool addInstMatch( QuantifiersEngine* qe, Node q, std::vector< Node >& m, context::Context* c, bool modEq = false,
                     int index = 0, bool onlyExist = false );
  bool removeInstMatch( QuantifiersEngine* qe, Node q, std::vector< Node >& m, int index = 0 );
  bool recordInstLemma( Node q, std::vector< Node >& m, Node lem, int index = 0 );
  void print( std::ostream& out, Node q, bool& firstTime, bool useActive, std::vector< Node >& active ) const{
    std::vector< TNode > terms;
    print( out, q, terms, firstTime, useActive, active );
  }
  void getInstantiations( std::vector< Node >& insts, Node q, QuantifiersEngine * qe, bool useActive, std::vector< Node >& active ) {
    std::vector< Node > terms;
    getInstantiations( insts, q, terms, qe, useActive, active );
  }
  void getExplanationForInstLemmas( Node q, std::vector< Node >& lems, std::map< Node, Node >& quant, std::map< Node, std::vector< Node > >& tvec ) const {
    std::vector< Node > terms;
    getExplanationForInstLemmas( q, terms, lems, quant, tvec );
  }  
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
    return d_imt.addInstMatch( qe, f, m, modEq, d_imtio );
  }
  bool existsInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq = false, bool modInst = false ){
    return d_imt.existsInstMatch( qe, f, m, modEq, d_imtio );
  }
};/* class InstMatchTrieOrdered */

}/* CVC4::theory::inst namespace */

typedef CVC4::theory::inst::InstMatch InstMatch;

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INST_MATCH_H */
