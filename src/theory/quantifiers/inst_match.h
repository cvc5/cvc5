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
  /* map from variable to ground terms */
  std::map< Node, Node > d_map;
public:
  InstMatch();
  InstMatch( InstMatch* m );

  /** set the match of v to m */
  bool setMatch( EqualityQuery* q, TNode v, TNode m );
  /* This version tell if the variable has been set */
  bool setMatch( EqualityQuery* q, TNode v, TNode m, bool & set);
  /** fill all unfilled values with m */
  bool add( InstMatch& m );
  /** if compatible, fill all unfilled values with m and return true
      return false otherwise */
  bool merge( EqualityQuery* q, InstMatch& m );
  /** debug print method */
  void debugPrint( const char* c );
  /** is complete? */
  bool isComplete( Node f ) { return d_map.size()==f[0].getNumChildren(); }
  /** make complete */
  void makeComplete( Node f, QuantifiersEngine* qe );
  /** make internal representative */
  //void makeInternalRepresentative( QuantifiersEngine* qe );
  /** make representative */
  void makeRepresentative( QuantifiersEngine* qe );
  /** get value */
  Node getValue( Node var ) const;
  /** clear */
  void clear(){ d_map.clear(); }
  /** is_empty */
  bool empty(){ return d_map.empty(); }
  /** to stream */
  inline void toStream(std::ostream& out) const {
    out << "INST_MATCH( ";
    for( std::map< Node, Node >::const_iterator it = d_map.begin(); it != d_map.end(); ++it ){
      if( it != d_map.begin() ){ out << ", "; }
      out << it->first << " -> " << it->second;
    }
    out << " )";
  }


  //for rewrite rules

  /** apply rewrite */
  void applyRewrite();
  /** erase */
  template<class Iterator>
  void erase(Iterator begin, Iterator end){
    for(Iterator i = begin; i != end; ++i){
      d_map.erase(*i);
    };
  }
  void erase(Node node){ d_map.erase(node); }
  /** get */
  Node get( TNode var ) { return d_map[var]; }
  Node get( QuantifiersEngine* qe, Node f, int i );
  /** set */
  void set(TNode var, TNode n);
  void set( QuantifiersEngine* qe, Node f, int i, TNode n );
  /** size */
  size_t size(){ return d_map.size(); }
  /* iterator */
  std::map< Node, Node >::iterator begin(){ return d_map.begin(); };
  std::map< Node, Node >::iterator end(){ return d_map.end(); };
  std::map< Node, Node >::iterator find(Node var){ return d_map.find(var); };
  /* Node used for matching the trigger only for mono-trigger (just for
     efficiency because I need only that) */
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
private:
  /** add match m for quantifier f starting at index, take into account equalities q, return true if successful */
  void addInstMatch2( QuantifiersEngine* qe, Node f, InstMatch& m, int index, ImtIndexOrder* imtio );
  /** exists match */
  bool existsInstMatch2( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, bool modInst, int index, ImtIndexOrder* imtio );
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
                        bool modInst = false, ImtIndexOrder* imtio = NULL );
  /** add match m for quantifier f, take into account equalities if modEq = true,
      if imtio is non-null, this is the order to add to trie
      return true if successful
  */
  bool addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq = false,
                     bool modInst = false, ImtIndexOrder* imtio = NULL );
};/* class InstMatchTrie */


/** trie for InstMatch objects */
class CDInstMatchTrie {
public:
  class ImtIndexOrder {
  public:
    std::vector< int > d_order;
  };/* class InstMatchTrie ImtIndexOrder */
private:
  /** add match m for quantifier f starting at index, take into account equalities q, return true if successful */
  void addInstMatch2( QuantifiersEngine* qe, Node f, InstMatch& m, context::Context* c, int index, ImtIndexOrder* imtio );
  /** exists match */
  bool existsInstMatch2( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, bool modInst, int index, ImtIndexOrder* imtio );
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
  bool existsInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq = false,
                        bool modInst = false, ImtIndexOrder* imtio = NULL );
  /** add match m for quantifier f, take into account equalities if modEq = true,
      if imtio is non-null, this is the order to add to trie
      return true if successful
  */
  bool addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, context::Context* c, bool modEq = false,
                     bool modInst = false, ImtIndexOrder* imtio = NULL );
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
