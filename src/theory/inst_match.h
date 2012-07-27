/*********************                                                        */
/*! \file inst_match.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief inst match class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__INST_MATCH_H
#define __CVC4__INST_MATCH_H

#include "theory/theory.h"
#include "util/hash.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "context/cdlist.h"

//#define USE_EFFICIENT_E_MATCHING

namespace CVC4 {
namespace theory {

/** Attribute true for nodes that should not be used for matching */
struct NoMatchAttributeId {};
/** use the special for boolean flag */
typedef expr::Attribute< NoMatchAttributeId,
                         bool,
                         expr::attr::NullCleanupStrategy,
                         true // context dependent
                       > NoMatchAttribute;

// attribute for "contains instantiation constants from"
struct InstConstantAttributeId {};
typedef expr::Attribute<InstConstantAttributeId, Node> InstConstantAttribute;

struct InstLevelAttributeId {};
typedef expr::Attribute<InstLevelAttributeId, uint64_t> InstLevelAttribute;

struct InstVarNumAttributeId {};
typedef expr::Attribute<InstVarNumAttributeId, uint64_t> InstVarNumAttribute;

// Attribute that tell if a node have been asserted in this branch
struct AvailableInTermDbId {};
/** use the special for boolean flag */
typedef expr::Attribute<AvailableInTermDbId,
                        bool,
                        expr::attr::NullCleanupStrategy,
                        true  // context dependent
                        > AvailableInTermDb;


class QuantifiersEngine;
namespace quantifiers{
  class TermArgTrie;
}

namespace uf{
  class InstantiatorTheoryUf;
  class TheoryUF;
}/* CVC4::theory::uf namespace */

namespace inst {

class CandidateGenerator
{
public:
  CandidateGenerator(){}
  ~CandidateGenerator(){}

  /** Get candidates functions.  These set up a context to get all match candidates.
      cg->reset( eqc );
      do{
        Node cand = cg->getNextCandidate();
        //.......
      }while( !cand.isNull() );

      eqc is the equivalence class you are searching in
  */
  virtual void reset( Node eqc ) = 0;
  virtual Node getNextCandidate() = 0;
  /** add candidate to list of nodes returned by this generator */
  virtual void addCandidate( Node n ) {}
  /** call this at the beginning of each instantiation round */
  virtual void resetInstantiationRound() = 0;
public:
  /** legal candidate */
  static bool isLegalCandidate( Node n );
};/* class CandidateGenerator */

/** candidate generator queue (for manual candidate generation) */
class CandidateGeneratorQueue : public CandidateGenerator {
private:
  std::vector< Node > d_candidates;
  int d_candidate_index;
public:
  CandidateGeneratorQueue() : d_candidate_index( 0 ){}
  ~CandidateGeneratorQueue(){}

  void addCandidate( Node n );

  void resetInstantiationRound(){}
  void reset( Node eqc );
  Node getNextCandidate();
};/* class CandidateGeneratorQueue */

class EqualityQuery {
public:
  EqualityQuery(){}
  virtual ~EqualityQuery(){};
  /** contains term */
  virtual bool hasTerm( Node a ) = 0;
  /** get the representative of the equivalence class of a */
  virtual Node getRepresentative( Node a ) = 0;
  /** returns true if a and b are equal in the current context */
  virtual bool areEqual( Node a, Node b ) = 0;
  /** returns true is a and b are disequal in the current context */
  virtual bool areDisequal( Node a, Node b ) = 0;
  /** getInternalRepresentative gets the current best representative in the equivalence class of a, based on some criteria.
      If cbqi is active, this will return a term in the equivalence class of "a" that does
      not contain instantiation constants, if such a term exists.
   */
  virtual Node getInternalRepresentative( Node a ) = 0;
};/* class EqualityQuery */

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
  /** make complete */
  void makeComplete( Node f, QuantifiersEngine* qe );
  /** make internal: ensure that no term in d_map contains instantiation constants */
  void makeInternal( QuantifiersEngine* qe );
  /** make representative */
  void makeRepresentative( QuantifiersEngine* qe );
  /** apply rewrite */
  void applyRewrite();
  /** compute d_match */
  void computeTermVec( QuantifiersEngine* qe, const std::vector< Node >& vars, std::vector< Node >& match );
  /** compute d_match */
  void computeTermVec( const std::vector< Node >& vars, std::vector< Node >& match );
  /** clear */
  void clear(){ d_map.clear(); }
  /** erase */
  template<class Iterator>
  void erase(Iterator begin, Iterator end){
    for(Iterator i = begin; i != end; ++i){
      d_map.erase(*i);
    };
  }
  void erase(Node node){ d_map.erase(node); }
  /** is_empty */
  bool empty(){ return d_map.empty(); }
  /** set */
  void set(TNode var, TNode n){
    //std::cout << "var.getType() " << var.getType() << "n.getType() " << n.getType() << std::endl ;
    Assert( !var.isNull() );
    Assert( n.isNull() ||// For a strange use in inst_match.cpp InstMatchGeneratorSimple::addInstantiations
            var.getType() == n.getType() );
    d_map[var] = n;
  }
  Node get(TNode var){ return d_map[var]; }
  size_t size(){ return d_map.size(); }
  /* iterator */
  std::map< Node, Node >::iterator begin(){ return d_map.begin(); };
  std::map< Node, Node >::iterator end(){ return d_map.end(); };
  std::map< Node, Node >::iterator find(Node var){ return d_map.find(var); };
  /* Node used for matching the trigger only for mono-trigger (just for
     efficiency because I need only that) */
  Node d_matched;
  /** to stream */
  inline void toStream(std::ostream& out) const {
    out << "INST_MATCH( ";
    for( std::map< Node, Node >::const_iterator it = d_map.begin(); it != d_map.end(); ++it ){
      if( it != d_map.begin() ){ out << ", "; }
      out << it->first << " -> " << it->second;
    }
    out << " )";
  }
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
  bool existsInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, int index, ImtIndexOrder* imtio );
public:
  /** the data */
  std::map< Node, InstMatchTrie > d_data;
public:
  InstMatchTrie(){}
  ~InstMatchTrie(){}
public:
  /** add match m for quantifier f, take into account equalities if modEq = true,
      if imtio is non-null, this is the order to add to trie
      return true if successful
  */
  bool addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq = false, ImtIndexOrder* imtio = NULL );
};/* class InstMatchTrie */

class InstMatchTrieOrdered {
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
  bool addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq = false ){
    return d_imt.addInstMatch( qe, f, m, modEq, d_imtio );
  }
};/* class InstMatchTrieOrdered */

/** base class for producing InstMatch objects */
class IMGenerator {
public:
  /** reset instantiation round (call this at beginning of instantiation round) */
  virtual void resetInstantiationRound( QuantifiersEngine* qe ) = 0;
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  virtual void reset( Node eqc, QuantifiersEngine* qe ) = 0;
  /** get the next match.  must call reset( eqc ) before this function. */
  virtual bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ) = 0;
  /** return true if whatever Node is substituted for the variables the
      given Node can't match the pattern */
  virtual bool nonunifiable( TNode t, const std::vector<Node> & vars) = 0;
  /** add instantiations directly */
  virtual int addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe ) = 0;
  /** add ground term t, called when t is added to term db */
  virtual int addTerm( Node f, Node t, QuantifiersEngine* qe ) = 0;
};/* class IMGenerator */


class InstMatchGenerator : public IMGenerator {
private:
  /** candidate generator */
  CandidateGenerator* d_cg;
  /** policy to use for matching */
  int d_matchPolicy;
  /** children generators */
  std::vector< InstMatchGenerator* > d_children;
  std::vector< int > d_children_index;
  /** partial vector */
  std::vector< InstMatch > d_partial;
  /** eq class */
  Node d_eq_class;
  /** for arithmetic matching */
  std::map< Node, Node > d_arith_coeffs;
  /** initialize pattern */
  void initializePatterns( std::vector< Node >& pats, QuantifiersEngine* qe );
  void initializePattern( Node pat, QuantifiersEngine* qe );
public:
  enum {
    //options for producing matches
    MATCH_GEN_DEFAULT = 0,
    MATCH_GEN_EFFICIENT_E_MATCH,   //generate matches via Efficient E-matching for SMT solvers
    //others (internally used)
    MATCH_GEN_INTERNAL_ARITHMETIC,
    MATCH_GEN_INTERNAL_ERROR,
  };
private:
  /** get the next match.  must call d_cg->reset( ... ) before using.
      only valid for use where !d_match_pattern.isNull().
  */
  bool getNextMatch2( InstMatch& m, QuantifiersEngine* qe, bool saveMatched = false );
  /** for arithmetic */
  bool getMatchArithmetic( Node t, InstMatch& m, QuantifiersEngine* qe );
public:
  /** get the match against ground term or formula t.
      d_match_pattern and t should have the same shape.
      only valid for use where !d_match_pattern.isNull().
  */
  bool getMatch( Node t, InstMatch& m, QuantifiersEngine* qe );

  /** constructors */
  InstMatchGenerator( Node pat, QuantifiersEngine* qe, int matchOption = 0 );
  InstMatchGenerator( std::vector< Node >& pats, QuantifiersEngine* qe, int matchOption = 0 );
  /** destructor */
  ~InstMatchGenerator(){}
  /** The pattern we are producing matches for.
      If null, this is a multi trigger that is merging matches from d_children.
  */
  Node d_pattern;
  /** match pattern */
  Node d_match_pattern;
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe );
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  void reset( Node eqc, QuantifiersEngine* qe );
  /** get the next match.  must call reset( eqc ) before this function. */
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe );
  /** return true if whatever Node is substituted for the variables the
      given Node can't match the pattern */
  bool nonunifiable( TNode t, const std::vector<Node> & vars);
  /** add instantiations */
  int addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe );
  /** add ground term t */
  int addTerm( Node f, Node t, QuantifiersEngine* qe );
};/* class InstMatchGenerator */

/** smart multi-trigger implementation */
class InstMatchGeneratorMulti : public IMGenerator {
private:
  /** indexed trie */
  typedef std::pair< std::pair< int, int >, InstMatchTrie* > IndexedTrie;
  /** process new match */
  void processNewMatch( QuantifiersEngine* qe, InstMatch& m, int fromChildIndex, int& addedLemmas );
  /** process new instantiations */
  void processNewInstantiations( QuantifiersEngine* qe, InstMatch& m, int& addedLemmas, InstMatchTrie* tr,
                                 std::vector< IndexedTrie >& unique_var_tries,
                                 int trieIndex, int childIndex, int endChildIndex, bool modEq );
  /** process new instantiations 2 */
  void processNewInstantiations2( QuantifiersEngine* qe, InstMatch& m, int& addedLemmas,
                                  std::vector< IndexedTrie >& unique_var_tries,
                                  int uvtIndex, InstMatchTrie* tr = NULL, int trieIndex = 0 );
private:
  /** var contains (variable indices) for each pattern node */
  std::map< Node, std::vector< int > > d_var_contains;
  /** variable indices contained to pattern nodes */
  std::map< int, std::vector< Node > > d_var_to_node;
  /** quantifier to use */
  Node d_f;
  /** policy to use for matching */
  int d_matchPolicy;
  /** children generators */
  std::vector< InstMatchGenerator* > d_children;
  /** inst match tries for each child */
  std::vector< InstMatchTrieOrdered > d_children_trie;
  /** calculate matches */
  void calculateMatches( QuantifiersEngine* qe );
public:
  /** constructors */
  InstMatchGeneratorMulti( Node f, std::vector< Node >& pats, QuantifiersEngine* qe, int matchOption = 0 );
  /** destructor */
  ~InstMatchGeneratorMulti(){}
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe );
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  void reset( Node eqc, QuantifiersEngine* qe );
  /** get the next match.  must call reset( eqc ) before this function. (not implemented) */
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ) { return false; }
  /** return true if whatever Node is substituted for the variables the
      given Node can't match the pattern */
  bool nonunifiable( TNode t, const std::vector<Node> & vars) { return true; }
  /** add instantiations */
  int addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe );
  /** add ground term t */
  int addTerm( Node f, Node t, QuantifiersEngine* qe );
};/* class InstMatchGeneratorMulti */

/** smart (single)-trigger implementation */
class InstMatchGeneratorSimple : public IMGenerator {
private:
  /** quantifier for match term */
  Node d_f;
  /** match term */
  Node d_match_pattern;
  /** add instantiations */
  void addInstantiations( InstMatch& m, QuantifiersEngine* qe, int& addedLemmas, int argIndex, quantifiers::TermArgTrie* tat );
public:
  /** constructors */
  InstMatchGeneratorSimple( Node f, Node pat ) : d_f( f ), d_match_pattern( pat ){}
  /** destructor */
  ~InstMatchGeneratorSimple(){}
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe ) {}
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  void reset( Node eqc, QuantifiersEngine* qe ) {}
  /** get the next match.  must call reset( eqc ) before this function. (not implemented) */
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ) { return false; }
  /** return true if whatever Node is substituted for the variables the
      given Node can't match the pattern */
  bool nonunifiable( TNode t, const std::vector<Node> & vars) { return true; }
  /** add instantiations */
  int addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe );
  /** add ground term t, possibly add instantiations */
  int addTerm( Node f, Node t, QuantifiersEngine* qe );
};/* class InstMatchGeneratorSimple */

}/* CVC4::theory::inst namespace */

typedef CVC4::theory::inst::InstMatch InstMatch;
typedef CVC4::theory::inst::EqualityQuery EqualityQuery;

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__INST_MATCH_H */
