/*********************                                                        */
/*! \file inst_match_generator.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief inst match generator class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_H
#define __CVC4__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_H

#include "theory/quantifiers/inst_match.h"
#include <map>

namespace CVC4 {
namespace theory {

class QuantifiersEngine;
namespace quantifiers{
  class TermArgTrie;
}

namespace inst {

/** base class for producing InstMatch objects */
class IMGenerator {
public:
  /** reset instantiation round (call this at beginning of instantiation round) */
  virtual void resetInstantiationRound( QuantifiersEngine* qe ) = 0;
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  virtual void reset( Node eqc, QuantifiersEngine* qe ) = 0;
  /** get the next match.  must call reset( eqc ) before this function. */
  virtual bool getNextMatch( Node f, InstMatch& m, QuantifiersEngine* qe ) = 0;
  /** add instantiations directly */
  virtual int addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe ) = 0;
  /** add ground term t, called when t is added to term db */
  virtual int addTerm( Node f, Node t, QuantifiersEngine* qe ) = 0;
  /** set active add */
  virtual void setActiveAdd( bool val ) {}
};/* class IMGenerator */

class CandidateGenerator;

class InstMatchGenerator : public IMGenerator {
private:
  bool d_needsReset;
  /** candidate generator */
  CandidateGenerator* d_cg;
  /** policy to use for matching */
  int d_matchPolicy;
  /** children generators */
  std::vector< InstMatchGenerator* > d_children;
  std::vector< int > d_children_index;
  /** the next generator in order */
  InstMatchGenerator* d_next;
  /** eq class */
  Node d_eq_class;
  /** for arithmetic matching */
  std::map< Node, Node > d_arith_coeffs;
  /** variable numbers */
  std::map< int, int > d_var_num;
  /** initialize pattern */
  void initialize( QuantifiersEngine* qe, std::vector< InstMatchGenerator * > & gens );
public:
  enum {
    //options for producing matches
    MATCH_GEN_DEFAULT = 0,
    MATCH_GEN_EFFICIENT_E_MATCH,   //generate matches via Efficient E-matching for SMT solvers
    //others (internally used)
    MATCH_GEN_INTERNAL_ERROR,
  };
public:
  /** get the match against ground term or formula t.
      d_match_pattern and t should have the same shape.
      only valid for use where !d_match_pattern.isNull().
  */
  bool getMatch( Node f, Node t, InstMatch& m, QuantifiersEngine* qe );

  /** constructors */
  InstMatchGenerator( Node pat, int matchOption = 0 );
  /** destructor */
  ~InstMatchGenerator(){}
  /** The pattern we are producing matches for.
      If null, this is a multi trigger that is merging matches from d_children.
  */
  Node d_pattern;
  /** match pattern */
  Node d_match_pattern;
  /** match pattern op */
  Node d_match_pattern_op;
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe );
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  void reset( Node eqc, QuantifiersEngine* qe );
  /** get the next match.  must call reset( eqc ) before this function. */
  bool getNextMatch( Node f, InstMatch& m, QuantifiersEngine* qe );
  /** add instantiations */
  int addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe );
  /** add ground term t */
  int addTerm( Node f, Node t, QuantifiersEngine* qe );

  bool d_active_add;
  void setActiveAdd( bool val );

  static InstMatchGenerator* mkInstMatchGenerator( Node pat, QuantifiersEngine* qe );
  static InstMatchGenerator* mkInstMatchGenerator( std::vector< Node >& pats, QuantifiersEngine* qe );
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
  bool getNextMatch( Node f, InstMatch& m, QuantifiersEngine* qe ) { return false; }
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
  /** operator */
  Node d_op;
  /** to indicies */
  std::map< int, int > d_var_num;
  /** add instantiations */
  void addInstantiations( InstMatch& m, QuantifiersEngine* qe, int& addedLemmas, int argIndex, quantifiers::TermArgTrie* tat );
public:
  /** constructors */
  InstMatchGeneratorSimple( Node f, Node pat );
  /** destructor */
  ~InstMatchGeneratorSimple(){}
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe );
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  void reset( Node eqc, QuantifiersEngine* qe ) {}
  /** get the next match.  must call reset( eqc ) before this function. (not implemented) */
  bool getNextMatch( Node f, InstMatch& m, QuantifiersEngine* qe ) { return false; }
  /** add instantiations */
  int addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe );
  /** add ground term t, possibly add instantiations */
  int addTerm( Node f, Node t, QuantifiersEngine* qe );
};/* class InstMatchGeneratorSimple */

}
}
}

#endif
