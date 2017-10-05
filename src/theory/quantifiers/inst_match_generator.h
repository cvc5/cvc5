/*********************                                                        */
/*! \file inst_match_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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

class Trigger;

/** base class for producing InstMatch objects */
class IMGenerator {
public:
  virtual ~IMGenerator() {}
  /** reset instantiation round (call this at beginning of instantiation round) */
  virtual void resetInstantiationRound( QuantifiersEngine* qe ) = 0;
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  virtual bool reset( Node eqc, QuantifiersEngine* qe ) = 0;
  /** get the next match.  must call reset( eqc ) before this function. */
  virtual int getNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent ) = 0;
  /** add instantiations directly */
  virtual int addInstantiations( Node q, InstMatch& baseMatch, QuantifiersEngine* qe, Trigger * tparent ) = 0;
  /** set active add */
  virtual void setActiveAdd( bool val ) {}
  /** get active score */
  virtual int getActiveScore( QuantifiersEngine * qe ) { return 0; }
protected:
  /** send instantiation */
  bool sendInstantiation( Trigger * tparent, InstMatch& m );
};/* class IMGenerator */

class CandidateGenerator;

class InstMatchGenerator : public IMGenerator {
protected:
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
  Node d_eq_class_rel;
  /** variable numbers */
  std::map< int, int > d_var_num;
  /** excluded matches */
  std::map< Node, bool > d_curr_exclude_match;
  /** first candidate */
  Node d_curr_first_candidate;
  /** indepdendent generate (failures should be cached) */
  bool d_independent_gen;
  /** initialize pattern */
  void initialize( Node q, QuantifiersEngine* qe, std::vector< InstMatchGenerator * > & gens, 
                   Trigger * tparent );
  /** children types 0 : variable, 1 : child term, -1 : ground term */
  std::vector< int > d_children_types;
  /** continue */
  int continueNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent );
public:
  enum {
    //options for producing matches
    MATCH_GEN_DEFAULT = 0,
    //others (internally used)
    MATCH_GEN_INTERNAL_ERROR,
  };
public:
  /** get the match against ground term or formula t.
      d_match_pattern and t should have the same shape.
      only valid for use where !d_match_pattern.isNull().
  */
  int getMatch( Node q, Node t, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent );

  /** constructors */
  InstMatchGenerator( Node pat );
  InstMatchGenerator();
  /** destructor */
  virtual ~InstMatchGenerator() throw();
  /** The pattern we are producing matches for.
      If null, this is a multi trigger that is merging matches from d_children.
  */
  Node d_pattern;
  /** match pattern */
  Node d_match_pattern;
  /** match pattern type */
  TypeNode d_match_pattern_type;
  /** match pattern op */
  Node d_match_pattern_op;
  /** what matched */
  Node d_curr_matched;
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe );
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  bool reset( Node eqc, QuantifiersEngine* qe );
  /** get the next match.  must call reset( eqc ) before this function. */
  int getNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent );
  /** add instantiations */
  int addInstantiations( Node q, InstMatch& baseMatch, QuantifiersEngine* qe, Trigger * tparent );

  bool d_active_add;
  void setActiveAdd( bool val );
  int getActiveScore( QuantifiersEngine * qe );
  void excludeMatch( Node n ) { d_curr_exclude_match[n] = true; }
  void setIndependent() { d_independent_gen = true; }

  static InstMatchGenerator* mkInstMatchGenerator( Node q, Node pat, QuantifiersEngine* qe, Trigger * tparent );
  static InstMatchGenerator* mkInstMatchGeneratorMulti( Node q, std::vector< Node >& pats, QuantifiersEngine* qe, 
                                                        Trigger * tparent );
  static InstMatchGenerator* mkInstMatchGenerator( Node q, std::vector< Node >& pats, QuantifiersEngine* qe, 
                                                   std::map< Node, InstMatchGenerator * >& pat_map_init, 
                                                   Trigger * tparent );
};/* class InstMatchGenerator */

//match generator for boolean term ITEs
class VarMatchGeneratorBooleanTerm : public InstMatchGenerator {
public:
  VarMatchGeneratorBooleanTerm( Node var, Node comp );
  virtual ~VarMatchGeneratorBooleanTerm() throw() {}
  Node d_comp;
  bool d_rm_prev;
  /** reset instantiation round (call this at beginning of instantiation round) */
  void resetInstantiationRound( QuantifiersEngine* qe ){}
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  bool reset( Node eqc, QuantifiersEngine* qe ){ 
    d_eq_class = eqc; 
    return true;
  }
  /** get the next match.  must call reset( eqc ) before this function. */
  int getNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent );
  /** add instantiations directly */
  int addInstantiations( Node q, InstMatch& baseMatch, QuantifiersEngine* qe, Trigger * tparent ){ return 0; }
};

//match generator for purified terms (matched term is substituted into d_subs)
class VarMatchGeneratorTermSubs : public InstMatchGenerator {
public:
  VarMatchGeneratorTermSubs( Node var, Node subs );
  virtual ~VarMatchGeneratorTermSubs() throw() {}
  TNode d_var;
  TypeNode d_var_type;
  Node d_subs;
  bool d_rm_prev;
  /** reset instantiation round (call this at beginning of instantiation round) */
  void resetInstantiationRound( QuantifiersEngine* qe ){}
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  bool reset( Node eqc, QuantifiersEngine* qe ){ 
    d_eq_class = eqc; 
    return true;
  }
  /** get the next match.  must call reset( eqc ) before this function. */
  int getNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent );
  /** add instantiations directly */
  int addInstantiations( Node q, InstMatch& baseMatch, QuantifiersEngine* qe, Trigger * tparent ) { return 0; }
};


/** smart multi-trigger implementation */
class InstMatchGeneratorMultiLinear : public InstMatchGenerator {
private:
  int resetChildren( QuantifiersEngine* qe );
public:
  /** constructors */
  InstMatchGeneratorMultiLinear( Node q, std::vector< Node >& pats, QuantifiersEngine* qe );
  /** destructor */
  virtual ~InstMatchGeneratorMultiLinear() throw();
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  bool reset( Node eqc, QuantifiersEngine* qe );
  /** get the next match.  must call reset( eqc ) before this function.*/
  int getNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent );
};/* class InstMatchGeneratorMulti */


/** smart multi-trigger implementation */
class InstMatchGeneratorMulti : public IMGenerator {
private:
  /** indexed trie */
  typedef std::pair< std::pair< int, int >, InstMatchTrie* > IndexedTrie;
  /** process new match */
  void processNewMatch( QuantifiersEngine* qe, Trigger * tparent, InstMatch& m, int fromChildIndex, int& addedLemmas );
  /** process new instantiations */
  void processNewInstantiations( QuantifiersEngine* qe, Trigger * tparent, InstMatch& m, int& addedLemmas, InstMatchTrie* tr,
                                 std::vector< IndexedTrie >& unique_var_tries,
                                 int trieIndex, int childIndex, int endChildIndex, bool modEq );
  /** process new instantiations 2 */
  void processNewInstantiations2( QuantifiersEngine* qe, Trigger * tparent, InstMatch& m, int& addedLemmas,
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
  /** order */
  std::map< unsigned, InstMatchTrie::ImtIndexOrder* > d_imtio;
  /** inst match tries for each child */
  std::vector< InstMatchTrieOrdered > d_children_trie;
  /** calculate matches */
  void calculateMatches( QuantifiersEngine* qe );
public:
  /** constructors */
  InstMatchGeneratorMulti( Node q, std::vector< Node >& pats, QuantifiersEngine* qe, Trigger * tparent );
  /** destructor */
  virtual ~InstMatchGeneratorMulti() throw();
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe );
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  bool reset( Node eqc, QuantifiersEngine* qe );
  /** get the next match.  must call reset( eqc ) before this function. (not implemented) */
  int getNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent ) { return -1; }
  /** add instantiations */
  int addInstantiations( Node q, InstMatch& baseMatch, QuantifiersEngine* qe, Trigger * tparent );
};/* class InstMatchGeneratorMulti */

/** smart (single)-trigger implementation */
class InstMatchGeneratorSimple : public IMGenerator {
private:
  /** quantifier for match term */
  Node d_f;
  /** match term */
  Node d_match_pattern;
  /** equivalence class */
  bool d_pol;
  Node d_eqc;
  /** match pattern arg types */
  std::vector< TypeNode > d_match_pattern_arg_types;
  /** operator */
  Node d_op;
  /** to indicies */
  std::map< int, int > d_var_num;
  /** add instantiations */
  void addInstantiations( InstMatch& m, QuantifiersEngine* qe, 
                          int& addedLemmas, int argIndex, quantifiers::TermArgTrie* tat );
public:
  /** constructors */
  InstMatchGeneratorSimple( Node q, Node pat, QuantifiersEngine* qe );
  /** destructor */
  ~InstMatchGeneratorSimple() throw() {}
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe );
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  bool reset( Node eqc, QuantifiersEngine* qe ) { return true; }
  /** get the next match.  must call reset( eqc ) before this function. (not implemented) */
  int getNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent ) { return -1; }
  /** add instantiations */
  int addInstantiations( Node q, InstMatch& baseMatch, QuantifiersEngine* qe, Trigger * tparent );
  /** get active score */
  int getActiveScore( QuantifiersEngine * qe );
};/* class InstMatchGeneratorSimple */

}
}
}

#endif
