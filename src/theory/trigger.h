/*********************                                                        */
/*! \file trigger.h
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
 ** \brief trigger class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__TRIGGER_H
#define __CVC4__TRIGGER_H

#include "theory/inst_match.h"

namespace CVC4 {
namespace theory {

//a collect of nodes representing a trigger
class Trigger {
private:
  /** computation of variable contains */
  static std::map< TNode, std::vector< TNode > > d_var_contains;
  static void computeVarContains( Node n );
  static void computeVarContains2( Node n, Node parent );
private:
  /** the quantifiers engine */
  QuantifiersEngine* d_quantEngine;
  /** the quantifier this trigger is for */
  Node d_f;
  /** match generators */
  IMGenerator* d_mg;
private:
  /** a trie of triggers */
  class TrTrie {
  private:
    Trigger* getTrigger2( std::vector< Node >& nodes );
    void addTrigger2( std::vector< Node >& nodes, Trigger* t );
  public:
    TrTrie() : d_tr( NULL ){}
    Trigger* d_tr;
    std::map< TNode, TrTrie* > d_children;
    Trigger* getTrigger( std::vector< Node >& nodes ){
      std::vector< Node > temp;
      temp.insert( temp.begin(), nodes.begin(), nodes.end() );
      std::sort( temp.begin(), temp.end() );
      return getTrigger2( temp );
    }
    void addTrigger( std::vector< Node >& nodes, Trigger* t ){
      std::vector< Node > temp;
      temp.insert( temp.begin(), nodes.begin(), nodes.end() );
      std::sort( temp.begin(), temp.end() );
      return addTrigger2( temp, t );
    }
  };/* class Trigger::TrTrie */
  /** all triggers will be stored in this trie */
  static TrTrie d_tr_trie;
private:
  /** trigger constructor */
  Trigger( QuantifiersEngine* ie, Node f, std::vector< Node >& nodes, int matchOption = 0, bool smartTriggers = false );
public:
  ~Trigger(){}
public:
  std::vector< Node > d_nodes;
public:
  void debugPrint( const char* c );
  IMGenerator* getGenerator() { return d_mg; }
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound();
  /** reset, eqc is the equivalence class to search in (search in any if eqc=null) */
  void reset( Node eqc );
  /** get next match.  must call reset( eqc ) once before this function. */
  bool getNextMatch( InstMatch& m );
  /** get the match against ground term or formula t.
      the trigger and t should have the same shape.
      Currently the trigger should not be a multi-trigger.
  */
  bool getMatch( Node t, InstMatch& m);
  /** add ground term t, called when t is added to the TermDb */
  int addTerm( Node t );
  /** return true if whatever Node is subsituted for the variables the
      given Node can't match the pattern */
  bool nonunifiable( TNode t, const std::vector<Node> & vars){
    return d_mg->nonunifiable(t,vars);
  }
  /** return whether this is a multi-trigger */
  bool isMultiTrigger() { return d_nodes.size()>1; }
public:
  /** add all available instantiations exhaustively, in any equivalence class
      if limitInst>0, limitInst is the max # of instantiations to try */
  int addInstantiations( InstMatch& baseMatch, int instLimit = 0, bool addSplits = false );
  /** mkTrigger method
     ie     : quantifier engine;
     f      : forall something ....
     nodes  : (multi-)trigger
     matchOption : which policy to use for creating matches (one of InstMatchGenerator::MATCH_GEN_* )
     keepAll: don't remove unneeded patterns;
     trOption : policy for dealing with triggers that already existed (see below)
  */
  enum{
    TR_MAKE_NEW,    //make new trigger even if it already may exist
    TR_GET_OLD,     //return a previous trigger if it had already been created
    TR_RETURN_NULL  //return null if a duplicate is found
  };
  static Trigger* mkTrigger( QuantifiersEngine* qe, Node f, std::vector< Node >& nodes,
                             int matchOption = 0, bool keepAll = true, int trOption = TR_MAKE_NEW,
                             bool smartTriggers = false );
  static Trigger* mkTrigger( QuantifiersEngine* qe, Node f, Node n,
                             int matchOption = 0, bool keepAll = true, int trOption = TR_MAKE_NEW,
                             bool smartTriggers = false );
private:
  /** is subterm of trigger usable */
  static bool isUsable( Node n, Node f );
  /** collect all APPLY_UF pattern terms for f in n */
  static bool collectPatTerms2( QuantifiersEngine* qe, Node f, Node n, std::map< Node, bool >& patMap, int tstrt );
public:
  //different strategies for choosing trigger terms
  enum {
    TS_MAX_TRIGGER = 0,
    TS_MIN_TRIGGER,
    TS_ALL,
  };
  static void collectPatTerms( QuantifiersEngine* qe, Node f, Node n, std::vector< Node >& patTerms, int tstrt, bool filterInst = false );
public:
  /** is usable trigger */
  static bool isUsableTrigger( std::vector< Node >& nodes, Node f );
  static bool isUsableTrigger( Node n, Node f );
  static bool isAtomicTrigger( Node n );
  static bool isSimpleTrigger( Node n );
  /** filter all nodes that have instances */
  static void filterInstances( std::vector< Node >& nodes );
  /** -1: n1 is an instance of n2, 1: n1 is an instance of n2 */
  static int isInstanceOf( Node n1, Node n2 );
  /** variables subsume, return true if n1 contains all free variables in n2 */
  static bool isVariableSubsume( Node n1, Node n2 );
  /** get var contains */
  static void getVarContains( Node f, std::vector< Node >& pats, std::map< Node, std::vector< Node > >& varContains );
  static void getVarContainsNode( Node f, Node n, std::vector< Node >& varContains );
  /** get pattern arithmetic */
  static bool getPatternArithmetic( Node f, Node n, std::map< Node, Node >& coeffs );

  inline void toStream(std::ostream& out) const {
    out << "TRIGGER( ";
    for( int i=0; i<(int)d_nodes.size(); i++ ){
      if( i>0 ){ out << ", "; }
      out << d_nodes[i];
    }
    out << " )";
  }
};

inline std::ostream& operator<<(std::ostream& out, const Trigger & tr) {
  tr.toStream(out);
  return out;
}

}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif /* __CVC4__TRIGGER_H */
