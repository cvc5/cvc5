/*********************                                                        */
/*! \file rr_trigger.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: bobot
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief trigger class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__REWRITERULES__RR_TRIGGER_H
#define __CVC4__THEORY__REWRITERULES__RR_TRIGGER_H

#include "theory/rewriterules/rr_inst_match.h"

namespace CVC4 {
namespace theory {
namespace rrinst {

//a collect of nodes representing a trigger
class Trigger {
public:
  static int trCount;
private:
  /** computation of variable contains */
  static std::map< Node, std::vector< Node > > d_var_contains;
  static void computeVarContains( Node n );
  static void computeVarContains2( Node n, Node parent );
private:
  /** the quantifiers engine */
  QuantifiersEngine* d_quantEngine;
  /** the quantifier this trigger is for */
  Node d_f;
  /** match generators */
  PatsMatcher * d_mg;
private:
  /** a trie of triggers */
  class TrTrie
  {
  private:
    Trigger* getTrigger2( std::vector< Node >& nodes );
    void addTrigger2( std::vector< Node >& nodes, Trigger* t );
  public:
    TrTrie() : d_tr( NULL ){}
    Trigger* d_tr;
    std::map< Node, TrTrie* > d_children;
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
  };
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
  PatsMatcher* getGenerator() { return d_mg; }
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound();
  /** get next match.  must call reset( eqc ) once before this function. */
  bool getNextMatch();
  const InstMatch & getInstMatch(){return d_mg->getInstMatch();};
  /** return whether this is a multi-trigger */
  bool isMultiTrigger() { return d_nodes.size()>1; }
public:
  /** add all available instantiations exhaustively, in any equivalence class
      if limitInst>0, limitInst is the max # of instantiations to try */
  int addInstantiations( InstMatch& baseMatch);
  /** mkTrigger method
     ie     : quantifier engine;
     f      : forall something ....
     nodes  : (multi-)trigger
     matchOption : which policy to use for creating matches (one of InstMatchGenerator::MATCH_GEN_* )
     keepAll: don't remove unneeded patterns;
     trOption : policy for dealing with triggers that already existed (see below)
  */
  enum {
    //options for producing matches
    MATCH_GEN_DEFAULT = 0,
    MATCH_GEN_EFFICIENT_E_MATCH,   //generate matches via Efficient E
  };
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
  static inline bool isUsableTrigger( TNode n, TNode f ){
    //return n.getAttribute(InstConstantAttribute())==f && n.getKind()==APPLY_UF;
    return n.getAttribute(InstConstantAttribute())==f && isAtomicTrigger( n ) && isUsable( n, f );
  }
  static inline bool isAtomicTrigger( TNode n ){
    return
      n.getKind()==kind::APPLY_UF ||
      n.getKind()==kind::SELECT ||
      n.getKind()==kind::STORE;
  }
  static bool isUsableTrigger( std::vector< Node >& nodes, Node f );
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

}/* CVC4::theory::rrinst namespace */

}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__REWRITERULES__RR_TRIGGER_H */
