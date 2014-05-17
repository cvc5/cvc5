/*********************                                                        */
/*! \file trigger.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief trigger class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__TRIGGER_H
#define __CVC4__THEORY__QUANTIFIERS__TRIGGER_H

#include "theory/quantifiers/inst_match.h"
#include "expr/node.h"
#include "util/hash.h"
#include <map>

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace inst {

class IMGenerator;

//a collect of nodes representing a trigger
class Trigger {
private:
  /** the quantifiers engine */
  QuantifiersEngine* d_quantEngine;
  /** the quantifier this trigger is for */
  Node d_f;
  /** match generators */
  IMGenerator* d_mg;
private:
  /** trigger constructor */
  Trigger( QuantifiersEngine* ie, Node f, std::vector< Node >& nodes, int matchOption = 0, bool smartTriggers = false );
public:
  ~Trigger(){}
public:
  std::vector< Node > d_nodes;
public:
  IMGenerator* getGenerator() { return d_mg; }
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound();
  /** reset, eqc is the equivalence class to search in (search in any if eqc=null) */
  void reset( Node eqc );
  /** get next match.  must call reset( eqc ) once before this function. */
  bool getNextMatch( Node f, InstMatch& m );
  /** get the match against ground term or formula t.
      the trigger and t should have the same shape.
      Currently the trigger should not be a multi-trigger.
  */
  bool getMatch( Node f, Node t, InstMatch& m);
  /** add ground term t, called when t is added to the TermDb */
  int addTerm( Node t );
  /** return whether this is a multi-trigger */
  bool isMultiTrigger() { return d_nodes.size()>1; }
public:
  /** add all available instantiations exhaustively, in any equivalence class
      if limitInst>0, limitInst is the max # of instantiations to try */
  int addInstantiations( InstMatch& baseMatch );
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
  static Node getIsUsableTrigger( Node n, Node f, bool pol = true, bool hasPol = false );
  /** collect all APPLY_UF pattern terms for f in n */
  static bool collectPatTerms2( QuantifiersEngine* qe, Node f, Node n, std::map< Node, bool >& patMap, int tstrt, bool pol, bool hasPol );
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
  /** get pattern arithmetic */
  static bool isArithmeticTrigger( Node f, Node n, std::map< Node, Node >& coeffs );
  static bool isBooleanTermTrigger( Node n );

  inline void toStream(std::ostream& out) const {
    /*
    out << "TRIGGER( ";
    for( int i=0; i<(int)d_nodes.size(); i++ ){
      if( i>0 ){ out << ", "; }
      out << d_nodes[i];
    }
    out << " )";
    */
  }
  void debugPrint( const char * c ) {
    Trace(c) << "TRIGGER( ";
    for( int i=0; i<(int)d_nodes.size(); i++ ){
      if( i>0 ){ Trace(c) << ", "; }
      Trace(c) << d_nodes[i];
    }
    Trace(c) << " )";
  }
};

inline std::ostream& operator<<(std::ostream& out, const Trigger & tr) {
  tr.toStream(out);
  return out;
}


/** a trie of triggers */
class TriggerTrie {
private:
  inst::Trigger* getTrigger2( std::vector< Node >& nodes );
  void addTrigger2( std::vector< Node >& nodes, inst::Trigger* t );
public:
  TriggerTrie() : d_tr( NULL ){}
  inst::Trigger* d_tr;
  std::map< TNode, TriggerTrie* > d_children;
  inst::Trigger* getTrigger( std::vector< Node >& nodes ){
    std::vector< Node > temp;
    temp.insert( temp.begin(), nodes.begin(), nodes.end() );
    std::sort( temp.begin(), temp.end() );
    return getTrigger2( temp );
  }
  void addTrigger( std::vector< Node >& nodes, inst::Trigger* t ){
    std::vector< Node > temp;
    temp.insert( temp.begin(), nodes.begin(), nodes.end() );
    std::sort( temp.begin(), temp.end() );
    return addTrigger2( temp, t );
  }
};/* class inst::Trigger::Trigger */

}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__TRIGGER_H */
