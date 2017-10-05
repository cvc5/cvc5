/*********************                                                        */
/*! \file trigger.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief trigger class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__TRIGGER_H
#define __CVC4__THEORY__QUANTIFIERS__TRIGGER_H

#include <map>

#include "expr/node.h"
#include "theory/quantifiers/inst_match.h"
#include "options/quantifiers_options.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace inst {

class IMGenerator;
class InstMatchGenerator;

class TriggerTermInfo {
public:
  TriggerTermInfo() : d_reqPol(0){}
  ~TriggerTermInfo(){}
  std::vector< Node > d_fv;
  int d_reqPol;
  Node d_reqPolEq;
  void init( Node q, Node n, int reqPol = 0, Node reqPolEq = Node::null() );
};

class HigherOrderTrigger;

/** A collect of nodes representing a trigger. */
class Trigger {
  friend class IMGenerator;
public:
  virtual ~Trigger();

  IMGenerator* getGenerator() { return d_mg; }

  /** reset instantiation round (call this whenever equivalence
   * classes have changed) */
  void resetInstantiationRound();
  /** reset, eqc is the equivalence class to search in (search in any
   * if eqc=null) */
  void reset( Node eqc );
  /** get next match.  must call reset( eqc ) once before this function. */
  bool getNextMatch( Node f, InstMatch& m );
  /** return whether this is a multi-trigger */
  bool isMultiTrigger() { return d_nodes.size()>1; }
  /** get inst pattern list */
  Node getInstPattern();

  /** add all available instantiations */
  virtual int addInstantiations( InstMatch& baseMatch );
protected:
  /** add all available instantiations exhaustively */
  int addBasicInstantiations( InstMatch& baseMatch );
  /** add an instantiation (called by InstMatchGenerator) */
  virtual bool sendInstantiation( InstMatch& m );
public:
  /** mkTrigger method
     ie     : quantifier engine;
     f      : forall something ....
     nodes  : (multi-)trigger
     keepAll: don't remove unneeded patterns;
     trOption : policy for dealing with triggers that already existed
                (see below)
  */
  enum{
    TR_MAKE_NEW,    //make new trigger even if it already may exist
    TR_GET_OLD,     //return a previous trigger if it had already been created
    TR_RETURN_NULL  //return null if a duplicate is found
  };
  //nodes input, trNodes output
  static bool mkTriggerTerms( Node q, std::vector< Node >& nodes, unsigned n_vars, std::vector< Node >& trNodes );
  static Trigger* mkTrigger( QuantifiersEngine* qe, Node f, std::vector< Node >& nodes,
                             bool keepAll = true, int trOption = TR_MAKE_NEW, unsigned use_n_vars = 0 );
  static Trigger* mkTrigger( QuantifiersEngine* qe, Node f, Node n, bool keepAll = true,
                             int trOption = TR_MAKE_NEW, unsigned use_n_vars = 0 );
  static void collectPatTerms( Node q, Node n, std::vector< Node >& patTerms, quantifiers::TriggerSelMode tstrt,
                               std::vector< Node >& exclude, std::map< Node, TriggerTermInfo >& tinfo,
                               bool filterInst = false );
  /** is usable trigger */
  static bool isUsableTrigger( Node n, Node q );
  static Node getIsUsableTrigger( Node n, Node q );
  static bool isUsableAtomicTrigger( Node n, Node q );
  static bool isAtomicTrigger( Node n );
  static bool isAtomicTriggerKind( Kind k );
  static bool isRelationalTrigger( Node n );
  static bool isRelationalTriggerKind( Kind k );
  static bool isCbqiKind( Kind k );
  static bool isSimpleTrigger( Node n );
  static bool isBooleanTermTrigger( Node n );
  static bool isPureTheoryTrigger( Node n );
  static int getTriggerWeight( Node n );
  static bool isLocalTheoryExt( Node n, std::vector< Node >& vars,
                                std::vector< Node >& patTerms );
  /** return data structure for producing matches for this trigger. */
  static InstMatchGenerator* getInstMatchGenerator( Node q, Node n );
  static Node getInversionVariable( Node n );
  static Node getInversion( Node n, Node x );
  /** get all variables that E-matching can possibly handle */
  static void getTriggerVariables( Node icn, Node f, std::vector< Node >& t_vars );

  void debugPrint( const char * c ) {
    Trace(c) << "TRIGGER( ";
    for( int i=0; i<(int)d_nodes.size(); i++ ){
      if( i>0 ){ Trace(c) << ", "; }
      Trace(c) << d_nodes[i];
    }
    Trace(c) << " )";
  }
  int getActiveScore();
protected:
  /** trigger constructor */
  Trigger( QuantifiersEngine* ie, Node f, std::vector< Node >& nodes );

  /** is subterm of trigger usable */
  static bool isUsable( Node n, Node q );
  static Node getIsUsableEq( Node q, Node eq );
  static bool isUsableEqTerms( Node q, Node n1, Node n2 );
  /** collect all APPLY_UF pattern terms for f in n */
  static void collectPatTerms2( Node q, Node n, std::map< Node, std::vector< Node > >& visited, std::map< Node, TriggerTermInfo >& tinfo, 
                                quantifiers::TriggerSelMode tstrt, std::vector< Node >& exclude, std::vector< Node >& added,
                                bool pol, bool hasPol, bool epol, bool hasEPol, bool knowIsUsable = false );

  std::vector< Node > d_nodes;

  /** the quantifiers engine */
  QuantifiersEngine* d_quantEngine;
  /** the quantifier this trigger is for */
  Node d_f;
  /** match generators */
  IMGenerator* d_mg;
}; /* class Trigger */

/** a trie of triggers */
class TriggerTrie {
public:
  TriggerTrie();
  ~TriggerTrie();

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
private:
  inst::Trigger* getTrigger2( std::vector< Node >& nodes );
  void addTrigger2( std::vector< Node >& nodes, inst::Trigger* t );

  std::vector< inst::Trigger* > d_tr;
  std::map< TNode, TriggerTrie* > d_children;
};/* class inst::Trigger::TriggerTrie */

}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__TRIGGER_H */
