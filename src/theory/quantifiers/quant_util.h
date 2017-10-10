/*********************                                                        */
/*! \file quant_util.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief quantifier util
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANT_UTIL_H
#define __CVC4__THEORY__QUANT_UTIL_H

#include <iostream>
#include <map>
#include <vector>

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {
  class TermDb;
  class TermUtil;
}

/** QuantifiersModule class
*
* This is the virtual class for defining subsolvers of the quantifiers theory.
* It has a similar interface to a Theory object.
*/
class QuantifiersModule {
public:
  QuantifiersModule( QuantifiersEngine* qe ) : d_quantEngine( qe ){}
  virtual ~QuantifiersModule(){}
  /** presolve */
  virtual void presolve() {}
  /* whether this module needs to check this round */
  virtual bool needsCheck( Theory::Effort e ) { return e>=Theory::EFFORT_LAST_CALL; }
  /* whether this module needs a model built during 
  * It returns one of QEFFORT_* from quantifiers_engine.h,
  * which specifies the quantifiers effort in which it requires the model to
  * be built.
  */
  virtual unsigned needsModel( Theory::Effort e );
  /* reset
  * Called at the beginning of an instantiation round.
  */
  virtual void reset_round( Theory::Effort e ){}
  /* Call during quantifier engine's check */
  virtual void check( Theory::Effort e, unsigned quant_e ) = 0;
  /* check was complete, return false if the module's reasoning was globally incomplete 
  * (e.g. "sat" must be replaced with "incomplete") 
  */
  virtual bool checkComplete() { return true; }
  /* check was complete for quantified formula q
  * If for each quantified formula q, some module returns true for checkCompleteFor( q ),
  * and no lemmas are added by the quantifiers theory, then we may answer "sat", unless
  * we are incomplete for other reasons.
  */
  virtual bool checkCompleteFor( Node q ) { return false; }
  /* Called for new quantified formulas */
  virtual void preRegisterQuantifier( Node q ) { }
  /* Called for new quantifiers after ownership of quantified formulas are finalized */
  virtual void registerQuantifier( Node q ) = 0;
  /* Called when a quantified formula n is asserted to the quantifiers theory */
  virtual void assertNode( Node n ) {}
  /* Get the next decision request, identical to Theory::getNextDecisionRequest */
  virtual Node getNextDecisionRequest( unsigned& priority ) { return TNode::null(); }
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  virtual std::string identify() const = 0;
//----------------------------general queries
  /** get currently used the equality engine */
  eq::EqualityEngine * getEqualityEngine();
  /** are n1 and n2 equal in the current used equality engine? */
  bool areEqual( TNode n1, TNode n2 );
  /** are n1 and n2 disequal in the current used equality engine? */
  bool areDisequal( TNode n1, TNode n2 );
  /** get the representative of n in the current used equality engine */
  TNode getRepresentative( TNode n );
  /** get quantifiers engine that owns this module */
  QuantifiersEngine* getQuantifiersEngine() { return d_quantEngine; }
  /** get currently used term database */
  quantifiers::TermDb * getTermDatabase();
  /** get currently used term utility object */
  quantifiers::TermUtil * getTermUtil();
//----------------------------end general queries
protected:
  /** pointer to the quantifiers engine that owns this module */
  QuantifiersEngine* d_quantEngine;
};/* class QuantifiersModule */

/** Quantifiers utility 
*
* This is a lightweight version of a quantifiers module that does not implement methods
* for checking satisfiability.
*/
class QuantifiersUtil {
public:
  QuantifiersUtil(){}
  virtual ~QuantifiersUtil(){}
  /* reset
  * Called at the beginning of an instantiation round 
  * Returns false if the reset failed. When reset fails, the utility should have added a lemma 
  * via a call to qe->addLemma. TODO: improve this contract #1163
  */
  virtual bool reset( Theory::Effort e ) = 0;
  /* Called for new quantifiers */
  virtual void registerQuantifier( Node q ) = 0;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  virtual std::string identify() const = 0;
};


class QuantArith
{
public:
  static bool getMonomial( Node n, Node& c, Node& v );
  static bool getMonomial( Node n, std::map< Node, Node >& msum );
  static bool getMonomialSum( Node n, std::map< Node, Node >& msum );
  static bool getMonomialSumLit( Node lit, std::map< Node, Node >& msum );
  static Node mkNode( std::map< Node, Node >& msum );
  static Node mkCoeffTerm( Node coeff, Node t );
  //return 1 : solved on LHS, return -1 : solved on RHS, return 0: failed
  static int isolate( Node v, std::map< Node, Node >& msum, Node & veq_c, Node & val, Kind k );
  static int isolate( Node v, std::map< Node, Node >& msum, Node & veq, Kind k, bool doCoeff = false );
  static Node solveEqualityFor( Node lit, Node v );
  static Node negate( Node t );
  static Node offset( Node t, int i );
  static void debugPrintMonomialSum( std::map< Node, Node >& msum, const char * c );
};


/** QuantRelevance 
* This class is used for implementing SinE-style heuristics (e.g. see Hoder et al CADE 2011)
* This is enabled by the option --relevant-triggers.
*/
class QuantRelevance : public QuantifiersUtil
{
private:
  /** for computing relevance */
  bool d_computeRel;
  /** map from quantifiers to symbols they contain */
  std::map< Node, std::vector< Node > > d_syms;
  /** map from symbols to quantifiers */
  std::map< Node, std::vector< Node > > d_syms_quants;
  /** relevance for quantifiers and symbols */
  std::map< Node, int > d_relevance;
  /** compute symbols */
  void computeSymbols( Node n, std::vector< Node >& syms );
public:
  QuantRelevance( bool cr ) : d_computeRel( cr ){}
  ~QuantRelevance(){}
  virtual bool reset( Theory::Effort e ) { return true; }
  /* Called for new quantifiers after ownership of quantified formulas are finalized */
  virtual void registerQuantifier( Node q );
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  virtual std::string identify() const { return "QuantRelevance"; }
  /** set relevance */
  void setRelevance( Node s, int r );
  /** get relevance */
  int getRelevance( Node s ) { return d_relevance.find( s )==d_relevance.end() ? -1 : d_relevance[s]; }
  /** get number of quantifiers for symbol s */
  int getNumQuantifiersForSymbol( Node s ) { return (int)d_syms_quants[s].size(); }
};

class QuantPhaseReq
{
private:
  /** helper functions compute phase requirements */
  void computePhaseReqs( Node n, bool polarity, std::map< Node, int >& phaseReqs );
public:
  QuantPhaseReq(){}
  QuantPhaseReq( Node n, bool computeEq = false );
  ~QuantPhaseReq(){}
  void initialize( Node n, bool computeEq );
  /** is phase required */
  bool isPhaseReq( Node lit ) { return d_phase_reqs.find( lit )!=d_phase_reqs.end(); }
  /** get phase requirement */
  bool getPhaseReq( Node lit ) { return d_phase_reqs.find( lit )==d_phase_reqs.end() ? false : d_phase_reqs[ lit ]; }
  /** phase requirements for each quantifier for each instantiation literal */
  std::map< Node, bool > d_phase_reqs;
  std::map< Node, bool > d_phase_reqs_equality;
  std::map< Node, Node > d_phase_reqs_equality_term;

  static void getPolarity( Node n, int child, bool hasPol, bool pol, bool& newHasPol, bool& newPol );
  static void getEntailPolarity( Node n, int child, bool hasPol, bool pol, bool& newHasPol, bool& newPol );
};


/** EqualityQuery
* This is a wrapper class around equality engine.
*/
class EqualityQuery : public QuantifiersUtil {
public:
  EqualityQuery(){}
  virtual ~EqualityQuery(){};
  /** extends engine */
  virtual bool extendsEngine() { return false; }
  /** contains term */
  virtual bool hasTerm( Node a ) = 0;
  /** get the representative of the equivalence class of a */
  virtual Node getRepresentative( Node a ) = 0;
  /** returns true if a and b are equal in the current context */
  virtual bool areEqual( Node a, Node b ) = 0;
  /** returns true is a and b are disequal in the current context */
  virtual bool areDisequal( Node a, Node b ) = 0;
  /** get the equality engine associated with this query */
  virtual eq::EqualityEngine* getEngine() = 0;
  /** get the equivalence class of a */
  virtual void getEquivalenceClass( Node a, std::vector< Node >& eqc ) = 0;
  /** get the term that exists in EE that is congruent to f with args (f is returned by TermDb::getMatchOperator(...)) */
  virtual TNode getCongruentTerm( Node f, std::vector< TNode >& args ) = 0;
};/* class EqualityQuery */

class QuantEPR
{
private:
  void registerNode( Node n, std::map< int, std::map< Node, bool > >& visited, bool beneathQuant, bool hasPol, bool pol );
  /** non-epr */
  std::map< TypeNode, bool > d_non_epr;
  /** axioms for epr */
  std::map< TypeNode, Node > d_epr_axiom;
public:
  QuantEPR(){}
  virtual ~QuantEPR(){}
  /** constants per type */
  std::map< TypeNode, std::vector< Node > > d_consts;
  /* reset */
  //bool reset( Theory::Effort e ) {}
  /** identify */
  //std::string identify() const { return "QuantEPR"; }
  /** register assertion */
  void registerAssertion( Node assertion );
  /** finish init */
  void finishInit();
  /** is EPR */
  bool isEPR( TypeNode tn ) const { return d_non_epr.find( tn )==d_non_epr.end(); }
  /** is EPR constant */
  bool isEPRConstant( TypeNode tn, Node k ); 
  /** add EPR constant */
  void addEPRConstant( TypeNode tn, Node k ); 
  /** get EPR axiom */
  Node mkEPRAxiom( TypeNode tn );
  /** has EPR axiom */
  bool hasEPRAxiom( TypeNode tn ) const { return d_epr_axiom.find( tn )!=d_epr_axiom.end(); }
};

class TermRecBuild {
private:
  std::vector< Node > d_term;
  std::vector< std::vector< Node > > d_children;
  std::vector< Kind > d_kind;
  std::vector< bool > d_has_op;
  std::vector< unsigned > d_pos;
  void addTerm( Node n );
public:
  TermRecBuild(){}
  void init( Node n );
  void push( unsigned p );
  void pop();
  void replaceChild( unsigned i, Node n );
  Node getChild( unsigned i );
  Node build( unsigned p=0 );
};

}
}

#endif
