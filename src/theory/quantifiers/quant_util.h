/*********************                                                        */
/*! \file quant_util.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief quantifier util
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANT_UTIL_H
#define __CVC4__THEORY__QUANT_UTIL_H

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {
  class TermDb;
}

class QuantifiersModule {
protected:
  QuantifiersEngine* d_quantEngine;
public:
  QuantifiersModule( QuantifiersEngine* qe ) : d_quantEngine( qe ){}
  virtual ~QuantifiersModule(){}
  //get quantifiers engine
  QuantifiersEngine* getQuantifiersEngine() { return d_quantEngine; }
  /** presolve */
  virtual void presolve() {}
  /* whether this module needs to check this round */
  virtual bool needsCheck( Theory::Effort e ) { return e>=Theory::EFFORT_LAST_CALL; }
  /* whether this module needs a model built */
  virtual unsigned needsModel( Theory::Effort e );
  /* reset at a round */
  virtual void reset_round( Theory::Effort e ){}
  /* Call during quantifier engine's check */
  virtual void check( Theory::Effort e, unsigned quant_e ) = 0;
  /* check was complete, return false if there is no way to answer "SAT", true if maybe can answer "SAT" */
  virtual bool checkComplete() { return true; }
  /* check was complete for quantified formula q (e.g. no lemmas implies a model) */
  virtual bool checkCompleteFor( Node q ) { return false; }
  /* Called for new quantified formulas */
  virtual void preRegisterQuantifier( Node q ) { }
  /* Called for new quantifiers after owners are finalized */
  virtual void registerQuantifier( Node q ) = 0;
  virtual void assertNode( Node n ) {}
  virtual void propagate( Theory::Effort level ){}
  virtual Node getNextDecisionRequest( unsigned& priority ) { return TNode::null(); }
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  virtual std::string identify() const = 0;
public:
  eq::EqualityEngine * getEqualityEngine();
  bool areDisequal( TNode n1, TNode n2 );
  bool areEqual( TNode n1, TNode n2 );
  TNode getRepresentative( TNode n );
  quantifiers::TermDb * getTermDatabase();
};/* class QuantifiersModule */

class QuantifiersUtil {
public:
  QuantifiersUtil(){}
  virtual ~QuantifiersUtil(){}
  /* reset at a round */
  virtual bool reset( Theory::Effort e ) = 0;
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
  //return 1 : solved on LHS, return -1 : solved on RHS, return 0: failed
  static int isolate( Node v, std::map< Node, Node >& msum, Node & veq_c, Node & val, Kind k );
  static int isolate( Node v, std::map< Node, Node >& msum, Node & veq, Kind k, bool doCoeff = false );
  static Node solveEqualityFor( Node lit, Node v );
  static Node negate( Node t );
  static Node offset( Node t, int i );
  static void debugPrintMonomialSum( std::map< Node, Node >& msum, const char * c );
};


class QuantRelevance
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
  /** register quantifier */
  void registerQuantifier( Node f );
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
  /** get the term that exists in EE that is congruent to f with args (f is returned by TermDb::getMatchOperator(...) */
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

}
}

#endif
