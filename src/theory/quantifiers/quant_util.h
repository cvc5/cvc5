/*********************                                                        */
/*! \file quant_util.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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


class QuantArith
{
public:
  static bool getMonomial( Node n, std::map< Node, Node >& msum );
  static bool getMonomialSum( Node n, std::map< Node, Node >& msum );
  static bool getMonomialSumLit( Node lit, std::map< Node, Node >& msum );
  static bool isolate( Node v, std::map< Node, Node >& msum, Node & veq, Kind k );
  static Node negate( Node t );
  static Node offset( Node t, int i );
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
  QuantPhaseReq( Node n, bool computeEq = false );
  ~QuantPhaseReq(){}
  /** is phase required */
  bool isPhaseReq( Node lit ) { return d_phase_reqs.find( lit )!=d_phase_reqs.end(); }
  /** get phase requirement */
  bool getPhaseReq( Node lit ) { return d_phase_reqs.find( lit )==d_phase_reqs.end() ? false : d_phase_reqs[ lit ]; }
  /** phase requirements for each quantifier for each instantiation literal */
  std::map< Node, bool > d_phase_reqs;
  std::map< Node, bool > d_phase_reqs_equality;
  std::map< Node, Node > d_phase_reqs_equality_term;

  static void getPolarity( Node n, int child, bool hasPol, bool pol, bool& newHasPol, bool& newPol );
};


class EqualityQuery {
public:
  EqualityQuery(){}
  virtual ~EqualityQuery(){};
  /** reset */
  virtual void reset() = 0;
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

  virtual void setLiberal( bool l ) = 0;
};/* class EqualityQuery */

}
}

#endif
