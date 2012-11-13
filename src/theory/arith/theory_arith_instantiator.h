/*********************                                                        */
/*! \file theory_arith_instantiator.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief instantiator_arith_instantiator
 **/


#include "cvc4_private.h"

#ifndef __CVC4__INSTANTIATOR_ARITH_H
#define __CVC4__INSTANTIATOR_ARITH_H

#include "theory/quantifiers_engine.h"
#include "theory/arith/arithvar_node_map.h"

#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace arith {

class TheoryArith;
class InstantiatorTheoryArith;

class InstStrategySimplex : public InstStrategy{
private:
  /** delta */
  std::map< TypeNode, Node > d_deltas;
  /** for each quantifier, simplex rows */
  std::map< Node, std::vector< ArithVar > > d_instRows;
  /** tableaux */
  std::map< ArithVar, Node > d_tableaux_term;
  std::map< ArithVar, std::map< Node, Node > > d_tableaux_ce_term;
  std::map< ArithVar, std::map< Node, Node > > d_tableaux;
  /** ce tableaux */
  std::map< ArithVar, std::map< Node, Node > > d_ceTableaux;
  /** get value */
  Node getTableauxValue( Node n, bool minus_delta = false );
  Node getTableauxValue( ArithVar v, bool minus_delta = false );
  /** do instantiation */
  bool doInstantiation( Node f, Node term, ArithVar x, InstMatch& m, Node var );
  bool doInstantiation2( Node f, Node term, ArithVar x, InstMatch& m, Node var, bool minus_delta = false );
  /** add term to row */
  void addTermToRow( ArithVar x, Node n, Node& f, NodeBuilder<>& t );
  /** get arith theory */
  TheoryArith* getTheoryArith();
  /** print debug */
  void debugPrint( const char* c );
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryArith* d_th;
  /** */
  int d_counter;
  /** negative one */
  Node d_negOne;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e );
public:
  InstStrategySimplex( InstantiatorTheoryArith* th, QuantifiersEngine* ie );
  ~InstStrategySimplex(){}
  /** identify */
  std::string identify() const { return std::string("Simplex"); }

  class Statistics {
  public:
    IntStat d_instantiations;
    IntStat d_instantiations_minus;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
};

class InstantiatorTheoryArith : public Instantiator{
  friend class QuantifiersEngine;
  friend class InstStrategySimplex;
  friend class InstStrategySimplexUfMatch;
public:
  InstantiatorTheoryArith(context::Context* c, QuantifiersEngine* ie, Theory* th);
  ~InstantiatorTheoryArith() {}

  /** assertNode function, assertion is asserted to theory */
  void assertNode( Node assertion );
  /** Pre-register a term.  Done one time for a Node, ever. */
  void preRegisterTerm( Node t );
  /** identify */
  std::string identify() const { return std::string("InstantiatorTheoryArith"); }
private:
  /**  reset instantiation */
  void processResetInstantiationRound( Theory::Effort effort );
  /** process at effort */
  int process( Node f, Theory::Effort effort, int e );


};/* class InstantiatiorTheoryArith  */

}
}
}

#endif