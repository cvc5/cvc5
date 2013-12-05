/*********************                                                        */
/*! \file inst_strategy_cbqi.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief instantiator_arith_instantiator
 **/


#include "cvc4_private.h"

#ifndef __CVC4__INST_STRATEGT_CBQI_H
#define __CVC4__INST_STRATEGT_CBQI_H

#include "theory/quantifiers/instantiation_engine.h"
#include "theory/arith/arithvar.h"

#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {

namespace arith {
  class TheoryArith;
}

namespace datatypes {
  class TheoryDatatypes;
}

namespace quantifiers {


class InstStrategySimplex : public InstStrategy{
protected:
  /** calculate if we should process this quantifier */
  bool calculateShouldProcess( Node f );
private:
  /** reference to theory arithmetic */
  arith::TheoryArith* d_th;
  /** delta */
  std::map< TypeNode, Node > d_deltas;
  /** for each quantifier, simplex rows */
  std::map< Node, std::vector< arith::ArithVar > > d_instRows;
  /** tableaux */
  std::map< Node, std::map< arith::ArithVar, Node > > d_tableaux_term;
  std::map< Node, std::map< arith::ArithVar, std::map< Node, Node > > > d_tableaux_ce_term;
  std::map< Node, std::map< arith::ArithVar, std::map< Node, Node > > > d_tableaux;
  /** ce tableaux */
  std::map< Node, std::map< arith::ArithVar, std::map< Node, Node > > > d_ceTableaux;
  /** get value */
  Node getTableauxValue( Node n, bool minus_delta = false );
  Node getTableauxValue( arith::ArithVar v, bool minus_delta = false );
  /** do instantiation */
  bool doInstantiation( Node f, Node ic, Node term, arith::ArithVar x, InstMatch& m, Node var );
  bool doInstantiation2( Node f, Node ic, Node term, arith::ArithVar x, InstMatch& m, Node var, bool minus_delta = false );
  /** add term to row */
  void addTermToRow( Node ic, arith::ArithVar x, Node n, NodeBuilder<>& t );
  /** print debug */
  void debugPrint( const char* c );
private:
  /** */
  int d_counter;
  /** negative one */
  Node d_negOne;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e );
public:
  InstStrategySimplex( arith::TheoryArith* th, QuantifiersEngine* ie );
  ~InstStrategySimplex(){}
  /** identify */
  std::string identify() const { return std::string("Simplex"); }
};


class InstStrategyDatatypesValue : public InstStrategy
{
protected:
  /** calculate if we should process this quantifier */
  bool calculateShouldProcess( Node f );
private:
  /** reference to theory datatypes */
  datatypes::TheoryDatatypes* d_th;
  /** get value function */
  Node getValueFor( Node n );
public:
  //constructor
  InstStrategyDatatypesValue( datatypes::TheoryDatatypes* th, QuantifiersEngine* qe );
  ~InstStrategyDatatypesValue(){}
  /** reset instantiation */
  void processResetInstantiationRound( Theory::Effort effort );
  /** process method, returns a status */
  int process( Node f, Theory::Effort effort, int e );
  /** identify */
  std::string identify() const { return std::string("InstStrategyDatatypesValue"); }

};/* class InstStrategy */

}
}
}

#endif
