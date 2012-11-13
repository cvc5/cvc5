/*********************                                                        */
/*! \file theory_datatypes_instantiator.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters, bobot
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief instantiator_datatypes_instantiator
 **/


#include "cvc4_private.h"

#ifndef __CVC4__INSTANTIATOR_DATATYPES_H
#define __CVC4__INSTANTIATOR_DATATYPES_H

#include "theory/quantifiers_engine.h"

#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

class TheoryDatatypes;

class InstStrategyDatatypesValue : public InstStrategy
{
private:
  Node getValueFor( Node n );
public:
  //constructor
  InstStrategyDatatypesValue( QuantifiersEngine* qe );
  ~InstStrategyDatatypesValue(){}
  /** reset instantiation */
  void processResetInstantiationRound( Theory::Effort effort );
  /** process method, returns a status */
  int process( Node f, Theory::Effort effort, int e );
  /** identify */
  std::string identify() const { return std::string("InstStrategyDatatypesValue"); }

  class Statistics {
  public:
    IntStat d_instantiations;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
};/* class InstStrategy */


class InstantiatorTheoryDatatypes : public Instantiator{
  friend class QuantifiersEngine;
public:
  InstantiatorTheoryDatatypes(context::Context* c, QuantifiersEngine* ie, TheoryDatatypes* th);
  ~InstantiatorTheoryDatatypes() {}

  /** assertNode function, assertion is asserted to theory */
  void assertNode( Node assertion );
  /** identify */
  std::string identify() const { return std::string("InstantiatorTheoryDatatypes"); }
private:
  /**  reset instantiation */
  void processResetInstantiationRound( Theory::Effort effort );
  /** process at effort */
  int process( Node f, Theory::Effort effort, int e );
public:
  /** general queries about equality */
  bool hasTerm( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  Node getRepresentative( Node a );
  eq::EqualityEngine* getEqualityEngine();
  void getEquivalenceClass( Node a, std::vector< Node >& eqc );
    /** general creators of candidate generators */
  CVC4::theory::rrinst::CandidateGenerator* getRRCanGenClass();
};/* class InstantiatiorTheoryDatatypes  */


}
}
}

#endif
