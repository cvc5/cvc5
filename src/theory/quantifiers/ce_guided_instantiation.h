/*********************                                                        */
/*! \file ce_guided_instantiation.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief counterexample guided instantiation class
 **/

#include "cvc4_private.h"

#ifndef CE_GUIDED_INSTANTIATION_H
#define CE_GUIDED_INSTANTIATION_H

#include "context/cdhashmap.h"
#include "context/cdchunk_list.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {



class CegInstantiation : public QuantifiersModule
{
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
private:
  class CegConjecture {
  public:
    CegConjecture();
    /** quantified formula */
    Node d_quant;
    /** guard */
    Node d_guard;
    /** base instantiation */
    Node d_base_inst;
    /** guard split */
    Node d_guard_split;
    /** list of constants for quantified formula */
    std::vector< Node > d_candidates;
    /** list of variables on inner quantification */
    std::vector< Node > d_inner_vars;
    /** is assigned */
    bool isAssigned() { return !d_quant.isNull(); }
    /** assign */
    void assign( Node q );
    /** initialize guard */
    void initializeGuard( QuantifiersEngine * qe );
  };
  /** the quantified formula stating the synthesis conjecture */
  CegConjecture d_conj;
  /** is conjecture active */
  context::CDO< bool > d_conj_active;
  /** is conjecture infeasible */
  context::CDO< bool > d_conj_infeasible;
  /** assertions for guards */
  NodeBoolMap d_guard_assertions;
private:
  /** check conjecture */
  void checkCegConjecture( CegConjecture * conj );
  /** get model value */
  Node getModelValue( Node n );
  /** get model term */
  Node getModelTerm( Node n );
public:
  CegInstantiation( QuantifiersEngine * qe, context::Context* c );
public:
  bool needsCheck( Theory::Effort e );
  /* Call during quantifier engine's check */
  void check( Theory::Effort e, unsigned quant_e );
  /* Called for new quantifiers */
  void registerQuantifier( Node q );
  void assertNode( Node n );
  Node getNextDecisionRequest();
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const { return "CegInstantiation"; }
};

}
}
}

#endif
