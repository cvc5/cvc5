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
    CegConjecture( context::Context* c );
    /** is conjecture active */
    context::CDO< bool > d_active;
    /** is conjecture infeasible */
    context::CDO< bool > d_infeasible;
    /** quantified formula */
    Node d_quant;
    /** guard */
    Node d_guard;
    /** base instantiation */
    Node d_base_inst;
    /** guard split */
    Node d_guard_split;
    /** is syntax-guided */
    bool d_syntax_guided;
    /** list of constants for quantified formula */
    std::vector< Node > d_candidates;
    /** list of variables on inner quantification */
    std::vector< Node > d_inner_vars;
    /** initialize guard */
    void initializeGuard( QuantifiersEngine * qe );
    /** measure term */
    Node d_measure_term;
    /** measure sum size */
    int d_measure_term_size;
    /** assign */
    void assign( Node q );
    /** is assigned */
    bool isAssigned() { return !d_quant.isNull(); }
    /** current extential quantifeirs whose couterexamples we must refine */
    std::vector< Node > d_ce_sk;
  public:  //for fairness
    /** the cardinality literals */
    std::map< int, Node > d_lits;
    /** current cardinality */
    context::CDO< int > d_curr_lit;
    /** allocate literal */
    Node getLiteral( QuantifiersEngine * qe, int i );
  };
  /** the quantified formula stating the synthesis conjecture */
  CegConjecture * d_conj;
private: //for enforcing fairness
  /** measure functions */
  std::map< TypeNode, Node > d_uf_measure;
  /** register measured type */
  void registerMeasuredType( TypeNode tn );
  /** term -> size term */
  std::map< Node, Node > d_size_term;
  /** get size term */
  Node getSizeTerm( Node n, TypeNode tn, std::vector< Node >& lems );
  /** term x constructor -> lemma */
  std::map< Node, std::map< int, Node > > d_size_term_lemma;
  /** get measure lemmas */
  void getMeasureLemmas( Node n, Node v, std::vector< Node >& lems );
private:
  /** check conjecture */
  void checkCegConjecture( CegConjecture * conj );
  /** get model values */
  bool getModelValues( std::vector< Node >& n, std::vector< Node >& v );
  /** get model value */
  Node getModelValue( Node n );
  /** get model term */
  Node getModelTerm( Node n );
public:
  CegInstantiation( QuantifiersEngine * qe, context::Context* c );
public:
  bool needsCheck( Theory::Effort e );
  bool needsModel( Theory::Effort e );
  bool needsFullModel( Theory::Effort e );
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
