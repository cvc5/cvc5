/*********************                                                        */
/*! \file ce_guided_instantiation.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief counterexample guided instantiation class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_INSTANTIATION_H
#define __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_INSTANTIATION_H

#include "context/cdchunk_list.h"
#include "context/cdhashmap.h"
#include "options/quantifiers_modes.h"
#include "theory/quantifiers/ce_guided_single_inv.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** a synthesis conjecture */
class CegConjecture {
private:
  QuantifiersEngine * d_qe;
  /** list of constants for quantified formula */
  std::vector< Node > d_candidates;
  /** base instantiation */
  Node d_base_inst;
  /** expand base inst to disjuncts */
  std::vector< Node > d_base_disj;
  /** list of variables on inner quantification */
  std::vector< Node > d_inner_vars;
  std::vector< std::vector< Node > > d_inner_vars_disj;
  /** current extential quantifeirs whose couterexamples we must refine */
  std::vector< std::vector< Node > > d_ce_sk;
  /** the cardinality literals */
  std::map< int, Node > d_lits;
  /** current cardinality */
  context::CDO< int > d_curr_lit;
  /** active measure term */
  Node d_active_measure_term;
  /** refinement lemmas */
  std::vector< Node > d_refinement_lemmas;
  std::vector< std::vector< Node > > d_refinement_lemmas_aux_vars;
private: //for condition solutions
  /** get candidate list recursively for conditional solutions */
  void getConditionalCandidateList( std::vector< Node >& clist, Node curr, bool reqAdd );
  Node constructConditionalCandidate( std::map< Node, Node >& cmv, Node curr );
  Node getActiveConditional( Node curr );
  void getContextConditionals( Node curr, Node x, std::vector< Node >& conds, std::vector< Node >& rets, std::map< Node, bool >& cpols );
  Node mkConditional( Node c, std::vector< Node >& args, bool pol = true );
  Node purifyConditionalEvaluations( Node n, std::map< Node, Node >& csol_cond, std::map< Node, Node >& psubs, 
                                     std::map< Node, Node >& visited );
  /** register candidate conditional */
  void registerCandidateConditional( Node v );
public:
  CegConjecture( QuantifiersEngine * qe, context::Context* c );
  ~CegConjecture();

  /** quantified formula asserted */
  Node d_assert_quant;
  /** quantified formula (after processing) */
  Node d_quant;

  class CandidateInfo {
  public:
    CandidateInfo() : d_csol_status(-1){}
    /** list of terms we have instantiated candidates with */
    std::vector< Node > d_inst;
    /** conditional solutions */
    Node d_csol_op;
    Node d_csol_cond;
    Node d_csol_var[2];
    /** solution status */
    int d_csol_status;
  };
  std::map< Node, CandidateInfo > d_cinfo;
  
  /** measure term */
  Node d_measure_term;
  /** measure sum size */
  int d_measure_term_size;
  /** refine count */
  unsigned d_refine_count;
  /** incomplete candidate values */
  bool d_incomplete_candidate_values;

  const CegConjectureSingleInv* getCegConjectureSingleInv() const {
    return d_ceg_si;
  }
  
  bool needsRefinement();
  void getCandidateList( std::vector< Node >& clist, bool forceOrig = false );
  bool constructCandidates( std::vector< Node >& clist, std::vector< Node >& model_values, std::vector< Node >& candidate_values );

  void doCegConjectureSingleInvCheck(std::vector< Node >& lems);
  void doCegConjectureCheck(std::vector< Node >& lems, std::vector< Node >& model_values);
  void doCegConjectureRefine(std::vector< Node >& lems);

  Node getSingleInvocationSolution(unsigned sol_index, TypeNode stn,
                                   int& reconstructed, bool rconsSygus=true){
    return d_ceg_si->getSolution(sol_index, stn, reconstructed, rconsSygus);
  }

  Node reconstructToSyntaxSingleInvocation(
      Node s, TypeNode stn, int& reconstructed, bool rconsSygus = true ) {
    return d_ceg_si->reconstructToSyntax(s, stn, reconstructed, rconsSygus);
  }

  std::vector<Node>& getProgTempVars(Node prog) {
    return d_ceg_si->d_prog_templ_vars[prog];
  }
  
  void recordInstantiation( std::vector< Node >& vs ) {
    Assert( vs.size()==d_candidates.size() );
    for( unsigned i=0; i<vs.size(); i++ ){
      d_cinfo[d_candidates[i]].d_inst.push_back( vs[i] );
    }
  }
  Node getCandidate( unsigned int i ) { return d_candidates[i]; }
  
  void debugPrint( const char * c );

private:
  /** single invocation utility */
  CegConjectureSingleInv * d_ceg_si;
public: //non-syntax guided (deprecated)
  /** guard */
  bool d_syntax_guided;
  Node d_nsg_guard;
public:
  /** get current term size */
  int getCurrentTermSize() { return d_curr_lit.get(); }
  /** increment current term size */
  void incrementCurrentTermSize() { d_curr_lit.set( d_curr_lit.get() + 1 ); }
  /** set measure term */
  void setMeasureTerm( Node mt );
  /** get measure term */
  Node getMeasureTermFactor( Node v );
  Node getMeasureTerm() { return d_measure_term; }
  /** allocate literal */
  Node getFairnessLiteral( int i );
  /** get guard */
  Node getGuard();
  /** is ground */
  bool isGround() { return d_inner_vars.empty(); }
  /** fairness */
  CegqiFairMode getCegqiFairMode();
  /** is single invocation */
  bool isSingleInvocation() const;
  /** is single invocation */
  bool isFullySingleInvocation();
  /** needs check */
  bool needsCheck( std::vector< Node >& lem );
  /** preregister conjecture */
  void preregisterConjecture( Node q );
  /** initialize guard */
  void initializeGuard();
  /** assign */
  void assign( Node q );
  /** is assigned */
  bool isAssigned() { return !d_quant.isNull(); }
  /** get model values */
  bool getModelValues( std::vector< Node >& n, std::vector< Node >& v );
  /** get model value */
  Node getModelValue( Node n );
};


class CegInstantiation : public QuantifiersModule
{
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
private:
  /** the quantified formula stating the synthesis conjecture */
  CegConjecture * d_conj;
  /** last instantiation by single invocation module? */
  bool d_last_inst_si;
  /** evaluation axioms */
  std::map< Node, bool > d_eval_axioms;
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
  /** get eager unfolding */
  Node getEagerUnfold( Node n, std::map< Node, Node >& visited );
private:
  /** check conjecture */
  void checkCegConjecture( CegConjecture * conj );
public:
  CegInstantiation( QuantifiersEngine * qe, context::Context* c );
  ~CegInstantiation();
public:
  bool needsCheck( Theory::Effort e );
  unsigned needsModel( Theory::Effort e );
  /* Call during quantifier engine's check */
  void check( Theory::Effort e, unsigned quant_e );
  /* Called for new quantifiers */
  void preRegisterQuantifier( Node q );
  void registerQuantifier( Node q );
  void assertNode( Node n );
  Node getNextDecisionRequest( unsigned& priority );
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const { return "CegInstantiation"; }
  /** print solution for synthesis conjectures */
  void printSynthSolution( std::ostream& out );
  /** collect disjuncts */
  static void collectDisjuncts( Node n, std::vector< Node >& ex );
  /** preregister assertion (before rewrite) */
  void preregisterAssertion( Node n );
public:
  class Statistics {
  public:
    IntStat d_cegqi_lemmas_ce;
    IntStat d_cegqi_lemmas_refine;
    IntStat d_cegqi_si_lemmas;
    Statistics();
    ~Statistics();
  };/* class CegInstantiation::Statistics */
  Statistics d_statistics;
}; /* class CegInstantiation */

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */

#endif
