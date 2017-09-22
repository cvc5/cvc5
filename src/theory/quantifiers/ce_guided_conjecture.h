/*********************                                                        */
/*! \file ce_guided_conjecture.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief counterexample guided instantiation class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_CONJECTURE_H
#define __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_CONJECTURE_H

#include "context/cdchunk_list.h"
#include "context/cdhashmap.h"
#include "theory/quantifiers/ce_guided_single_inv.h"
#include "theory/quantifiers/ce_guided_pbe.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** a synthesis conjecture */
class CegConjecture {
private:
  /** reference to quantifier engine */
  QuantifiersEngine * d_qe;
  /** single invocation utility */
  CegConjectureSingleInv * d_ceg_si;
  /** program by examples utility */
  CegConjecturePbe * d_ceg_pbe;
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
  /** refinement lemmas */
  std::vector< Node > d_refinement_lemmas;
  std::vector< Node > d_refinement_lemmas_base;
  /** quantified formula asserted */
  Node d_quant;
  /** quantified formula (after processing) */
  Node d_embed_quant;
  /** candidate information */
  class CandidateInfo {
  public:
    CandidateInfo(){}
    /** list of terms we have instantiated candidates with */
    std::vector< Node > d_inst;
  };
  std::map< Node, CandidateInfo > d_cinfo;  
  /** refine count */
  unsigned d_refine_count;
  /** Whether we are syntax-guided (e.g. was the input in SyGuS format).
   * This includes SyGuS inputs where no syntactic restrictions are provided.
   */
  bool d_syntax_guided;
private: // for sygusStream
  /** the streaming guards for sygus streaming mode */
  std::vector< Node > d_stream_guards;
  /** get current stream guard */
  Node getCurrentStreamGuard() const;
private: //non-syntax guided (deprecated)
  /** the guard for non-syntax-guided synthesis */
  Node d_nsg_guard;
private:
  /** get embedding */
  Node convertToEmbedding( Node n, std::map< Node, Node >& synth_fun_vars, std::map< Node, Node >& visited );
  /** collect constants */
  void collectConstants( Node n, std::map< TypeNode, std::vector< Node > >& consts, std::map< Node, bool >& visited );
  /** construct candidates */
  bool constructCandidates( std::vector< Node >& clist, std::vector< Node >& model_values, 
                            std::vector< Node >& candidate_values, std::vector< Node >& lems );
  /** get candidadate */
  Node getCandidate( unsigned int i ) { return d_candidates[i]; }
public:
  CegConjecture( QuantifiersEngine * qe, context::Context* c );
  ~CegConjecture();
  /** get original version of conjecture */
  Node getConjecture() { return d_quant; }
  /** get deep embedding version of conjecture */
  Node getEmbeddedConjecture() { return d_embed_quant; }
  /** get next decision request */
  Node getNextDecisionRequest( unsigned& priority );
  /** increment the number of times we have successfully done candidate refinement */
  void incrementRefineCount() { d_refine_count++; }
  /** whether the conjecture is waiting for a call to doRefine */
  bool needsRefinement();
  /** get the list of candidates */
  void getCandidateList( std::vector< Node >& clist, bool forceOrig = false );
  /** record instantiation */
  void recordInstantiation( std::vector< Node >& vs ) {
    Assert( vs.size()==d_candidates.size() );
    for( unsigned i=0; i<vs.size(); i++ ){
      d_cinfo[d_candidates[i]].d_inst.push_back( vs[i] );
    }
  }
public:
  /** do single invocation check */
  void doSingleInvCheck(std::vector< Node >& lems);
  /** do syntax-guided enumerative check */
  void doCheck(std::vector< Node >& lems, std::vector< Node >& model_values);
  /** do refinement */
  void doRefine(std::vector< Node >& lems);
public:
  /** print out debug information about this conjecture */
  void debugPrint( const char * c );
  /** print the synthesis solution
   * singleInvocation is whether to print the solution from single invocation techniques.
   */
  void printSynthSolution( std::ostream& out, bool singleInvocation );
public:
  /** get guard */
  Node getGuard();
  /** is ground */
  bool isGround() { return d_inner_vars.empty(); }
  /** is syntax guided */
  bool isSyntaxGuided() const { return d_syntax_guided; }
  /** is single invocation */
  bool isSingleInvocation() const;
  /** needs check */
  bool needsCheck( std::vector< Node >& lem );
  /** preregister conjecture */
  void preregisterConjecture( Node q );
  /** assign */
  void assign( Node q );
  /** is assigned */
  bool isAssigned() { return !d_embed_quant.isNull(); }
  /** get model values */
  void getModelValues( std::vector< Node >& n, std::vector< Node >& v );
  /** get model value */
  Node getModelValue( Node n );
  /** get number of refinement lemmas */
  unsigned getNumRefinementLemmas() { return d_refinement_lemmas.size(); }
  /** get refinement lemma */
  Node getRefinementLemma( unsigned i ) { return d_refinement_lemmas[i]; }
  /** get refinement lemma */
  Node getRefinementBaseLemma( unsigned i ) { return d_refinement_lemmas_base[i]; }
};

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */

#endif
