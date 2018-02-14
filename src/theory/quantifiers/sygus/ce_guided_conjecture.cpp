/*********************                                                        */
/*! \file ce_guided_conjecture.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief implementation of class that encapsulates counterexample-guided instantiation
 **        techniques for a single SyGuS synthesis conjecture
 **/
#include "theory/quantifiers/ce_guided_conjecture.h"

#include "expr/datatype.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "prop/prop_engine.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/ce_guided_instantiation.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/skolemize.h"
#include "theory/quantifiers/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/theory_engine.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

// recursion is not an issue since OR nodes are flattened by the (quantifiers) rewriter
// this function is for sanity since solution correctness in SyGuS depends on fully miniscoping based on this function
void collectDisjuncts( Node n, std::vector< Node >& d ) {
  if( n.getKind()==OR ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      collectDisjuncts( n[i], d );
    }
  }else{
    d.push_back( n );
  }
}

CegConjecture::CegConjecture(QuantifiersEngine* qe)
    : d_qe(qe),
      d_ceg_si(new CegConjectureSingleInv(qe, this)),
      d_ceg_pbe(new CegConjecturePbe(qe, this)),
      d_ceg_proc(new CegConjectureProcess(qe)),
      d_ceg_gc(new CegGrammarConstructor(qe, this)),
      d_refine_count(0),
      d_syntax_guided(false) {}

CegConjecture::~CegConjecture() {}

void CegConjecture::assign( Node q ) {
  Assert( d_embed_quant.isNull() );
  Assert( q.getKind()==FORALL );
  Trace("cegqi") << "CegConjecture : assign : " << q << std::endl;
  d_quant = q;

  // pre-simplify the quantified formula based on the process utility
  d_simp_quant = d_ceg_proc->preSimplify(d_quant);

  std::map< Node, Node > templates; 
  std::map< Node, Node > templates_arg;
  //register with single invocation if applicable
  if (d_qe->getQuantAttributes()->isSygus(q))
  {
    d_ceg_si->initialize(d_simp_quant);
    d_simp_quant = d_ceg_si->getSimplifiedConjecture();
    // carry the templates
    for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
      Node v = q[0][i];
      Node templ = d_ceg_si->getTemplate(v);
      if( !templ.isNull() ){
        templates[v] = templ;
        templates_arg[v] = d_ceg_si->getTemplateArg(v);
      }
    }
  }

  // post-simplify the quantified formula based on the process utility
  d_simp_quant = d_ceg_proc->postSimplify(d_simp_quant);

  // finished simplifying the quantified formula at this point

  // convert to deep embedding and finalize single invocation here
  d_embed_quant = d_ceg_gc->process(d_simp_quant, templates, templates_arg);
  Trace("cegqi") << "CegConjecture : converted to embedding : " << d_embed_quant << std::endl;

  // we now finalize the single invocation module, based on the syntax restrictions
  if (d_qe->getQuantAttributes()->isSygus(q))
  {
    d_ceg_si->finishInit( d_ceg_gc->isSyntaxRestricted(), d_ceg_gc->hasSyntaxITE() );
  }

  Assert( d_candidates.empty() );
  std::vector< Node > vars;
  for( unsigned i=0; i<d_embed_quant[0].getNumChildren(); i++ ){
    vars.push_back( d_embed_quant[0][i] );
    Node e = NodeManager::currentNM()->mkSkolem( "e", d_embed_quant[0][i].getType() );
    d_candidates.push_back( e );
  }
  Trace("cegqi") << "Base quantified formula is : " << d_embed_quant << std::endl;
  //construct base instantiation
  d_base_inst = Rewriter::rewrite(d_qe->getInstantiate()->getInstantiation(
      d_embed_quant, vars, d_candidates));
  Trace("cegqi") << "Base instantiation is :      " << d_base_inst << std::endl;
  d_base_body = d_base_inst;
  if (d_base_body.getKind() == NOT && d_base_body[0].getKind() == FORALL)
  {
    for (const Node& v : d_base_body[0][0])
    {
      d_base_vars.push_back(v);
    }
    d_base_body = d_base_body[0][1];
  }

  // register this term with sygus database and other utilities that impact
  // the enumerative sygus search
  std::vector< Node > guarded_lemmas;
  if( !isSingleInvocation() ){
    d_ceg_proc->initialize(d_base_inst, d_candidates);
    if( options::sygusPbe() ){
      d_ceg_pbe->initialize(d_base_inst, d_candidates, guarded_lemmas);
    } else {
      for (unsigned i = 0; i < d_candidates.size(); i++) {
        Node e = d_candidates[i];
        d_qe->getTermDatabaseSygus()->registerEnumerator(e, e, this);
      }
    }
  }

  if (d_qe->getQuantAttributes()->isSygus(q))
  {
    collectDisjuncts( d_base_inst, d_base_disj );
    Trace("cegqi") << "Conjecture has " << d_base_disj.size() << " disjuncts." << std::endl;
    //store the inner variables for each disjunct
    for( unsigned j=0; j<d_base_disj.size(); j++ ){
      Trace("cegqi") << "  " << j << " : " << d_base_disj[j] << std::endl;
      d_inner_vars_disj.push_back( std::vector< Node >() );
      //if the disjunct is an existential, store it
      if( d_base_disj[j].getKind()==NOT && d_base_disj[j][0].getKind()==FORALL ){
        for( unsigned k=0; k<d_base_disj[j][0][0].getNumChildren(); k++ ){
          d_inner_vars.push_back( d_base_disj[j][0][0][k] );
          d_inner_vars_disj[j].push_back( d_base_disj[j][0][0][k] );
        }
      }
    }
    d_syntax_guided = true;
  }
  else if (d_qe->getQuantAttributes()->isSynthesis(q))
  {
    d_syntax_guided = false;
  }else{
    Assert( false );
  }
  
  // initialize the guard
  if( !d_syntax_guided ){
    if( d_nsg_guard.isNull() ){
      d_nsg_guard = Rewriter::rewrite( NodeManager::currentNM()->mkSkolem( "G", NodeManager::currentNM()->booleanType() ) );
      d_nsg_guard = d_qe->getValuation().ensureLiteral( d_nsg_guard );
      AlwaysAssert( !d_nsg_guard.isNull() );
      d_qe->getOutputChannel().requirePhase( d_nsg_guard, true );
      // negated base as a guarded lemma
      guarded_lemmas.push_back( d_base_inst.negate() );
    }
  }else if( d_ceg_si->getGuard().isNull() ){
    std::vector< Node > lems;
    d_ceg_si->getInitialSingleInvLemma( lems );
    for( unsigned i=0; i<lems.size(); i++ ){
      Trace("cegqi-lemma") << "Cegqi::Lemma : single invocation " << i << " : " << lems[i] << std::endl;
      d_qe->getOutputChannel().lemma( lems[i] );
      if( Trace.isOn("cegqi-debug") ){
        Node rlem = Rewriter::rewrite( lems[i] );
        Trace("cegqi-debug") << "...rewritten : " << rlem << std::endl;
      }
    }
  }
  Assert( !getGuard().isNull() );
  Node gneg = getGuard().negate();
  for( unsigned i=0; i<guarded_lemmas.size(); i++ ){
    Node lem = NodeManager::currentNM()->mkNode( OR, gneg, guarded_lemmas[i] );
    Trace("cegqi-lemma") << "Cegqi::Lemma : initial (guarded) lemma : " << lem << std::endl;
    d_qe->getOutputChannel().lemma( lem );
  }

  // assign the cegis sampler if applicable
  if (options::cegisSample() != CEGIS_SAMPLE_NONE)
  {
    Trace("cegis-sample") << "Initialize sampler for " << d_base_body << "..."
                          << std::endl;
    TypeNode bt = d_base_body.getType();
    d_cegis_sampler.initialize(bt, d_base_vars, options::sygusSamples());
  }

  Trace("cegqi") << "...finished, single invocation = " << isSingleInvocation() << std::endl;
}

Node CegConjecture::getGuard() {
  return !d_syntax_guided ? d_nsg_guard : d_ceg_si->getGuard();
}

bool CegConjecture::isSingleInvocation() const {
  return d_ceg_si->isSingleInvocation();
}

bool CegConjecture::needsCheck( std::vector< Node >& lem ) {
  if( isSingleInvocation() && !d_ceg_si->needsCheck() ){
    return false;
  }else{
    bool value;
    Assert( !getGuard().isNull() );
    // non or fully single invocation : look at guard only
    if( d_qe->getValuation().hasSatValue( getGuard(), value ) ) {
      if( !value ){
        Trace("cegqi-engine-debug") << "Conjecture is infeasible." << std::endl;
        return false;
      }
    }else{
      Assert( false );
    }
    return true;
  }
}


void CegConjecture::doSingleInvCheck(std::vector< Node >& lems) {
  if( d_ceg_si!=NULL ){
    d_ceg_si->check(lems);
  }
}

void CegConjecture::doBasicCheck(std::vector< Node >& lems) {
  std::vector< Node > model_terms;
  std::vector< Node > clist;
  getCandidateList( clist, true );
  Assert( clist.size()==d_quant[0].getNumChildren() );
  getModelValues( clist, model_terms );
  if (d_qe->getInstantiate()->addInstantiation(d_quant, model_terms))
  {
    //record the instantiation
    recordInstantiation( model_terms );
  }else{
    Assert( false );
  }
}

bool CegConjecture::needsRefinement() { 
  return !d_ce_sk.empty();
}

void CegConjecture::getCandidateList( std::vector< Node >& clist, bool forceOrig ) {
  if( d_ceg_pbe->isPbe() && !forceOrig ){
    d_ceg_pbe->getCandidateList( d_candidates, clist );
  }else{
    clist.insert( clist.end(), d_candidates.begin(), d_candidates.end() );
  }
}

bool CegConjecture::constructCandidates( std::vector< Node >& clist, std::vector< Node >& model_values, std::vector< Node >& candidate_values, 
                                         std::vector< Node >& lems ) {
  Assert( clist.size()==model_values.size() );
  if( d_ceg_pbe->isPbe() ){
    return d_ceg_pbe->constructCandidates( clist, model_values, d_candidates, candidate_values, lems );
  }else{
    Assert( model_values.size()==d_candidates.size() );
    candidate_values.insert( candidate_values.end(), model_values.begin(), model_values.end() );
  }
  return true;
}

void CegConjecture::doCheck(std::vector< Node >& lems, std::vector< Node >& model_values) {
  std::vector< Node > clist;
  getCandidateList( clist );
  std::vector< Node > c_model_values;
  Trace("cegqi-check") << "CegConjuncture : check, build candidates..." << std::endl;
  bool constructed_cand = constructCandidates( clist, model_values, c_model_values, lems );

  //must get a counterexample to the value of the current candidate
  Node inst;
  if( constructed_cand ){
    if( Trace.isOn("cegqi-check")  ){
      Trace("cegqi-check") << "CegConjuncture : check candidate : " << std::endl;
      for( unsigned i=0; i<c_model_values.size(); i++ ){
        Trace("cegqi-check") << "  " << i << " : " << d_candidates[i] << " -> " << c_model_values[i] << std::endl;
      }
    }
    Assert( c_model_values.size()==d_candidates.size() );
    inst = d_base_inst.substitute( d_candidates.begin(), d_candidates.end(), c_model_values.begin(), c_model_values.end() );
  }else{
    inst = d_base_inst;
  }
  
  //check whether we will run CEGIS on inner skolem variables
  bool sk_refine = ( !isGround() || d_refine_count==0 ) && ( !d_ceg_pbe->isPbe() || constructed_cand );
  if( sk_refine ){
    if (options::cegisSample() == CEGIS_SAMPLE_TRUST)
    {
      // we have that the current candidate passed a sample test
      // since we trust sampling in this mode, we assert there is no
      // counterexample to the conjecture here.
      NodeManager* nm = NodeManager::currentNM();
      Node lem = nm->mkNode(OR, d_quant.negate(), nm->mkConst(false));
      lem = getStreamGuardedLemma(lem);
      lems.push_back(lem);
      recordInstantiation(c_model_values);
      return;
    }
    Assert( d_ce_sk.empty() );
    d_ce_sk.push_back( std::vector< Node >() );
  }else{
    if( !constructed_cand ){
      return;
    }
  }
  
  std::vector< Node > ic;
  ic.push_back( d_quant.negate() );
  std::vector< Node > d;
  collectDisjuncts( inst, d );
  Assert( d.size()==d_base_disj.size() );
  //immediately skolemize inner existentials
  for( unsigned i=0; i<d.size(); i++ ){
    Node dr = Rewriter::rewrite( d[i] );
    if( dr.getKind()==NOT && dr[0].getKind()==FORALL ){
      if( constructed_cand ){
        ic.push_back(d_qe->getSkolemize()->getSkolemizedBody(dr[0]).negate());
      }
      if( sk_refine ){
        Assert( !isGround() );
        d_ce_sk.back().push_back( dr[0] );
      }
    }else{
      if( constructed_cand ){
        ic.push_back( dr );
        if( !d_inner_vars_disj[i].empty() ){
          Trace("cegqi-debug") << "*** quantified disjunct : " << d[i] << " simplifies to " << dr << std::endl;
        }
      }
      if( sk_refine ){
        d_ce_sk.back().push_back( Node::null() );
      }
    }
  }
  if( constructed_cand ){
    Node lem = NodeManager::currentNM()->mkNode( OR, ic );
    lem = Rewriter::rewrite( lem );
    //eagerly unfold applications of evaluation function
    if( options::sygusDirectEval() ){
      Trace("cegqi-debug") << "pre-unfold counterexample : " << lem << std::endl;
      std::map< Node, Node > visited_n;
      lem = d_qe->getTermDatabaseSygus()->getEagerUnfold( lem, visited_n );
    }
    lem = getStreamGuardedLemma(lem);
    lems.push_back( lem );
    recordInstantiation( c_model_values );
  }
}
        
void CegConjecture::doRefine( std::vector< Node >& lems ){
  Assert( lems.empty() );
  Assert( d_ce_sk.size()==1 );

  //first, make skolem substitution
  Trace("cegqi-refine") << "doRefine : construct skolem substitution..." << std::endl;
  std::vector< Node > sk_vars;
  std::vector< Node > sk_subs;
  //collect the substitution over all disjuncts
  for( unsigned k=0; k<d_ce_sk[0].size(); k++ ){
    Node ce_q = d_ce_sk[0][k];
    if( !ce_q.isNull() ){
      Assert( !d_inner_vars_disj[k].empty() );
      std::vector<Node> skolems;
      d_qe->getSkolemize()->getSkolemConstants(ce_q, skolems);
      Assert(d_inner_vars_disj[k].size() == skolems.size());
      std::vector< Node > model_values;
      getModelValues(skolems, model_values);
      sk_vars.insert( sk_vars.end(), d_inner_vars_disj[k].begin(), d_inner_vars_disj[k].end() );
      sk_subs.insert( sk_subs.end(), model_values.begin(), model_values.end() );
    }else{
      if( !d_inner_vars_disj[k].empty() ){
        //denegrate case : quantified disjunct was trivially true and does not need to be refined
        //add trivial substitution (in case we need substitution for previous cex's)
        for( unsigned i=0; i<d_inner_vars_disj[k].size(); i++ ){
          sk_vars.push_back( d_inner_vars_disj[k][i] );
          sk_subs.push_back( getModelValue( d_inner_vars_disj[k][i] ) ); // will return dummy value
        }
      }
    }
  } 
  
  //for conditional evaluation
  std::vector< Node > lem_c;
  Assert( d_ce_sk[0].size()==d_base_disj.size() );
  std::vector< Node > inst_cond_c;
  Trace("cegqi-refine") << "doRefine : Construct refinement lemma..." << std::endl;
  for( unsigned k=0; k<d_ce_sk[0].size(); k++ ){
    Node ce_q = d_ce_sk[0][k];
    Trace("cegqi-refine-debug") << "  For counterexample point, disjunct " << k << " : " << ce_q << " " << d_base_disj[k] << std::endl;
    Node c_disj;
    if( !ce_q.isNull() ){
      Assert( d_base_disj[k].getKind()==kind::NOT && d_base_disj[k][0].getKind()==kind::FORALL );
      c_disj = d_base_disj[k][0][1];
    }else{
      if( d_inner_vars_disj[k].empty() ){
        c_disj = d_base_disj[k].negate();
      }else{
        //denegrate case : quantified disjunct was trivially true and does not need to be refined
        Trace("cegqi-refine-debug") << "*** skip " << d_base_disj[k] << std::endl;
      }
    }
    if( !c_disj.isNull() ){
      //compute the body, inst_cond
      //standard CEGIS refinement : plug in values, assert that d_candidates must satisfy entire specification
      lem_c.push_back( c_disj );
    }
  }
  Assert( sk_vars.size()==sk_subs.size() );
  
  Node base_lem = lem_c.size()==1 ? lem_c[0] : NodeManager::currentNM()->mkNode( AND, lem_c );
  
  Trace("cegqi-refine") << "doRefine : construct and finalize lemmas..." << std::endl;
  
  
  base_lem = base_lem.substitute( sk_vars.begin(), sk_vars.end(), sk_subs.begin(), sk_subs.end() );
  base_lem = Rewriter::rewrite( base_lem );
  d_refinement_lemmas.push_back(base_lem);

  Node lem =
      NodeManager::currentNM()->mkNode(OR, getGuard().negate(), base_lem);
  lems.push_back( lem );

  d_ce_sk.clear();
}

void CegConjecture::preregisterConjecture( Node q ) {
  d_ceg_si->preregisterConjecture( q );
}

void CegConjecture::getModelValues( std::vector< Node >& n, std::vector< Node >& v ) {
  Trace("cegqi-engine") << "  * Value is : ";
  for( unsigned i=0; i<n.size(); i++ ){
    Node nv = getModelValue( n[i] );
    v.push_back( nv );
    if( Trace.isOn("cegqi-engine") ){
      TypeNode tn = nv.getType();
      Trace("cegqi-engine") << n[i] << " -> ";
      std::stringstream ss;
      Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, nv);
      Trace("cegqi-engine") << ss.str() << " ";
      if (Trace.isOn("cegqi-engine-rr"))
      {
        Node bv = d_qe->getTermDatabaseSygus()->sygusToBuiltin(nv, tn);
        bv = Rewriter::rewrite(bv);
        Trace("cegqi-engine-rr") << " -> " << bv << std::endl;
      }
    }
    Assert( !nv.isNull() );
  }
  Trace("cegqi-engine") << std::endl;
}

Node CegConjecture::getModelValue( Node n ) {
  Trace("cegqi-mv") << "getModelValue for : " << n << std::endl;
  return d_qe->getModel()->getValue( n );
}

void CegConjecture::debugPrint( const char * c ) {
  Trace(c) << "Synthesis conjecture : " << d_embed_quant << std::endl;
  Trace(c) << "  * Candidate program/output symbol : ";
  for( unsigned i=0; i<d_candidates.size(); i++ ){
    Trace(c) << d_candidates[i] << " ";
  }
  Trace(c) << std::endl;
  Trace(c) << "  * Candidate ce skolems : ";
  for( unsigned i=0; i<d_ce_sk.size(); i++ ){
    Trace(c) << d_ce_sk[i] << " ";
  }
}

Node CegConjecture::getCurrentStreamGuard() const {
  if( d_stream_guards.empty() ){
    return Node::null();
  }else{
    return d_stream_guards.back();
  }
}

Node CegConjecture::getStreamGuardedLemma(Node n) const
{
  if (options::sygusStream())
  {
    // if we are in streaming mode, we guard with the current stream guard
    Node csg = getCurrentStreamGuard();
    Assert(!csg.isNull());
    return NodeManager::currentNM()->mkNode(kind::OR, csg.negate(), n);
  }
  return n;
}

Node CegConjecture::getNextDecisionRequest( unsigned& priority ) {
  // first, must try the guard
  // which denotes "this conjecture is feasible"
  Node feasible_guard = getGuard();
  bool value;
  if( !d_qe->getValuation().hasSatValue( feasible_guard, value ) ) {
    priority = 0;
    return feasible_guard;
  }else{
    if( value ){  
      // the conjecture is feasible
      if( options::sygusStream() ){
        Assert( !isSingleInvocation() );
        // if we are in sygus streaming mode, then get the "next guard" 
        // which denotes "we have not yet generated the next solution to the conjecture"
        Node curr_stream_guard = getCurrentStreamGuard();
        bool needs_new_stream_guard = false;
        if( curr_stream_guard.isNull() ){
          needs_new_stream_guard = true;
        }else{
          // check the polarity of the guard
          if( !d_qe->getValuation().hasSatValue( curr_stream_guard, value ) ) {
            priority = 0;
            return curr_stream_guard;
          }else{
            if( !value ){
              Trace("cegqi-debug") << "getNextDecision : we have a new solution since stream guard was propagated false: " << curr_stream_guard << std::endl;
              // we have generated a solution, print it
              // get the current output stream
              // this output stream should coincide with wherever --dump-synth is output on
              Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
              printSynthSolution( *nodeManagerOptions.getOut(), false );
              // need to make the next stream guard
              needs_new_stream_guard = true;
              
              // We will not refine the current candidate solution since it is a solution
              // thus, we clear information regarding the current refinement
              d_ce_sk.clear();
              // However, we need to exclude the current solution using an explicit refinement 
              // so that we proceed to the next solution. 
              std::vector< Node > clist;
              getCandidateList( clist );
              Trace("cegqi-debug") << "getNextDecision : solution was : " << std::endl;
              std::vector< Node > exp;
              for( unsigned i=0; i<clist.size(); i++ ){
                Node cprog = clist[i];
                Node sol = cprog;
                if( !d_cinfo[cprog].d_inst.empty() ){
                  sol = d_cinfo[cprog].d_inst.back();
                  // add to explanation of exclusion
                  d_qe->getTermDatabaseSygus()
                      ->getExplain()
                      ->getExplanationForConstantEquality(cprog, sol, exp);
                }
                Trace("cegqi-debug") << "  " << cprog << " -> " << sol << std::endl;
              }
              Assert( !exp.empty() );
              Node exc_lem = exp.size()==1 ? exp[0] : NodeManager::currentNM()->mkNode( kind::AND, exp );
              exc_lem = exc_lem.negate();
              Trace("cegqi-lemma") << "Cegqi::Lemma : stream exclude current solution : " << exc_lem << std::endl;
              d_qe->getOutputChannel().lemma( exc_lem );
            }
          }
        }
        if( needs_new_stream_guard ){
          // generate a new stream guard
          curr_stream_guard = Rewriter::rewrite( NodeManager::currentNM()->mkSkolem( "G_Stream", NodeManager::currentNM()->booleanType() ) );
          curr_stream_guard = d_qe->getValuation().ensureLiteral( curr_stream_guard );
          AlwaysAssert( !curr_stream_guard.isNull() );
          d_qe->getOutputChannel().requirePhase( curr_stream_guard, true );
          d_stream_guards.push_back( curr_stream_guard );
          Trace("cegqi-debug") << "getNextDecision : allocate new stream guard : " << curr_stream_guard << std::endl;
          // return it as a decision
          priority = 0;
          return curr_stream_guard;
        }
      }
    }else{
      Trace("cegqi-debug") << "getNextDecision : conjecture is infeasible." << std::endl;
    } 
  }
  return Node::null();
}

void CegConjecture::printSynthSolution( std::ostream& out, bool singleInvocation ) {
  Trace("cegqi-debug") << "Printing synth solution..." << std::endl;
  Assert( d_quant[0].getNumChildren()==d_embed_quant[0].getNumChildren() );
  std::vector<Node> sols;
  std::vector<int> statuses;
  getSynthSolutionsInternal(sols, statuses, singleInvocation);
  for (unsigned i = 0, size = d_embed_quant[0].getNumChildren(); i < size; i++)
  {
    Node sol = sols[i];
    if (!sol.isNull())
    {
      Node prog = d_embed_quant[0][i];
      int status = statuses[i];
      TypeNode tn = prog.getType();
      const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
      std::stringstream ss;
      ss << prog;
      std::string f(ss.str());
      f.erase(f.begin());
      out << "(define-fun " << f << " ";
      if( dt.getSygusVarList().isNull() ){
        out << "() ";
      }else{
        out << dt.getSygusVarList() << " ";
      }
      out << dt.getSygusType() << " ";
      if( status==0 ){
        out << sol;
      }else{
        Printer::getPrinter(options::outputLanguage())->toStreamSygus(out, sol);
      }
      out << ")" << std::endl;
      CegInstantiation* cei = d_qe->getCegInstantiation();
      ++(cei->d_statistics.d_solutions);

      if (status != 0 && options::sygusRewSynth())
      {
        TermDbSygus* sygusDb = d_qe->getTermDatabaseSygus();
        std::map<Node, SygusSamplerExt>::iterator its = d_sampler.find(prog);
        if (its == d_sampler.end())
        {
          d_sampler[prog].initializeSygusExt(
              d_qe, prog, options::sygusSamples());
          its = d_sampler.find(prog);
        }
        Node solb = sygusDb->sygusToBuiltin(sol, prog.getType());
        Node eq_sol = its->second.registerTerm(solb);
        // eq_sol is a candidate solution that is equivalent to sol
        if (eq_sol != solb)
        {
          ++(cei->d_statistics.d_candidate_rewrites);
          if (!eq_sol.isNull())
          {
            // Terms solb and eq_sol are equivalent under sample points but do
            // not rewrite to the same term. Hence, this indicates a candidate
            // rewrite.
            out << "(candidate-rewrite " << solb << " " << eq_sol << ")"
                << std::endl;
            ++(cei->d_statistics.d_candidate_rewrites_print);
            // debugging information
            if (Trace.isOn("sygus-rr-debug"))
            {
              ExtendedRewriter* er = sygusDb->getExtRewriter();
              Node solbr = er->extendedRewrite(solb);
              Node eq_solr = er->extendedRewrite(eq_sol);
              Trace("sygus-rr-debug")
                  << "; candidate #1 ext-rewrites to: " << solbr << std::endl;
              Trace("sygus-rr-debug")
                  << "; candidate #2 ext-rewrites to: " << eq_solr << std::endl;
            }
          }
        }
      }
    }
  }
}

void CegConjecture::getSynthSolutions(std::map<Node, Node>& sol_map,
                                      bool singleInvocation)
{
  NodeManager* nm = NodeManager::currentNM();
  TermDbSygus* sygusDb = d_qe->getTermDatabaseSygus();
  std::vector<Node> sols;
  std::vector<int> statuses;
  getSynthSolutionsInternal(sols, statuses, singleInvocation);
  for (unsigned i = 0, size = d_embed_quant[0].getNumChildren(); i < size; i++)
  {
    Node sol = sols[i];
    int status = statuses[i];
    // get the builtin solution
    Node bsol = sol;
    if (status != 0)
    {
      // convert sygus to builtin here
      bsol = sygusDb->sygusToBuiltin(sol, sol.getType());
    }
    // convert to lambda
    TypeNode tn = d_embed_quant[0][i].getType();
    const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
    Node bvl = Node::fromExpr(dt.getSygusVarList());
    if (!bvl.isNull())
    {
      bsol = nm->mkNode(LAMBDA, bvl, bsol);
    }
    // store in map
    Node fvar = d_quant[0][i];
    Assert(fvar.getType() == bsol.getType());
    sol_map[fvar] = bsol;
  }
}

void CegConjecture::getSynthSolutionsInternal(std::vector<Node>& sols,
                                              std::vector<int>& statuses,
                                              bool singleInvocation)
{
  for (unsigned i = 0, size = d_embed_quant[0].getNumChildren(); i < size; i++)
  {
    Node prog = d_embed_quant[0][i];
    Trace("cegqi-debug") << "  get solution for " << prog << std::endl;
    TypeNode tn = prog.getType();
    Assert(tn.isDatatype());
    // get the solution
    Node sol;
    int status = -1;
    if (singleInvocation)
    {
      Assert(d_ceg_si != NULL);
      sol = d_ceg_si->getSolution(i, tn, status, true);
      if (!sol.isNull())
      {
        sol = sol.getKind() == LAMBDA ? sol[1] : sol;
      }
    }
    else
    {
      Node cprog = getCandidate(i);
      if (!d_cinfo[cprog].d_inst.empty())
      {
        // the solution is just the last instantiated term
        sol = d_cinfo[cprog].d_inst.back();
        status = 1;

        // check if there was a template
        Node sf = d_quant[0][i];
        Node templ = d_ceg_si->getTemplate(sf);
        if (!templ.isNull())
        {
          Trace("cegqi-inv-debug")
              << sf << " used template : " << templ << std::endl;
          // if it was not embedded into the grammar
          if (!options::sygusTemplEmbedGrammar())
          {
            TNode templa = d_ceg_si->getTemplateArg(sf);
            // make the builtin version of the full solution
            TermDbSygus* sygusDb = d_qe->getTermDatabaseSygus();
            sol = sygusDb->sygusToBuiltin(sol, sol.getType());
            Trace("cegqi-inv") << "Builtin version of solution is : " << sol
                               << ", type : " << sol.getType() << std::endl;
            TNode tsol = sol;
            sol = templ.substitute(templa, tsol);
            Trace("cegqi-inv-debug") << "With template : " << sol << std::endl;
            sol = Rewriter::rewrite(sol);
            Trace("cegqi-inv-debug") << "Simplified : " << sol << std::endl;
            // now, reconstruct to the syntax
            sol = d_ceg_si->reconstructToSyntax(sol, tn, status, true);
            sol = sol.getKind() == LAMBDA ? sol[1] : sol;
            Trace("cegqi-inv-debug")
                << "Reconstructed to syntax : " << sol << std::endl;
          }
          else
          {
            Trace("cegqi-inv-debug")
                << "...was embedding into grammar." << std::endl;
          }
        }
        else
        {
          Trace("cegqi-inv-debug")
              << sf << " did not use template" << std::endl;
        }
      }
      else
      {
        Trace("cegqi-warn") << "WARNING : No recorded instantiations for "
                               "syntax-guided solution!"
                            << std::endl;
      }
    }
    sols.push_back(sol);
    statuses.push_back(status);
  }
}

Node CegConjecture::getSymmetryBreakingPredicate(
    Node x, Node e, TypeNode tn, unsigned tindex, unsigned depth)
{
  std::vector<Node> sb_lemmas;

  // based on simple preprocessing
  Node ppred =
      d_ceg_proc->getSymmetryBreakingPredicate(x, e, tn, tindex, depth);
  if (!ppred.isNull())
  {
    sb_lemmas.push_back(ppred);
  }

  // other static conjecture-dependent symmetry breaking goes here

  if (!sb_lemmas.empty())
  {
    return sb_lemmas.size() == 1
               ? sb_lemmas[0]
               : NodeManager::currentNM()->mkNode(kind::AND, sb_lemmas);
  }
  else
  {
    return Node::null();
  }
}

bool CegConjecture::sampleAddRefinementLemma(std::vector<Node>& vals,
                                             std::vector<Node>& lems)
{
  if (Trace.isOn("cegis-sample"))
  {
    Trace("cegis-sample") << "Check sampling for candidate solution"
                          << std::endl;
    for (unsigned i = 0, size = vals.size(); i < size; i++)
    {
      Trace("cegis-sample")
          << "  " << d_candidates[i] << " -> " << vals[i] << std::endl;
    }
  }
  Assert(vals.size() == d_candidates.size());
  Node sbody = d_base_body.substitute(
      d_candidates.begin(), d_candidates.end(), vals.begin(), vals.end());
  Trace("cegis-sample-debug") << "Sample " << sbody << std::endl;
  // do eager unfolding
  std::map<Node, Node> visited_n;
  sbody = d_qe->getTermDatabaseSygus()->getEagerUnfold(sbody, visited_n);
  Trace("cegis-sample") << "Sample (after unfolding): " << sbody << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, size = d_cegis_sampler.getNumSamplePoints(); i < size;
       i++)
  {
    if (d_cegis_sample_refine.find(i) == d_cegis_sample_refine.end())
    {
      Node ev = d_cegis_sampler.evaluate(sbody, i);
      Trace("cegis-sample-debug")
          << "...evaluate point #" << i << " to " << ev << std::endl;
      Assert(ev.isConst());
      Assert(ev.getType().isBoolean());
      if (!ev.getConst<bool>())
      {
        Trace("cegis-sample-debug") << "...false for point #" << i << std::endl;
        // mark this as a CEGIS point (no longer sampled)
        d_cegis_sample_refine.insert(i);
        std::vector<Node> vars;
        std::vector<Node> pt;
        d_cegis_sampler.getSamplePoint(i, vars, pt);
        Assert(d_base_vars.size() == pt.size());
        Node rlem = d_base_body.substitute(
            d_base_vars.begin(), d_base_vars.end(), pt.begin(), pt.end());
        rlem = Rewriter::rewrite(rlem);
        if (std::find(
                d_refinement_lemmas.begin(), d_refinement_lemmas.end(), rlem)
            == d_refinement_lemmas.end())
        {
          if (Trace.isOn("cegis-sample"))
          {
            Trace("cegis-sample") << "   false for point #" << i << " : ";
            for (const Node& cn : pt)
            {
              Trace("cegis-sample") << cn << " ";
            }
            Trace("cegis-sample") << std::endl;
          }
          Trace("cegqi-engine") << "  *** Refine by sampling" << std::endl;
          d_refinement_lemmas.push_back(rlem);
          // if trust, we are not interested in sending out refinement lemmas
          if (options::cegisSample() != CEGIS_SAMPLE_TRUST)
          {
            Node lem = nm->mkNode(OR, getGuard().negate(), rlem);
            lems.push_back(lem);
          }
          return true;
        }
        else
        {
          Trace("cegis-sample-debug") << "...duplicate." << std::endl;
        }
      }
    }
  }
  return false;
}

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */
