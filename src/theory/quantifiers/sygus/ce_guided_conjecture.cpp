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
#include "theory/quantifiers/sygus/ce_guided_conjecture.h"

#include "expr/datatype.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "prop/prop_engine.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/sygus/ce_guided_instantiation.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/skolemize.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/theory_engine.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegConjecture::CegConjecture(QuantifiersEngine* qe)
    : d_qe(qe),
      d_ceg_si(new CegConjectureSingleInv(qe, this)),
      d_ceg_proc(new CegConjectureProcess(qe)),
      d_ceg_gc(new CegGrammarConstructor(qe, this)),
      d_ceg_pbe(new CegConjecturePbe(qe, this)),
      d_ceg_cegis(new Cegis(qe, this)),
      d_master(nullptr),
      d_refine_count(0),
      d_syntax_guided(false)
{
  if (options::sygusPbe())
  {
    d_modules.push_back(d_ceg_pbe.get());
  }
  d_modules.push_back(d_ceg_cegis.get());
}

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

  // register this term with sygus database and other utilities that impact
  // the enumerative sygus search
  std::vector< Node > guarded_lemmas;
  if( !isSingleInvocation() ){
    d_ceg_proc->initialize(d_base_inst, d_candidates);
    for (unsigned i = 0, size = d_modules.size(); i < size; i++)
    {
      if (d_modules[i]->initialize(d_base_inst, d_candidates, guarded_lemmas))
      {
        d_master = d_modules[i];
        break;
      }
    }
    Assert(d_master != nullptr);
  }

  if (d_qe->getQuantAttributes()->isSygus(q))
  {
    // if the base instantiation is an existential, store its variables
    if (d_base_inst.getKind() == NOT && d_base_inst[0].getKind() == FORALL)
    {
      for (const Node& v : d_base_inst[0][0])
      {
        d_inner_vars.push_back(v);
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
  Assert(d_candidates.size() == d_quant[0].getNumChildren());
  getModelValues(d_candidates, model_terms);
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

void CegConjecture::doCheck(std::vector<Node>& lems)
{
  Assert(d_master != nullptr);

  // get the list of terms that the master strategy is interested in
  std::vector<Node> terms;
  d_master->getTermList(d_candidates, terms);

  // get their model value
  std::vector<Node> enum_values;
  getModelValues(terms, enum_values);

  std::vector<Node> candidate_values;
  Trace("cegqi-check") << "CegConjuncture : check, build candidates..." << std::endl;
  bool constructed_cand = d_master->constructCandidates(
      terms, enum_values, d_candidates, candidate_values, lems);

  NodeManager* nm = NodeManager::currentNM();

  //must get a counterexample to the value of the current candidate
  Node inst;
  if( constructed_cand ){
    if( Trace.isOn("cegqi-check")  ){
      Trace("cegqi-check") << "CegConjuncture : check candidate : " << std::endl;
      for (unsigned i = 0, size = candidate_values.size(); i < size; i++)
      {
        Trace("cegqi-check") << "  " << i << " : " << d_candidates[i] << " -> "
                             << candidate_values[i] << std::endl;
      }
    }
    Assert(candidate_values.size() == d_candidates.size());
    inst = d_base_inst.substitute(d_candidates.begin(),
                                  d_candidates.end(),
                                  candidate_values.begin(),
                                  candidate_values.end());
  }else{
    inst = d_base_inst;
  }
  
  //check whether we will run CEGIS on inner skolem variables
  bool sk_refine = (!isGround() || d_refine_count == 0) && constructed_cand;
  if( sk_refine ){
    if (options::cegisSample() == CEGIS_SAMPLE_TRUST)
    {
      // we have that the current candidate passed a sample test
      // since we trust sampling in this mode, we assert there is no
      // counterexample to the conjecture here.
      Node lem = nm->mkNode(OR, d_quant.negate(), nm->mkConst(false));
      lem = getStreamGuardedLemma(lem);
      lems.push_back(lem);
      recordInstantiation(candidate_values);
      return;
    }
    Assert( d_ce_sk.empty() );
  }else{
    if( !constructed_cand ){
      return;
    }
  }
  
  //immediately skolemize inner existentials
  Node instr = Rewriter::rewrite(inst);
  Node lem;
  if (instr.getKind() == NOT && instr[0].getKind() == FORALL)
  {
    if (constructed_cand)
    {
      lem = d_qe->getSkolemize()->getSkolemizedBody(instr[0]).negate();
    }
    if (sk_refine)
    {
      Assert(!isGround());
      d_ce_sk.push_back(instr[0]);
    }
  }
  else
  {
    if (constructed_cand)
    {
      // use the instance itself
      lem = instr;
    }
    if (sk_refine)
    {
      // we add null so that one test of the conjecture for the empty
      // substitution is checked
      d_ce_sk.push_back(Node::null());
    }
  }
  if (!lem.isNull())
  {
    lem = Rewriter::rewrite( lem );
    //eagerly unfold applications of evaluation function
    if( options::sygusDirectEval() ){
      Trace("cegqi-debug") << "pre-unfold counterexample : " << lem << std::endl;
      std::map< Node, Node > visited_n;
      lem = d_qe->getTermDatabaseSygus()->getEagerUnfold( lem, visited_n );
    }
    // record the instantiation
    // this is used for remembering the solution
    recordInstantiation(candidate_values);
    if (lem.isConst() && !lem.getConst<bool>() && options::sygusStream())
    {
      // short circuit the check
      // instead, we immediately print the current solution.
      // this saves us from introducing a check lemma and a new guard.
      printAndContinueStream();
    }
    else
    {
      // This is the "verification lemma", which states
      // either this conjecture does not have a solution, or candidate_values
      // is a solution for this conjecture.
      lem = nm->mkNode(OR, d_quant.negate(), lem);
      lem = getStreamGuardedLemma(lem);
      lems.push_back(lem);
    }
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
  Node ce_q = d_ce_sk[0];
  if (!ce_q.isNull())
  {
    std::vector<Node> skolems;
    d_qe->getSkolemize()->getSkolemConstants(ce_q, skolems);
    Assert(d_inner_vars.size() == skolems.size());
    std::vector<Node> model_values;
    getModelValues(skolems, model_values);
    sk_vars.insert(sk_vars.end(), d_inner_vars.begin(), d_inner_vars.end());
    sk_subs.insert(sk_subs.end(), model_values.begin(), model_values.end());
  }
  else
  {
    Assert(d_inner_vars.empty());
  }

  std::vector< Node > lem_c;
  Trace("cegqi-refine") << "doRefine : Construct refinement lemma..." << std::endl;
  Trace("cegqi-refine-debug")
      << "  For counterexample point : " << ce_q << std::endl;
  Node base_lem;
  if (!ce_q.isNull())
  {
    Assert(d_base_inst.getKind() == kind::NOT
           && d_base_inst[0].getKind() == kind::FORALL);
    base_lem = d_base_inst[0][1];
  }
  else
  {
    base_lem = d_base_inst.negate();
  }

  Assert( sk_vars.size()==sk_subs.size() );

  Trace("cegqi-refine") << "doRefine : construct and finalize lemmas..." << std::endl;

  base_lem = base_lem.substitute( sk_vars.begin(), sk_vars.end(), sk_subs.begin(), sk_subs.end() );
  base_lem = Rewriter::rewrite( base_lem );
  d_master->registerRefinementLemma(sk_vars, base_lem, lems);

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
              // need to make the next stream guard
              needs_new_stream_guard = true;
              // the guard has propagated false, indicating that a verify
              // lemma was unsatisfiable. Hence, the previous candidate is
              // an actual solution. We print and continue the stream.
              printAndContinueStream();
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

void CegConjecture::printAndContinueStream()
{
  Assert(d_master != nullptr);
  // we have generated a solution, print it
  // get the current output stream
  // this output stream should coincide with wherever --dump-synth is output on
  Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
  printSynthSolution(*nodeManagerOptions.getOut(), false);

  // We will not refine the current candidate solution since it is a solution
  // thus, we clear information regarding the current refinement
  d_ce_sk.clear();
  // However, we need to exclude the current solution using an explicit
  // blocking clause, so that we proceed to the next solution.
  std::vector<Node> terms;
  d_master->getTermList(d_candidates, terms);
  std::vector<Node> exp;
  for (const Node& cprog : terms)
  {
    Node sol = cprog;
    if (!d_cinfo[cprog].d_inst.empty())
    {
      sol = d_cinfo[cprog].d_inst.back();
      // add to explanation of exclusion
      d_qe->getTermDatabaseSygus()
          ->getExplain()
          ->getExplanationForConstantEquality(cprog, sol, exp);
    }
  }
  Assert(!exp.empty());
  Node exc_lem = exp.size() == 1
                     ? exp[0]
                     : NodeManager::currentNM()->mkNode(kind::AND, exp);
  exc_lem = exc_lem.negate();
  Trace("cegqi-lemma") << "Cegqi::Lemma : stream exclude current solution : "
                       << exc_lem << std::endl;
  d_qe->getOutputChannel().lemma(exc_lem);
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
              d_qe, prog, options::sygusSamples(), true);
          its = d_sampler.find(prog);
        }
        Node eq_sol = its->second.registerTerm(sol);
        // eq_sol is a candidate solution that is equivalent to sol
        if (eq_sol != sol)
        {
          ++(cei->d_statistics.d_candidate_rewrites);
          if (!eq_sol.isNull())
          {
            // The analog of terms sol and eq_sol are equivalent under sample
            // points but do not rewrite to the same term. Hence, this indicates
            // a candidate rewrite.
            Printer* p = Printer::getPrinter(options::outputLanguage());
            out << "(candidate-rewrite ";
            p->toStreamSygus(out, sol);
            out << " ";
            p->toStreamSygus(out, eq_sol);
            out << ")" << std::endl;
            ++(cei->d_statistics.d_candidate_rewrites_print);
            // debugging information
            if (Trace.isOn("sygus-rr-debug"))
            {
              ExtendedRewriter* er = sygusDb->getExtRewriter();
              Node solb = sygusDb->sygusToBuiltin(sol);
              Node solbr = er->extendedRewrite(solb);
              Node eq_solb = sygusDb->sygusToBuiltin(eq_sol);
              Node eq_solr = er->extendedRewrite(eq_solb);
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

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */
