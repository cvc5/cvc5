/*********************                                                        */
/*! \file ce_guided_single_inv.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing single invocation synthesis conjectures
 **
 **/
#include "theory/quantifiers/sygus/ce_guided_single_inv.h"

#include "options/quantifiers_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace std;

namespace CVC4 {

bool CegqiOutputSingleInv::doAddInstantiation( std::vector< Node >& subs ) {
  return d_out->doAddInstantiation( subs );
}

bool CegqiOutputSingleInv::isEligibleForInstantiation( Node n ) {
  return d_out->isEligibleForInstantiation( n );
}

bool CegqiOutputSingleInv::addLemma( Node n ) {
  return d_out->addLemma( n );
}

CegConjectureSingleInv::CegConjectureSingleInv(QuantifiersEngine* qe,
                                               CegConjecture* p)
    : d_qe(qe),
      d_parent(p),
      d_sip(new SingleInvocationPartition),
      d_sol(new CegConjectureSingleInvSol(qe)),
      d_cosi(new CegqiOutputSingleInv(this)),
      d_cinst(NULL),
      d_c_inst_match_trie(NULL),
      d_has_ites(true),
      d_single_invocation(false) {
  //  third and fourth arguments set to (false,false) until we have solution
  //  reconstruction for delta and infinity
  d_cinst = new CegInstantiator(d_qe, d_cosi, false, false);

  if (options::incrementalSolving()) {
    d_c_inst_match_trie = new inst::CDInstMatchTrie(qe->getUserContext());
  }
}

CegConjectureSingleInv::~CegConjectureSingleInv() {
  if (d_c_inst_match_trie) {
    delete d_c_inst_match_trie;
  }
  delete d_cinst;
  delete d_cosi;
  delete d_sol;  // (new CegConjectureSingleInvSol(qe)),
  delete d_sip;  // d_sip(new SingleInvocationPartition),
}

void CegConjectureSingleInv::getInitialSingleInvLemma( std::vector< Node >& lems ) {
  Assert( d_si_guard.isNull() );
  //single invocation guard
  d_si_guard = Rewriter::rewrite( NodeManager::currentNM()->mkSkolem( "G", NodeManager::currentNM()->booleanType() ) );
  d_si_guard = d_qe->getValuation().ensureLiteral( d_si_guard );
  AlwaysAssert( !d_si_guard.isNull() );
  d_qe->getOutputChannel().requirePhase( d_si_guard, true );

  if( !d_single_inv.isNull() ) {
    //make for new var/sk
    d_single_inv_var.clear();
    d_single_inv_sk.clear();
    Node inst;
    if( d_single_inv.getKind()==FORALL ){
      for( unsigned i=0; i<d_single_inv[0].getNumChildren(); i++ ){
        std::stringstream ss;
        ss << "k_" << d_single_inv[0][i];
        Node k = NodeManager::currentNM()->mkSkolem( ss.str(), d_single_inv[0][i].getType(), "single invocation function skolem" );
        d_single_inv_var.push_back( d_single_inv[0][i] );
        d_single_inv_sk.push_back( k );
        d_single_inv_sk_index[k] = i;
      }
      inst = d_single_inv[1].substitute( d_single_inv_var.begin(), d_single_inv_var.end(), d_single_inv_sk.begin(), d_single_inv_sk.end() );
    }else{
      inst = d_single_inv;
    }
    inst = TermUtil::simpleNegate( inst );
    Trace("cegqi-si") << "Single invocation initial lemma : " << inst << std::endl;

    //register with the instantiator
    Node ginst = NodeManager::currentNM()->mkNode( OR, d_si_guard.negate(), inst );
    lems.push_back( ginst );
    //make and register the instantiator
    if( d_cinst ){
      delete d_cinst;
    }
    d_cinst = new CegInstantiator( d_qe, d_cosi, false, false );
    d_cinst->registerCounterexampleLemma( lems, d_single_inv_sk );
  }
}

void CegConjectureSingleInv::initialize( Node q ) {
  // can only register one quantified formula with this
  Assert( d_quant.isNull() );
  d_quant = q;
  d_simp_quant = q;
  Trace("cegqi-si") << "CegConjectureSingleInv::initialize : " << q << std::endl;
  // infer single invocation-ness
  std::vector< Node > progs;
  std::map< Node, std::vector< Node > > prog_vars;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    Node sf = q[0][i];
    progs.push_back( sf );
    Node sfvl = sf.getAttribute(SygusSynthFunVarListAttribute());
    for( unsigned j=0; j<sfvl.getNumChildren(); j++ ){
      prog_vars[sf].push_back( sfvl[j] );
    }
  }
  // compute single invocation partition
  if( options::cegqiSingleInvMode()!=CEGQI_SI_MODE_NONE ){
    Node qq;
    if( q[1].getKind()==NOT && q[1][0].getKind()==FORALL ){
      qq = q[1][0][1];
    }else{
      qq = TermUtil::simpleNegate( q[1] );
    }
    //process the single invocation-ness of the property
    if( !d_sip->init( progs, qq ) ){
      Trace("cegqi-si") << "...not single invocation (type mismatch)" << std::endl;
    }else{
      Trace("cegqi-si") << "- Partitioned to single invocation parts : " << std::endl;
      d_sip->debugPrint( "cegqi-si" );

      //map from program to bound variables
      std::vector<Node> funcs;
      d_sip->getFunctions(funcs);
      for (unsigned j = 0, size = funcs.size(); j < size; j++)
      {
        Assert(std::find(progs.begin(), progs.end(), funcs[j]) != progs.end());
        d_prog_to_sol_index[funcs[j]] = j;
      }

      //check if it is single invocation
      if (!d_sip->isPurelySingleInvocation())
      {
        if( options::sygusInvTemplMode() != SYGUS_INV_TEMPL_MODE_NONE ){
          //if we are doing invariant templates, then construct the template
          Trace("cegqi-si") << "- Do transition inference..." << std::endl;
          d_ti[q].process( qq );
          Trace("cegqi-inv") << std::endl;
          if( !d_ti[q].d_func.isNull() ){
            // map the program back via non-single invocation map
            Node prog = d_ti[q].d_func;
            std::vector< Node > prog_templ_vars;
            prog_templ_vars.insert( prog_templ_vars.end(), d_ti[q].d_vars.begin(), d_ti[q].d_vars.end() );
            d_trans_pre[prog] = d_ti[q].getComponent( 1 );
            d_trans_post[prog] = d_ti[q].getComponent( -1 );
            Trace("cegqi-inv") << "   precondition : " << d_trans_pre[prog] << std::endl;
            Trace("cegqi-inv") << "  postcondition : " << d_trans_post[prog] << std::endl;
            std::vector<Node> sivars;
            d_sip->getSingleInvocationVariables(sivars);
            Node invariant = d_sip->getFunctionInvocationFor(prog);
            Assert(!invariant.isNull());
            invariant = invariant.substitute(sivars.begin(),
                                             sivars.end(),
                                             prog_templ_vars.begin(),
                                             prog_templ_vars.end());
            Trace("cegqi-inv") << "      invariant : " << invariant << std::endl;
            
            // store simplified version of quantified formula
            d_simp_quant = d_sip->getFullSpecification();
            std::vector< Node > new_bv;
            for (unsigned j = 0, size = sivars.size(); j < size; j++)
            {
              new_bv.push_back(
                  NodeManager::currentNM()->mkBoundVar(sivars[j].getType()));
            }
            d_simp_quant = d_simp_quant.substitute(
                sivars.begin(), sivars.end(), new_bv.begin(), new_bv.end());
            Assert( q[1].getKind()==NOT && q[1][0].getKind()==FORALL );
            for( unsigned j=0; j<q[1][0][0].getNumChildren(); j++ ){
              new_bv.push_back( q[1][0][0][j] );
            }
            d_simp_quant = NodeManager::currentNM()->mkNode( kind::FORALL, NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, new_bv ), d_simp_quant ).negate();
            d_simp_quant = Rewriter::rewrite( d_simp_quant );
            d_simp_quant = NodeManager::currentNM()->mkNode( kind::FORALL, q[0], d_simp_quant, q[2] );
            Trace("cegqi-si") << "Rewritten quantifier : " << d_simp_quant << std::endl;

            //construct template argument
            d_templ_arg[prog] = NodeManager::currentNM()->mkSkolem( "I", invariant.getType() );
            
            //construct template
            Node templ;
            if( options::sygusInvAutoUnfold() ){
              if( d_ti[q].isComplete() ){
                Trace("cegqi-inv-auto-unfold") << "Automatic deterministic unfolding... " << std::endl;
                // auto-unfold
                DetTrace dt;
                int init_dt = d_ti[q].initializeTrace( dt );
                if( init_dt==0 ){
                  Trace("cegqi-inv-auto-unfold") << "  Init : ";
                  dt.print("cegqi-inv-auto-unfold");
                  Trace("cegqi-inv-auto-unfold") << std::endl;
                  unsigned counter = 0;
                  unsigned status = 0;
                  while( counter<100 && status==0 ){
                    status = d_ti[q].incrementTrace( dt );
                    counter++;
                    Trace("cegqi-inv-auto-unfold") << "  #" << counter << " : ";
                    dt.print("cegqi-inv-auto-unfold");
                    Trace("cegqi-inv-auto-unfold") << "...status = " << status << std::endl;
                  }
                  if( status==1 ){
                    // we have a trivial invariant
                    templ = d_ti[q].constructFormulaTrace( dt );
                    Trace("cegqi-inv") << "By finite deterministic terminating trace, a solution invariant is : " << std::endl;
                    Trace("cegqi-inv") << "   " << templ << std::endl;
                    // FIXME : this should be unnecessary
                    templ = NodeManager::currentNM()->mkNode( AND, templ, d_templ_arg[prog] );
                  }
                }else{
                  Trace("cegqi-inv-auto-unfold") << "...failed initialize." << std::endl;
                }
              }
            }
            if( templ.isNull() ){
              if( options::sygusInvTemplMode() == SYGUS_INV_TEMPL_MODE_PRE ){
                //d_templ[prog] = NodeManager::currentNM()->mkNode( AND, NodeManager::currentNM()->mkNode( OR, d_trans_pre[prog], invariant ), d_trans_post[prog] );
                templ = NodeManager::currentNM()->mkNode( OR, d_trans_pre[prog], d_templ_arg[prog] );
              }else{
                Assert( options::sygusInvTemplMode() == SYGUS_INV_TEMPL_MODE_POST );
                //d_templ[prog] = NodeManager::currentNM()->mkNode( OR, d_trans_pre[prog], NodeManager::currentNM()->mkNode( AND, d_trans_post[prog], invariant ) );
                templ = NodeManager::currentNM()->mkNode( AND, d_trans_post[prog], d_templ_arg[prog] );
              }
            }
            Trace("cegqi-inv") << "       template (pre-substitution) : " << templ << std::endl;
            Assert( !templ.isNull() );
            // subsitute the template arguments
            templ = templ.substitute( prog_templ_vars.begin(), prog_templ_vars.end(), prog_vars[prog].begin(), prog_vars[prog].end() );
            Trace("cegqi-inv") << "       template : " << templ << std::endl;
            d_templ[prog] = templ;
          }
        }
      }else{
        //we are fully single invocation
        d_single_invocation = true;
      }
    }
  }
}

void CegConjectureSingleInv::finishInit( bool syntaxRestricted, bool hasItes ) {
  d_has_ites = hasItes;
  // do not do single invocation if grammar is restricted and CEGQI_SI_MODE_ALL is not enabled
  if( options::cegqiSingleInvMode()==CEGQI_SI_MODE_USE && d_single_invocation && syntaxRestricted ){
    d_single_invocation = false;
    Trace("cegqi-si") << "...grammar is restricted, do not use single invocation techniques." << std::endl;
  }

  // we now have determined whether we will do single invocation techniques
  if( d_single_invocation ){
    d_single_inv = d_sip->getSingleInvocation();
    d_single_inv = TermUtil::simpleNegate( d_single_inv );
    std::vector<Node> func_vars;
    d_sip->getFunctionVariables(func_vars);
    if (!func_vars.empty())
    {
      Node pbvl = NodeManager::currentNM()->mkNode(BOUND_VAR_LIST, func_vars);
      d_single_inv = NodeManager::currentNM()->mkNode( FORALL, pbvl, d_single_inv );
    }
    //now, introduce the skolems
    std::vector<Node> sivars;
    d_sip->getSingleInvocationVariables(sivars);
    for (unsigned i = 0, size = sivars.size(); i < size; i++)
    {
      Node v = NodeManager::currentNM()->mkSkolem(
          "a", sivars[i].getType(), "single invocation arg");
      d_single_inv_arg_sk.push_back( v );
    }
    d_single_inv = d_single_inv.substitute(sivars.begin(),
                                           sivars.end(),
                                           d_single_inv_arg_sk.begin(),
                                           d_single_inv_arg_sk.end());
    Trace("cegqi-si") << "Single invocation formula is : " << d_single_inv << std::endl;
    if( options::cbqiPreRegInst() && d_single_inv.getKind()==FORALL ){
      //just invoke the presolve now
      d_cinst->presolve( d_single_inv );
    }
  }else{
    d_single_inv = Node::null();
    Trace("cegqi-si") << "Formula is not single invocation." << std::endl;
    if( options::cegqiSingleInvAbort() ){
      Notice() << "Property is not single invocation." << std::endl;
      exit( 1 );
    }
  }
}

bool CegConjectureSingleInv::doAddInstantiation( std::vector< Node >& subs ){
  Assert( d_single_inv_sk.size()==subs.size() );
  Trace("cegqi-si-inst-debug") << "CegConjectureSingleInv::doAddInstantiation, #vars = ";
  Trace("cegqi-si-inst-debug") << d_single_inv_sk.size() << "..." << std::endl;
  std::stringstream siss;
  if( Trace.isOn("cegqi-si-inst-debug") || Trace.isOn("cegqi-engine") ){
    siss << "  * single invocation: " << std::endl;
    for( unsigned j=0; j<d_single_inv_sk.size(); j++ ){
      Node op = d_sip->getFunctionForFirstOrderVariable(d_single_inv[0][j]);
      Assert(!op.isNull());
      siss << "    * " << op;
      siss << " (" << d_single_inv_sk[j] << ")";
      siss << " -> " << subs[j] << std::endl;
    }
  }
  Trace("cegqi-si-inst-debug") << siss.str();

  bool alreadyExists;
  Node lem;
  if( subs.empty() ){
    Assert( d_single_inv.getKind()!=FORALL );
    alreadyExists = false;
    lem = d_single_inv;
  }else{
    Assert( d_single_inv.getKind()==FORALL );
    if( options::incrementalSolving() ){
      alreadyExists = !d_c_inst_match_trie->addInstMatch( d_qe, d_single_inv, subs, d_qe->getUserContext() );
    }else{
      alreadyExists = !d_inst_match_trie.addInstMatch( d_qe, d_single_inv, subs );
    }
    Trace("cegqi-si-inst-debug") << "  * success = " << !alreadyExists << std::endl;
    //Trace("cegqi-si-inst-debug") << siss.str();
    //Trace("cegqi-si-inst-debug") << "  * success = " << !alreadyExists << std::endl;
    if( alreadyExists ){
      return false;
    }else{
      Trace("cegqi-engine") << siss.str() << std::endl;
      Assert( d_single_inv_var.size()==subs.size() );
      lem = d_single_inv[1].substitute( d_single_inv_var.begin(), d_single_inv_var.end(), subs.begin(), subs.end() );
      if( d_qe->getTermUtil()->containsVtsTerm( lem ) ){
        Trace("cegqi-engine-debug") << "Rewrite based on vts symbols..." << std::endl;
        lem = d_qe->getTermUtil()->rewriteVtsSymbols( lem );
      }
    }
  }
  Trace("cegqi-engine-debug") << "Rewrite..." << std::endl;
  lem = Rewriter::rewrite( lem );
  Trace("cegqi-si") << "Single invocation lemma : " << lem << std::endl;
  if( std::find( d_lemmas_produced.begin(), d_lemmas_produced.end(), lem )==d_lemmas_produced.end() ){
    d_curr_lemmas.push_back( lem );
    d_lemmas_produced.push_back( lem );
    d_inst.push_back( std::vector< Node >() );
    d_inst.back().insert( d_inst.back().end(), subs.begin(), subs.end() );
  }
  return true;
}

bool CegConjectureSingleInv::isEligibleForInstantiation( Node n ) {
  return n.getKind()!=SKOLEM || std::find( d_single_inv_arg_sk.begin(), d_single_inv_arg_sk.end(), n )!=d_single_inv_arg_sk.end();
}

bool CegConjectureSingleInv::addLemma( Node n ) {
  d_curr_lemmas.push_back( n );
  return true;
}

bool CegConjectureSingleInv::check( std::vector< Node >& lems ) {
  if( !d_single_inv.isNull() ) {
    Trace("cegqi-si-debug") << "CegConjectureSingleInv::check..." << std::endl;
    Trace("cegqi-si-debug") << "CegConjectureSingleInv::check consulting ceg instantiation..." << std::endl;
    d_curr_lemmas.clear();
    Assert( d_cinst!=NULL );
    //call check for instantiator
    d_cinst->check();
    Trace("cegqi-si-debug") << "...returned " << d_curr_lemmas.size() << " lemmas " <<  std::endl;
    //add lemmas
    lems.insert( lems.end(), d_curr_lemmas.begin(), d_curr_lemmas.end() );
    return !lems.empty();
  }else{
    // not single invocation
    return false;
  }
}

Node CegConjectureSingleInv::constructSolution( std::vector< unsigned >& indices, unsigned i, unsigned index, std::map< Node, Node >& weak_imp ) {
  Assert( index<d_inst.size() );
  Assert( i<d_inst[index].size() );
  unsigned uindex = indices[index];
  if( index==indices.size()-1 ){
    return d_inst[uindex][i];
  }else{
    Node cond = d_lemmas_produced[uindex];
    //weaken based on unsat core
    std::map< Node, Node >::iterator itw = weak_imp.find( cond );
    if( itw!=weak_imp.end() ){
      cond = itw->second;
    }
    cond = TermUtil::simpleNegate( cond );
    Node ite1 = d_inst[uindex][i];
    Node ite2 = constructSolution( indices, i, index+1, weak_imp );
    return NodeManager::currentNM()->mkNode( ITE, cond, ite1, ite2 );
  }
}

//TODO: use term size?
struct sortSiInstanceIndices {
  CegConjectureSingleInv* d_ccsi;
  int d_i;
  bool operator() (unsigned i, unsigned j) {
    if( d_ccsi->d_inst[i][d_i].isConst() && !d_ccsi->d_inst[j][d_i].isConst() ){
      return true;
    }else{
      return false;
    }
  }
};


Node CegConjectureSingleInv::postProcessSolution( Node n ){
  ////remove boolean ITE (not allowed for sygus comp 2015)
  //if( n.getKind()==ITE && n.getType().isBoolean() ){
  //  Node n1 = postProcessSolution( n[1] );
  //  Node n2 = postProcessSolution( n[2] );
  //  return NodeManager::currentNM()->mkNode( OR, NodeManager::currentNM()->mkNode( AND, n[0], n1 ),
  //                                               NodeManager::currentNM()->mkNode( AND, n[0].negate(), n2 ) );
  //}else{
  bool childChanged = false;
  Kind k = n.getKind();
  if( n.getKind()==INTS_DIVISION_TOTAL ){
    k = INTS_DIVISION;
    childChanged = true;
  }else if( n.getKind()==INTS_MODULUS_TOTAL ){
    k = INTS_MODULUS;
    childChanged = true;
  }
  std::vector< Node > children;
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    Node nn = postProcessSolution( n[i] );
    children.push_back( nn );
    childChanged = childChanged || nn!=n[i];
  }
  if( childChanged ){
    if( n.hasOperator() && k==n.getKind() ){
      children.insert( children.begin(), n.getOperator() );
    }
    return NodeManager::currentNM()->mkNode( k, children );
  }else{
    return n;
  }
  //}
}


Node CegConjectureSingleInv::getSolution( unsigned sol_index, TypeNode stn, int& reconstructed, bool rconsSygus ){
  Assert( d_sol!=NULL );
  Assert( !d_lemmas_produced.empty() );
  const Datatype& dt = ((DatatypeType)(stn).toType()).getDatatype();
  Node varList = Node::fromExpr( dt.getSygusVarList() );
  Node prog = d_quant[0][sol_index];
  std::vector< Node > vars;
  Node s;
  if( d_prog_to_sol_index.find( prog )==d_prog_to_sol_index.end() ){
    Trace("csi-sol") << "Get solution for (unconstrained) " << prog << std::endl;
    s = d_qe->getTermEnumeration()->getEnumerateTerm(
        TypeNode::fromType(dt.getSygusType()), 0);
  }else{
    Trace("csi-sol") << "Get solution for " << prog << ", with skolems : ";
    sol_index = d_prog_to_sol_index[prog];
    d_sol->d_varList.clear();
    Assert( d_single_inv_arg_sk.size()==varList.getNumChildren() );
    for( unsigned i=0; i<d_single_inv_arg_sk.size(); i++ ){
      Trace("csi-sol") << d_single_inv_arg_sk[i] << " ";
      vars.push_back( d_single_inv_arg_sk[i] );
      d_sol->d_varList.push_back( varList[i] );
    }
    Trace("csi-sol") << std::endl;

    //construct the solution
    Trace("csi-sol") << "Sort solution return values " << sol_index << std::endl;
    bool useUnsatCore = false;
    std::vector< Node > active_lemmas;
    //minimize based on unsat core, if possible
    std::map< Node, Node > weak_imp;
    if( options::cegqiSolMinCore() ){
      if( options::cegqiSolMinInst() ){
        if( d_qe->getUnsatCoreLemmas( active_lemmas, weak_imp ) ){
          useUnsatCore = true;
        }
      }else{
        if( d_qe->getUnsatCoreLemmas( active_lemmas ) ){
          useUnsatCore = true;
        }
      }
    } 
    Assert( d_lemmas_produced.size()==d_inst.size() );
    std::vector< unsigned > indices;
    for( unsigned i=0; i<d_lemmas_produced.size(); i++ ){
      bool incl = true;
      if( useUnsatCore ){
        incl = std::find( active_lemmas.begin(), active_lemmas.end(), d_lemmas_produced[i] )!=active_lemmas.end();
      }
      if( incl ){
        Assert( sol_index<d_inst[i].size() );
        indices.push_back( i );
      }
    }
    Trace("csi-sol") << "...included " << indices.size() << " / " << d_lemmas_produced.size() << " instantiations." << std::endl;
    Assert( !indices.empty() );
    //sort indices based on heuristic : currently, do all constant returns first (leads to simpler conditions)
    // TODO : to minimize solution size, put the largest term last
    sortSiInstanceIndices ssii;
    ssii.d_ccsi = this;
    ssii.d_i = sol_index;
    std::sort( indices.begin(), indices.end(), ssii );
    Trace("csi-sol") << "Construct solution" << std::endl;
    s = constructSolution( indices, sol_index, 0, weak_imp );
    Assert( vars.size()==d_sol->d_varList.size() );
    s = s.substitute( vars.begin(), vars.end(), d_sol->d_varList.begin(), d_sol->d_varList.end() );
  }
  d_orig_solution = s;

  //simplify the solution
  Trace("csi-sol") << "Solution (pre-simplification): " << d_orig_solution << std::endl;
  s = d_sol->simplifySolution( s, stn );
  Trace("csi-sol") << "Solution (post-simplification): " << s << std::endl;
  return reconstructToSyntax( s, stn, reconstructed, rconsSygus );
}

Node CegConjectureSingleInv::reconstructToSyntax( Node s, TypeNode stn, int& reconstructed, bool rconsSygus ) {
  d_solution = s;
  const Datatype& dt = ((DatatypeType)(stn).toType()).getDatatype();

  //reconstruct the solution into sygus if necessary
  reconstructed = 0;
  if( options::cegqiSingleInvReconstruct() && !dt.getSygusAllowAll() && !stn.isNull() && rconsSygus ){
    d_sol->preregisterConjecture( d_orig_conjecture );
    d_sygus_solution = d_sol->reconstructSolution( s, stn, reconstructed );
    if( reconstructed==1 ){
      Trace("csi-sol") << "Solution (post-reconstruction into Sygus): " << d_sygus_solution << std::endl;
    }
  }else{
    Trace("csi-sol") << "Post-process solution..." << std::endl;
    Node prev = d_solution;
    d_solution = postProcessSolution( d_solution );
    if( prev!=d_solution ){
      Trace("csi-sol") << "Solution (after post process) : " << d_solution << std::endl;
    }
  }


  if( Trace.isOn("csi-sol") ){
    //debug solution
    if( !d_sol->debugSolution( d_solution ) ){
      Trace("csi-sol") << "WARNING : solution " << d_solution << " contains free constants." << std::endl;
      //exit( 47 );
    }else{
      //exit( 49 );
    }
  }
  if( Trace.isOn("cegqi-stats") ){
    int tsize, itesize;
    tsize = 0;itesize = 0;
    d_sol->debugTermSize( d_orig_solution, tsize, itesize );
    Trace("cegqi-stats") << tsize << " " << itesize << " ";
    tsize = 0;itesize = 0;
    d_sol->debugTermSize( d_solution, tsize, itesize );
    Trace("cegqi-stats") << tsize << " " << itesize << " ";
    if( !d_sygus_solution.isNull() ){
      tsize = 0;itesize = 0;
      d_sol->debugTermSize( d_sygus_solution, tsize, itesize );
      Trace("cegqi-stats") << tsize << " - ";
    }else{
      Trace("cegqi-stats") << "null ";
    }
    Trace("cegqi-stats") << std::endl;
  }
  Node sol;
  if( reconstructed==1 ){
    sol = d_sygus_solution;
  }else if( reconstructed==-1 ){
    return Node::null();
  }else{
    sol = d_solution;
  }
  //make into lambda
  if( !dt.getSygusVarList().isNull() ){
    Node varList = Node::fromExpr( dt.getSygusVarList() );
    return NodeManager::currentNM()->mkNode( LAMBDA, varList, sol );
  }else{
    return sol;
  }
}

bool CegConjectureSingleInv::needsCheck() {
  if( options::cegqiSingleInvMode()==CEGQI_SI_MODE_ALL_ABORT ){
    if( !d_has_ites ){
      return d_inst.empty();
    }
  }
  return true;
}

void CegConjectureSingleInv::preregisterConjecture( Node q ) {
  d_orig_conjecture = q;
}

bool DetTrace::DetTraceTrie::add( Node loc, std::vector< Node >& val, unsigned index ){
  if( index==val.size() ){
    if( d_children.empty() ){
      d_children[loc].clear();
      return true;
    }else{
      return false;
    }
  }else{
    return d_children[val[index]].add( loc, val, index+1 );
  }
}

Node DetTrace::DetTraceTrie::constructFormula( std::vector< Node >& vars, unsigned index ){
  if( index==vars.size() ){
    return NodeManager::currentNM()->mkConst( true );    
  }else{
    std::vector< Node > disj;
    for( std::map< Node, DetTraceTrie >::iterator it = d_children.begin(); it != d_children.end(); ++it ){
      Node eq = vars[index].eqNode( it->first );
      if( index<vars.size()-1 ){
        Node conc = it->second.constructFormula( vars, index+1 );
        disj.push_back( NodeManager::currentNM()->mkNode( kind::AND, eq, conc ) );
      }else{
        disj.push_back( eq );
      }
    }
    Assert( !disj.empty() );
    return disj.size()==1 ? disj[0] : NodeManager::currentNM()->mkNode( kind::OR, disj );
  }
}

bool DetTrace::increment( Node loc, std::vector< Node >& vals ){
  if( d_trie.add( loc, vals ) ){
    for( unsigned i=0; i<vals.size(); i++ ){
      d_curr[i] = vals[i];
    }
    return true;
  }else{
    return false;
  }
}

Node DetTrace::constructFormula( std::vector< Node >& vars ) {
  return d_trie.constructFormula( vars );
}


void DetTrace::print( const char* c ) {
  for( unsigned i=0; i<d_curr.size(); i++ ){
    Trace(c) << d_curr[i] << " ";
  }
}

void TransitionInference::initialize( Node f, std::vector< Node >& vars ) {
  Assert( d_vars.empty() );
  d_func = f;
  d_vars.insert( d_vars.end(), vars.begin(), vars.end() );
}


void TransitionInference::getConstantSubstitution( std::vector< Node >& vars, std::vector< Node >& disjuncts, std::vector< Node >& const_var, std::vector< Node >& const_subs, bool reqPol ) {
  for( unsigned j=0; j<disjuncts.size(); j++ ){
    Node sn;
    if( !const_var.empty() ){
      sn = disjuncts[j].substitute( const_var.begin(), const_var.end(), const_subs.begin(), const_subs.end() );
      sn = Rewriter::rewrite( sn );
    }else{
      sn = disjuncts[j];
    }
    bool slit_pol = sn.getKind()!=NOT;
    Node slit = sn.getKind()==NOT ? sn[0] : sn;
    if( slit.getKind()==EQUAL && slit_pol==reqPol ){
      // check if it is a variable equality
      TNode v;
      Node s;
      for( unsigned r=0; r<2; r++ ){
        if( std::find( vars.begin(), vars.end(), slit[r] )!=vars.end() ){
          if( !TermUtil::containsTerm( slit[1-r], slit[r] ) ){
            v = slit[r];
            s = slit[1-r];
            break;
          }
        }
      }
      if( v.isNull() ){
        //solve for var
        std::map< Node, Node > msum;
        if (ArithMSum::getMonomialSumLit(slit, msum))
        {
          for( std::map< Node, Node >::iterator itm = msum.begin(); itm != msum.end(); ++itm ){
            if( std::find( vars.begin(), vars.end(), itm->first )!=vars.end() ){  
              Node veq_c;
              Node val;
              int ires =
                  ArithMSum::isolate(itm->first, msum, veq_c, val, EQUAL);
              if( ires!=0 && veq_c.isNull() && !TermUtil::containsTerm( val, itm->first ) ){
                v = itm->first;
                s = val;
              }
            }
          }
        }
      }
      if( !v.isNull() ){
        TNode ts = s;
        for( unsigned k=0; k<const_subs.size(); k++ ){
          const_subs[k] = Rewriter::rewrite( const_subs[k].substitute( v, ts ) );
        }
        Trace("cegqi-inv-debug2") << "...substitution : " << v << " -> " << s << std::endl;
        const_var.push_back( v );
        const_subs.push_back( s );
      }
    }
  }
}

void TransitionInference::process( Node n ) {
  d_complete = true;
  std::vector< Node > n_check;
  if( n.getKind()==AND ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      n_check.push_back( n[i] );
    }
  }else{
    n_check.push_back( n );
  }
  for( unsigned i=0; i<n_check.size(); i++ ){
    Node nn = n_check[i];
    std::map< Node, bool > visited;
    std::map< bool, Node > terms;
    std::vector< Node > disjuncts;
    Trace("cegqi-inv") << "TransitionInference : Process disjunct : " << nn << std::endl;
    if( processDisjunct( nn, terms, disjuncts, visited, true ) ){
      if( !terms.empty() ){
        Node norm_args;
        int comp_num;
        std::map< bool, Node >::iterator itt = terms.find( false );
        if( itt!=terms.end() ){
          norm_args = itt->second;
          if( terms.find( true )!=terms.end() ){
            comp_num = 0;
          }else{
            comp_num = -1;
          }
        }else{
          norm_args = terms[true];
          comp_num = 1;
        }
        std::vector< Node > subs;
        for( unsigned j=0; j<norm_args.getNumChildren(); j++ ){
          subs.push_back( norm_args[j] );
        }        
        Trace("cegqi-inv-debug2") << "  normalize based on " << norm_args << std::endl;
        Assert( d_vars.size()==subs.size() );
        for( unsigned j=0; j<disjuncts.size(); j++ ){
          disjuncts[j] = Rewriter::rewrite( disjuncts[j].substitute( subs.begin(), subs.end(), d_vars.begin(), d_vars.end() ) );
          Trace("cegqi-inv-debug2") << "  ..." << disjuncts[j] << std::endl;
        }
        std::vector< Node > const_var;
        std::vector< Node > const_subs;
        if( comp_num==0 ){
          //transition
          Assert( terms.find( true )!=terms.end() );
          Node next = terms[true];
          next = Rewriter::rewrite( next.substitute( subs.begin(), subs.end(), d_vars.begin(), d_vars.end() ) );
          Trace("cegqi-inv-debug") << "transition next predicate : " << next << std::endl;
          // normalize the other direction
          std::vector< Node > rvars;
          for( unsigned i=0; i<next.getNumChildren(); i++ ){
            rvars.push_back( next[i] );
          }
          if( d_prime_vars.size()<next.getNumChildren() ){
            for( unsigned i=0; i<next.getNumChildren(); i++ ){
              Node v = NodeManager::currentNM()->mkSkolem( "ir", next[i].getType(), "template inference rev argument" );
              d_prime_vars.push_back( v );
            }
          }
          Trace("cegqi-inv-debug2") << "  normalize based on " << next << std::endl;
          Assert( d_vars.size()==subs.size() );
          for( unsigned j=0; j<disjuncts.size(); j++ ){
            disjuncts[j] = Rewriter::rewrite( disjuncts[j].substitute( rvars.begin(), rvars.end(), d_prime_vars.begin(), d_prime_vars.end() ) );
            Trace("cegqi-inv-debug2") << "  ..." << disjuncts[j] << std::endl;
          }
          getConstantSubstitution( d_prime_vars, disjuncts, const_var, const_subs, false );
        }else{
          getConstantSubstitution( d_vars, disjuncts, const_var, const_subs, false );
        }
        Node res;
        if( disjuncts.empty() ){
          res = NodeManager::currentNM()->mkConst( false );
        }else if( disjuncts.size()==1 ){
          res = disjuncts[0];
        }else{
          res = NodeManager::currentNM()->mkNode( kind::OR, disjuncts );
        }
        if( !res.hasBoundVar() ){
          Trace("cegqi-inv") << "*** inferred " << ( comp_num==1 ? "pre" : ( comp_num==-1 ? "post" : "trans" ) ) << "-condition : " << res << std::endl;
          d_com[comp_num].d_conjuncts.push_back( res );
          if( !const_var.empty() ){
            bool has_const_eq = const_var.size()==d_vars.size();
            Trace("cegqi-inv") << "    with constant substitution, complete = " << has_const_eq << " : " << std::endl;
            for( unsigned i=0; i<const_var.size(); i++ ){
              Trace("cegqi-inv") << "      " << const_var[i] << " -> " << const_subs[i] << std::endl;
              if( has_const_eq ){
                d_com[comp_num].d_const_eq[res][const_var[i]] = const_subs[i];
              }
            }
            Trace("cegqi-inv") << "...size = " << const_var.size() << ", #vars = " << d_vars.size() << std::endl;
          }
        }else{
          Trace("cegqi-inv-debug2") << "...failed, free variable." << std::endl;
          d_complete = false;
        }
      }
    }else{
      d_complete = false;
    }
  }
  
  // finalize the components
  for( int i=-1; i<=1; i++ ){
    Node ret;
    if( d_com[i].d_conjuncts.empty() ){
      ret = NodeManager::currentNM()->mkConst( true );
    }else if( d_com[i].d_conjuncts.size()==1 ){
      ret = d_com[i].d_conjuncts[0];
    }else{
      ret = NodeManager::currentNM()->mkNode( kind::AND, d_com[i].d_conjuncts );
    }
    if( i==0 || i==1 ){
      // pre-condition and transition are negated
      ret = TermUtil::simpleNegate( ret );
    }
    d_com[i].d_this = ret;
  }
}

bool TransitionInference::processDisjunct( Node n, std::map< bool, Node >& terms, std::vector< Node >& disjuncts, 
                                           std::map< Node, bool >& visited, bool topLevel ) {
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    bool childTopLevel = n.getKind()==OR && topLevel;
    //if another part mentions UF or a free variable, then fail
    bool lit_pol = n.getKind()!=NOT;
    Node lit = n.getKind()==NOT ? n[0] : n;
    if( lit.getKind()==APPLY_UF ){
      Node op = lit.getOperator();
      if( d_func.isNull() ){
        d_func = op;
        Trace("cegqi-inv-debug") << "Use " << op << " with args ";
        for( unsigned i=0; i<lit.getNumChildren(); i++ ){
          Node v = NodeManager::currentNM()->mkSkolem( "i", lit[i].getType(), "template inference argument" );
          d_vars.push_back( v );
          Trace("cegqi-inv-debug") << v << " ";
        }
        Trace("cegqi-inv-debug") << std::endl;
      }
      if( op!=d_func ){
        Trace("cegqi-inv-debug") << "...failed, free function : " << n << std::endl;
        return false;
      }else if( topLevel ){
        if( terms.find( lit_pol )==terms.end() ){
          terms[lit_pol] = lit;
          return true;
        }else{
          Trace("cegqi-inv-debug") << "...failed, repeated inv-app : " << lit << std::endl;
          return false;
        }
      }else{
        Trace("cegqi-inv-debug") << "...failed, non-entailed inv-app : " << lit << std::endl;
        return false;
      }
    }else if( topLevel && !childTopLevel ){
      disjuncts.push_back( n );
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( !processDisjunct( n[i], terms, disjuncts, visited, childTopLevel ) ){
        return false;
      }
    }
  }
  return true;
}

Node TransitionInference::getComponent( int i ) {
  return d_com[i].d_this;
}

int TransitionInference::initializeTrace( DetTrace& dt, Node loc, bool fwd ) {
  int index = fwd ? 1 : -1;
  Assert( d_com[index].has( loc ) );
  std::map< Node, std::map< Node, Node > >::iterator it = d_com[index].d_const_eq.find( loc );
  if( it!=d_com[index].d_const_eq.end() ){
    std::vector< Node > next;
    for( unsigned i=0; i<d_vars.size(); i++ ){
      Node v = d_vars[i];
      Assert( it->second.find( v )!=it->second.end() );
      next.push_back( it->second[v] );
      dt.d_curr.push_back( it->second[v] );
    }
    Trace("cegqi-inv-debug2") << "dtrace : initial increment" << std::endl;
    bool ret = dt.increment( loc, next );
    AlwaysAssert( ret );
    return 0;
  }
  return -1;
}
  
int TransitionInference::incrementTrace( DetTrace& dt, Node loc, bool fwd ) {
  Assert( d_com[0].has( loc ) );
  // check if it satisfies the pre/post condition
  int check_index = fwd ? -1 : 1;
  Node cc = getComponent( check_index );
  Assert( !cc.isNull() );
  Node ccr = Rewriter::rewrite( cc.substitute( d_vars.begin(), d_vars.end(), dt.d_curr.begin(), dt.d_curr.end() ) );
  if( ccr.isConst() ){
    if( ccr.getConst<bool>()==( fwd ? false : true ) ){
      Trace("cegqi-inv-debug2") << "dtrace : counterexample" << std::endl;
      return 2;
    }
  }


  // terminates?
  Node c = getComponent( 0 );
  Assert( !c.isNull() );

  Assert( d_vars.size()==dt.d_curr.size() );
  Node cr = Rewriter::rewrite( c.substitute( d_vars.begin(), d_vars.end(), dt.d_curr.begin(), dt.d_curr.end() ) );
  if( cr.isConst() ){
    if( !cr.getConst<bool>() ){
      Trace("cegqi-inv-debug2") << "dtrace : terminated" << std::endl;
      return 1;
    }else{
      return -1;
    }
  }
  if( fwd ){
    std::map< Node, std::map< Node, Node > >::iterator it = d_com[0].d_const_eq.find( loc );
    if( it!=d_com[0].d_const_eq.end() ){
      std::vector< Node > next;
      for( unsigned i=0; i<d_prime_vars.size(); i++ ){
        Node pv = d_prime_vars[i];
        Assert( it->second.find( pv )!=it->second.end() );
        Node pvs = it->second[pv];
        Assert( d_vars.size()==dt.d_curr.size() );
        Node pvsr = Rewriter::rewrite( pvs.substitute( d_vars.begin(), d_vars.end(), dt.d_curr.begin(), dt.d_curr.end() ) );
        next.push_back( pvsr );
      }
      if( dt.increment( loc, next ) ){
        Trace("cegqi-inv-debug2") << "dtrace : success increment" << std::endl;
        return 0;
      }else{
        // looped
        Trace("cegqi-inv-debug2") << "dtrace : looped" << std::endl;
        return 1;
      }
    }
  }else{
    //TODO
  }
  return -1;
}

int TransitionInference::initializeTrace( DetTrace& dt, bool fwd ) {
  Trace("cegqi-inv-debug2") << "Initialize trace" << std::endl;
  int index = fwd ? 1 : -1;
  if( d_com[index].d_conjuncts.size()==1 ){
    return initializeTrace( dt, d_com[index].d_conjuncts[0], fwd );
  }else{
    return -1;
  }
}

int TransitionInference::incrementTrace( DetTrace& dt, bool fwd ) {
  if( d_com[0].d_conjuncts.size()==1 ){
    return incrementTrace( dt, d_com[0].d_conjuncts[0], fwd );
  }else{
    return -1;
  }
}

Node TransitionInference::constructFormulaTrace( DetTrace& dt ) {
  return dt.constructFormula( d_vars );
}
  
} //namespace CVC4

