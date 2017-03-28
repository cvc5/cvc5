/*********************                                                        */
/*! \file ce_guided_instantiation.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief counterexample guided instantiation class
 **
 **/
#include "theory/quantifiers/ce_guided_instantiation.h"

#include "expr/datatype.h"
#include "options/quantifiers_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "theory/theory_engine.h"
#include "prop/prop_engine.h"
#include "theory/bv/theory_bv_rewriter.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {


CegConjecture::CegConjecture( QuantifiersEngine * qe, context::Context* c )
    : d_qe( qe ), d_curr_lit( c, 0 ) {
  d_refine_count = 0;
  d_ceg_si = new CegConjectureSingleInv( qe, this );
}

CegConjecture::~CegConjecture() {
  delete d_ceg_si;
}

void CegConjecture::assign( Node q ) {
  Assert( d_quant.isNull() );
  Assert( q.getKind()==FORALL );
  d_assert_quant = q;
  //register with single invocation if applicable
  if( d_qe->getTermDatabase()->isQAttrSygus( d_assert_quant ) && options::cegqiSingleInvMode()!=CEGQI_SI_MODE_NONE ){
    d_ceg_si->initialize( q );
    if( q!=d_ceg_si->d_quant ){
      //Node red_lem = NodeManager::currentNM()->mkNode( OR, q.negate(), d_cegqi_si->d_quant );
      //may have rewritten quantified formula (for invariant synthesis)
      q = d_ceg_si->d_quant;
    }
  }
  d_quant = q;
  Assert( d_candidates.empty() );
  std::vector< Node > vars;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    vars.push_back( q[0][i] );
    d_candidates.push_back( NodeManager::currentNM()->mkSkolem( "e", q[0][i].getType() ) );
  }
  Trace("cegqi") << "Base quantified formula is : " << q << std::endl;
  //construct base instantiation
  d_base_inst = Rewriter::rewrite( d_qe->getInstantiation( q, vars, d_candidates ) );
  Trace("cegqi") << "Base instantiation is :      " << d_base_inst << std::endl;
  if( d_qe->getTermDatabase()->isQAttrSygus( d_assert_quant ) ){
    CegInstantiation::collectDisjuncts( d_base_inst, d_base_disj );
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
    if( options::sygusUnifCondSol() ){
      // for each variable, determine whether we can do conditional counterexamples
      for( unsigned i=0; i<d_candidates.size(); i++ ){
        registerCandidateConditional( d_candidates[i] );
      }
    }
    d_syntax_guided = true;
  }else if( d_qe->getTermDatabase()->isQAttrSynthesis( d_assert_quant ) ){
    d_syntax_guided = false;
  }else{
    Assert( false );
  }
}

void CegConjecture::registerCandidateConditional( Node v ) {
  TypeNode tn = v.getType();
  bool type_valid = false;
  bool success = false;
  std::vector< TypeNode > unif_types;
  if( tn.isDatatype() ){
    const Datatype& dt = ((DatatypeType)tn.toType()).getDatatype();
    if( dt.isSygus() ){
      type_valid = true;
      if( d_candidates.size()==1 ){  // conditional solutions for multiple function conjectures TODO?
        for( unsigned r=0; r<2; r++ ){
          for( unsigned j=0; j<dt.getNumConstructors(); j++ ){
            Node op = Node::fromExpr( dt[j].getSygusOp() );
            if( r==0 ){
              if( op.getKind() == kind::BUILTIN ){
                Kind sk = NodeManager::operatorToKind( op );
                if( sk==kind::ITE ){
                  // we can do unification
                  success = true;
                  d_cinfo[v].d_csol_op = Node::fromExpr( dt[j].getConstructor() );
                  Assert( dt[j].getNumArgs()==3 );
                  for( unsigned k=0; k<3; k++ ){
                    unif_types.push_back( TypeNode::fromType( dt[j][k].getRangeType() ) );
                  }
                  break;
                }
              }
            }else{
              if( dt[j].getNumArgs()>=3 ){
                // could be a defined ITE (this is a hack for ICFP benchmarks)
                std::vector< Node > utchildren;
                utchildren.push_back( Node::fromExpr( dt[j].getConstructor() ) );
                std::vector< Node > sks;
                for( unsigned k=0; k<dt[j].getNumArgs(); k++ ){
                  Type t = dt[j][k].getRangeType();
                  Node kv = NodeManager::currentNM()->mkSkolem( "ut", TypeNode::fromType( t ) );
                  sks.push_back( kv );
                  utchildren.push_back( kv );
                }
                Node ut = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, utchildren );
                std::vector< Node > echildren;
                echildren.push_back( Node::fromExpr( dt.getSygusEvaluationFunc() ) );
                echildren.push_back( ut );
                Node sbvl = Node::fromExpr( dt.getSygusVarList() );
                for( unsigned k=0; k<sbvl.getNumChildren(); k++ ){
                  echildren.push_back( sbvl[k] );
                }
                Node eut = NodeManager::currentNM()->mkNode( kind::APPLY_UF, echildren );
                Trace("sygus-unif-debug") << "Test evaluation of " << eut << "..." << std::endl;
                eut = d_qe->getTermDatabaseSygus()->unfold( eut );
                Trace("sygus-unif-debug") << "...got " << eut << std::endl;
                if( eut.getKind()==kind::ITE ){
                  success = true;
                  std::vector< Node > vs;
                  std::vector< Node > ss;
                  std::map< Node, unsigned > templ_var_index;
                  for( unsigned k=0; k<sks.size(); k++ ){
                    echildren[1] = sks[k];
                    Node esk = NodeManager::currentNM()->mkNode( kind::APPLY_UF, echildren );
                    vs.push_back( esk );
                    Node tvar = NodeManager::currentNM()->mkSkolem( "templ", esk.getType() );
                    templ_var_index[tvar] = k;
                    ss.push_back( tvar );
                  }
                  eut = eut.substitute( vs.begin(), vs.end(), ss.begin(), ss.end() );
                  Trace("sygus-unif") << "Defined constructor " << j << ", base term is " << eut << std::endl;
                  //success if we can find a injection from ITE args to sygus args
                  std::map< unsigned, unsigned > templ_injection;
                  for( unsigned k=0; k<3; k++ ){
                    if( !inferIteTemplate( k, eut[k], templ_var_index, templ_injection ) ){
                      Trace("sygus-unif") << "...failed to find injection (range)." << std::endl;
                      success = false;
                      break;
                    }
                    if( templ_injection.find( k )==templ_injection.end() ){
                      Trace("sygus-unif") << "...failed to find injection (domain)." << std::endl;
                      success = false;
                      break;
                    }
                  }
                  if( success ){
                    d_cinfo[v].d_csol_op = Node::fromExpr( dt[j].getConstructor() );
                    for( unsigned k=0; k<3; k++ ){
                      Assert( templ_injection.find( k )!=templ_injection.end() );
                      unsigned sk_index = templ_injection[k];
                      unif_types.push_back( sks[sk_index].getType() );
                      //also store the template information, if necessary
                      Node teut = eut[k];
                      if( !teut.isVar() ){
                        d_cinfo[v].d_template[k] = teut;
                        d_cinfo[v].d_template_arg[k] = ss[sk_index];
                        Trace("sygus-unif") << "  Arg " << k << " : template : " << teut << ", arg " << ss[sk_index] << std::endl;
                      }else{
                        Assert( teut==ss[sk_index] );
                      }
                    }
                  }
                }
              }
            }
          }
          if( success ){
            break;
          }
        }
      }
    }
  }
  //mark active
  if( !success ){
    d_cinfo[v].d_csol_status = -1;
  }else{     
    //make progress guard
    Node pg = Rewriter::rewrite( NodeManager::currentNM()->mkSkolem( "P", NodeManager::currentNM()->booleanType(), "Progress guard for conditional solution." ) );
    Node pglem = NodeManager::currentNM()->mkNode( kind::OR, pg.negate(), pg );
    Trace("cegqi-lemma") << "Cegqi::Lemma : progress split : " << pglem << std::endl;
    d_qe->getOutputChannel().lemma( pglem );
    d_qe->getOutputChannel().requirePhase( pg, true );
              
    Assert( unif_types.size()==3 ); 
    d_cinfo[v].d_csol_cond = NodeManager::currentNM()->mkSkolem( "c", unif_types[0] );
    for( unsigned k=0; k<2; k++ ){
      d_cinfo[v].d_csol_var[k] = NodeManager::currentNM()->mkSkolem( "e", unif_types[k+1] );
      // optimization : need not be an ITE if types are equivalent  TODO
    }
    d_cinfo[v].d_csol_progress_guard = pg;
    Trace("sygus-unif") << "Can do synthesis unification for variable " << v << ", based on operator " << d_cinfo[v].d_csol_op << std::endl;
  }
  if( !type_valid ){
    Assert( false );
  }
}

bool CegConjecture::inferIteTemplate( unsigned k, Node n, std::map< Node, unsigned >& templ_var_index, std::map< unsigned, unsigned >& templ_injection ){
  if( n.getNumChildren()==0 ){
    std::map< Node, unsigned >::iterator itt = templ_var_index.find( n );
    if( itt!=templ_var_index.end() ){
      unsigned kk = itt->second;
      std::map< unsigned, unsigned >::iterator itti = templ_injection.find( k );
      if( itti==templ_injection.end() ){
        templ_injection[k] = kk;
      }else if( itti->second!=kk ){
        return false;
      }
    }
    return true;
  }else{
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( !inferIteTemplate( k, n[i], templ_var_index, templ_injection ) ){
        return false;
      }
    }
  }
  return true;
}

void CegConjecture::initializeGuard(){
  if( isAssigned() ){
    if( !d_syntax_guided ){
      if( d_nsg_guard.isNull() ){
        d_nsg_guard = Rewriter::rewrite( NodeManager::currentNM()->mkSkolem( "G", NodeManager::currentNM()->booleanType() ) );
        d_nsg_guard = d_qe->getValuation().ensureLiteral( d_nsg_guard );
        AlwaysAssert( !d_nsg_guard.isNull() );
        d_qe->getOutputChannel().requirePhase( d_nsg_guard, true );
        //add immediate lemma
        Node lem = NodeManager::currentNM()->mkNode( OR, d_nsg_guard.negate(), d_base_inst.negate() );
        Trace("cegqi-lemma") << "Cegqi::Lemma : non-syntax-guided : " << lem << std::endl;
        d_qe->getOutputChannel().lemma( lem );
      }
    }else if( d_ceg_si->d_si_guard.isNull() ){
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
  }
}

void CegConjecture::setMeasureTerm( Node mt ){ 
  d_measure_term = mt;
  d_active_measure_term = mt;
}

Node CegConjecture::getMeasureTermFactor( Node v ) {
  Node ret;
  if( getCegqiFairMode()==CEGQI_FAIR_DT_SIZE ){
    if( v.getType().isDatatype() ){
      ret = NodeManager::currentNM()->mkNode( DT_SIZE, v );
    }
  }
  //TODO
  Assert( ret.isNull() || ret.getType().isInteger() );
  return ret;
}
  
  
Node CegConjecture::getFairnessLiteral( int i ) {
  if( d_measure_term.isNull() ){
    return Node::null();
  }else{
    std::map< int, Node >::iterator it = d_lits.find( i );
    if( it==d_lits.end() ){
      Trace("cegqi-engine") << "******* CEGQI : allocate size literal " << i << std::endl;
      Node c = NodeManager::currentNM()->mkConst( Rational( i ) );
      Node lit = NodeManager::currentNM()->mkNode( LEQ, d_measure_term, c );
      lit = Rewriter::rewrite( lit );
      d_lits[i] = lit;

      Node lem = NodeManager::currentNM()->mkNode( kind::OR, lit, lit.negate() );
      Trace("cegqi-lemma") << "Cegqi::Lemma : Fairness split : " << lem << std::endl;
      d_qe->getOutputChannel().lemma( lem );
      d_qe->getOutputChannel().requirePhase( lit, true );

      if( getCegqiFairMode()==CEGQI_FAIR_DT_HEIGHT_PRED || getCegqiFairMode()==CEGQI_FAIR_DT_SIZE_PRED ){
        //implies height bounds on each candidate variable
        std::vector< Node > lem_c;
        for( unsigned j=0; j<d_candidates.size(); j++ ){
          if( getCegqiFairMode()==CEGQI_FAIR_DT_HEIGHT_PRED ){
            lem_c.push_back( NodeManager::currentNM()->mkNode( DT_HEIGHT_BOUND, d_candidates[j], c ) );
          }else{
            //lem_c.push_back( NodeManager::currentNM()->mkNode( DT_SIZE_BOUND, d_candidates[j], c ) );
          }
        }
        Node hlem = NodeManager::currentNM()->mkNode( OR, lit.negate(), lem_c.size()==1 ? lem_c[0] : NodeManager::currentNM()->mkNode( AND, lem_c ) );
        Trace("cegqi-lemma") << "Cegqi::Lemma : Fairness expansion (pred) : " << hlem << std::endl;
        d_qe->getOutputChannel().lemma( hlem );
      }
      return lit;
    }else{
      return it->second;
    }
  }
}

Node CegConjecture::getGuard() {
  return !d_syntax_guided ? d_nsg_guard : d_ceg_si->d_si_guard;
}

CegqiFairMode CegConjecture::getCegqiFairMode() {
  return isSingleInvocation() ? CEGQI_FAIR_NONE : options::ceGuidedInstFair();
}

bool CegConjecture::isSingleInvocation() const {
  return d_ceg_si->isSingleInvocation();
}

bool CegConjecture::isFullySingleInvocation() {
  return d_ceg_si->isFullySingleInvocation();
}

bool CegConjecture::needsCheck( std::vector< Node >& lem ) {
  if( isSingleInvocation() && !d_ceg_si->needsCheck() ){
    return false;
  }else{
    bool value;
    if( !isSingleInvocation() || isFullySingleInvocation() ){
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
    }else{
      // not fully single invocation : infeasible if overall specification is infeasible
      Assert( !d_ceg_si->d_full_guard.isNull() );
      if( d_qe->getValuation().hasSatValue( d_ceg_si->d_full_guard, value ) ) {
        if( !value ){
          Trace("cegqi-nsi") << "NSI : found full specification is infeasible." << std::endl;
          return false;
        }else{
          Assert( !d_ceg_si->d_si_guard.isNull() );
          if( d_qe->getValuation().hasSatValue( d_ceg_si->d_si_guard, value ) ) {
            if( !value ){
              if( !d_ceg_si->d_single_inv_exp.isNull() ){
                //this should happen infrequently : only if cegqi determines infeasibility of a false candidate before E-matching does
                Trace("cegqi-nsi") << "NSI : current single invocation lemma was infeasible, block assignment upon which conjecture was based." << std::endl;
                Node l = NodeManager::currentNM()->mkNode( OR, d_ceg_si->d_full_guard.negate(), d_ceg_si->d_single_inv_exp );
                lem.push_back( l );
                d_ceg_si->initializeNextSiConjecture();
              }
              return false;
            }
          }else{
            Assert( false );
          }
        }
      }else{
        Assert( false );
      }
    }
    return true;
  }
}


void CegConjecture::doCegConjectureSingleInvCheck(std::vector< Node >& lems) {
  if( d_ceg_si!=NULL ){
    d_ceg_si->check(lems);
  }
}

bool CegConjecture::needsRefinement() { 
  return !d_ce_sk.empty();
}

void CegConjecture::getConditionalCandidateList( std::vector< Node >& clist, Node curr, bool reqAdd ){
  Assert( options::sygusUnifCondSol() );
  std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( curr );
  if( it!=d_cinfo.end() ){
    if( !it->second.d_csol_cond.isNull() ){
      if( it->second.d_csol_status!=-1 ){
        int pstatus = getProgressStatus( curr );
        if( pstatus!=-1 ){
          Assert( it->second.d_csol_status==0 || it->second.d_csol_status==1 );
          //interested in model value for condition and branched variables
          clist.push_back( it->second.d_csol_cond );
          //assume_flat_ITEs
          clist.push_back( it->second.d_csol_var[it->second.d_csol_status] );
          //conditionally get the other branch
          getConditionalCandidateList( clist, it->second.d_csol_var[1-it->second.d_csol_status], false );
          return;
        }else{
          // it is progress-inactive, will not be included
        }
      }
      //otherwise, yet to expand branch
      if( !reqAdd ){
        // if we are not top-level, we can ignore this (it won't be part of solution)
        return;
      }
    }else{
      // a standard variable not handlable by unification
    }
    clist.push_back( curr );
  }
}

void CegConjecture::getCandidateList( std::vector< Node >& clist, bool forceOrig ) {
  if( options::sygusUnifCondSol() && !forceOrig ){
    for( unsigned i=0; i<d_candidates.size(); i++ ){
      getConditionalCandidateList( clist, d_candidates[i], true );
    }
  }else{
    clist.insert( clist.end(), d_candidates.begin(), d_candidates.end() );
  }
}

Node CegConjecture::constructConditionalCandidate( std::map< Node, Node >& cmv, Node curr ) {
  Assert( options::sygusUnifCondSol() );
  std::map< Node, Node >::iterator itc = cmv.find( curr );
  if( itc!=cmv.end() ){
    return itc->second;
  }else{
    std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( curr );
    if( it!=d_cinfo.end() ){
      if( !it->second.d_csol_cond.isNull() ){
        if( it->second.d_csol_status!=-1 ){
          int pstatus = getProgressStatus( curr );
          if( pstatus!=-1 ){
            Assert( it->second.d_csol_status==0 || it->second.d_csol_status==1 );
            Node v_curr = constructConditionalCandidate( cmv, it->second.d_csol_var[it->second.d_csol_status] );
            Node v_next = constructConditionalCandidate( cmv, it->second.d_csol_var[1-it->second.d_csol_status] );
            if( v_next.isNull() ){
              // try taking current branch as a leaf
              return v_curr;
            }else{
              Node v_cond = constructConditionalCandidate( cmv, it->second.d_csol_cond );
              std::vector< Node > args;
              args.push_back( it->second.d_csol_op );
              args.push_back( v_cond );
              args.push_back( it->second.d_csol_status==0 ? v_curr : v_next );
              args.push_back( it->second.d_csol_status==0 ? v_next : v_curr );
              return NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, args );
            }
          }
        }
      }
    }
  }
  return Node::null();
}

bool CegConjecture::constructCandidates( std::vector< Node >& clist, std::vector< Node >& model_values, std::vector< Node >& candidate_values ) {
  Assert( clist.size()==model_values.size() );
  if( options::sygusUnifCondSol() ){
    std::map< Node, Node > cmv;
    for( unsigned i=0; i<clist.size(); i++ ){
      cmv[ clist[i] ] = model_values[i];
    }
    for( unsigned i=0; i<d_candidates.size(); i++ ){
      Node n = constructConditionalCandidate( cmv, d_candidates[i] );
      Trace("cegqi-candidate") << "...constructed conditional candidate " << n << " for " << d_candidates[i] << std::endl;
      candidate_values.push_back( n );
      if( n.isNull() ){
        Assert( false ); //currently should never happen
        return false;
      }
    }
  }else{
    Assert( model_values.size()==d_candidates.size() );
    candidate_values.insert( candidate_values.end(), model_values.begin(), model_values.end() );
  }
  return true;
}

void CegConjecture::doCegConjectureCheck(std::vector< Node >& lems, std::vector< Node >& model_values) {
  std::vector< Node > clist;
  getCandidateList( clist );
  std::vector< Node > c_model_values;
  Trace("cegqi-check") << "CegConjuncture : check, build candidates..." << std::endl;
  if( constructCandidates( clist, model_values, c_model_values ) ){
    Assert( c_model_values.size()==d_candidates.size() );
    if( Trace.isOn("cegqi-check")  ){
      Trace("cegqi-check") << "CegConjuncture : check candidate : " << std::endl;
      for( unsigned i=0; i<c_model_values.size(); i++ ){
        Trace("cegqi-check") << "  " << i << " : " << d_candidates[i] << " -> " << c_model_values[i] << std::endl;
      }
    }
    //must get a counterexample to the value of the current candidate
    Node inst = d_base_inst.substitute( d_candidates.begin(), d_candidates.end(), c_model_values.begin(), c_model_values.end() );
    bool hasActiveConditionalNode = false;
    if( options::sygusUnifCondSol() ){
      //TODO
      hasActiveConditionalNode = true;
    }
    //check whether we will run CEGIS on inner skolem variables
    bool sk_refine = ( !isGround() || d_refine_count==0 || hasActiveConditionalNode );
    if( sk_refine ){
      Assert( d_ce_sk.empty() );
      d_ce_sk.push_back( std::vector< Node >() );
    }
    std::vector< Node > ic;
    ic.push_back( d_assert_quant.negate() );
    std::vector< Node > d;
    CegInstantiation::collectDisjuncts( inst, d );
    Assert( d.size()==d_base_disj.size() );
    //immediately skolemize inner existentials
    for( unsigned i=0; i<d.size(); i++ ){
      Node dr = Rewriter::rewrite( d[i] );
      if( dr.getKind()==NOT && dr[0].getKind()==FORALL ){
        ic.push_back( d_qe->getTermDatabase()->getSkolemizedBody( dr[0] ).negate() );
        if( sk_refine ){
          d_ce_sk.back().push_back( dr[0] );
        }
      }else{
        ic.push_back( dr );
        if( sk_refine ){
          d_ce_sk.back().push_back( Node::null() );
        }
        if( !d_inner_vars_disj[i].empty() ){
          Trace("cegqi-debug") << "*** quantified disjunct : " << d[i] << " simplifies to " << dr << std::endl;
        }
      }
    }
    Node lem = NodeManager::currentNM()->mkNode( OR, ic );
    lem = Rewriter::rewrite( lem );
    lems.push_back( lem );
    recordInstantiation( c_model_values );
  }else{
    Assert( false );
  }
}

Node CegConjecture::getActiveConditional( Node curr ) {
  Assert( options::sygusUnifCondSol() );
  std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( curr );
  Assert( it!=d_cinfo.end() );
  if( !it->second.d_csol_cond.isNull() ){
    if( it->second.d_csol_status==-1 ){
      //yet to branch, this is the one
      return curr;
    }else{
      int pstatus = getProgressStatus( curr );
      if( pstatus==-1 ){
        // it is progress-inactive
        return curr;
      }else{
        Assert( it->second.d_csol_status==0 || it->second.d_csol_status==1 );
        return getActiveConditional( it->second.d_csol_var[1-it->second.d_csol_status] );
      }
    }
  }else{
    //not a conditional
    return curr;
  }
}

void CegConjecture::getContextConditionalNodes( Node curr, Node x, std::vector< Node >& nodes ) {
  if( curr!=x ){
    std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( curr );
    if( !it->second.d_csol_cond.isNull() ){
      if( it->second.d_csol_status!=-1 ){
        nodes.push_back( curr );
        getContextConditionalNodes( it->second.d_csol_var[1-it->second.d_csol_status], x, nodes );
      }
    }
  }
}

Node CegConjecture::mkConditionalEvalNode( Node c, std::vector< Node >& args ) {
  Assert( !c.isNull() );
  std::vector< Node > condc;
  //get evaluator
  Assert( c.getType().isDatatype() );
  const Datatype& cd = ((DatatypeType)c.getType().toType()).getDatatype();
  Assert( cd.isSygus() );
  condc.push_back( Node::fromExpr( cd.getSygusEvaluationFunc() ) );
  condc.push_back( c );
  for( unsigned a=0; a<args.size(); a++ ){
    condc.push_back( args[a] );
  }
  return NodeManager::currentNM()->mkNode( kind::APPLY_UF, condc );
}

Node CegConjecture::mkConditionalNode( Node v, std::vector< Node >& args, unsigned eindex ) {
  std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( v );
  if( it!=d_cinfo.end() ){
    Assert( eindex<=2 );
    Node en = eindex==0 ? it->second.d_csol_cond : it->second.d_csol_var[eindex-1];
    if( !en.isNull() ){
      Node ret = mkConditionalEvalNode( en, args );
      //consider template
      std::map< unsigned, Node >::iterator itt = it->second.d_template.find( eindex );
      if( itt!=it->second.d_template.end() ){
        Assert( it->second.d_template_arg.find( eindex )!=it->second.d_template_arg.end() );
        TNode var = it->second.d_template_arg[eindex];
        TNode subs = ret;
        Node rret = itt->second.substitute( var, subs );
        ret = rret;
      }
      return ret;
    }
  }
  Assert( false );
  return Node::null();
}

Node CegConjecture::mkConditional( Node v, std::vector< Node >& args, bool pol ) {
  Node ret = mkConditionalNode( v, args, 0 );
  if( !pol ){
    ret = ret.negate();
  }
  return ret;
}
  
Node CegConjecture::purifyConditionalEvaluations( Node n, std::map< Node, Node >& csol_active, std::map< Node, Node >& psubs, std::map< Node, Node >& visited ){
  std::map< Node, Node >::iterator itv = visited.find( n );
  if( itv!=visited.end() ){
    return itv->second;
  }else{
    Node ret;
    if( n.getKind()==APPLY_UF ){
      std::map< Node, Node >::iterator itc = csol_active.find( n[0] );
      if( itc!=csol_active.end() ){
        //purify it with a variable
        ret = NodeManager::currentNM()->mkSkolem( "y", n.getType(), "purification variable for sygus conditional solution" );
        psubs[n] = ret;
      }
    }
    if( ret.isNull() ){
      ret = n;
      if( n.getNumChildren()>0 ){
        std::vector< Node > children;
        if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
          children.push_back( n.getOperator() );
        }
        bool childChanged = false;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          Node nc = purifyConditionalEvaluations( n[i], csol_active, psubs, visited );
          childChanged = childChanged || nc!=n[i];
          children.push_back( nc );
        }
        if( childChanged ){
          ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
        }
      }
    }
    visited[n] = ret;
    return ret;
  }
}
        
void CegConjecture::doCegConjectureRefine( std::vector< Node >& lems ){
  Assert( lems.empty() );
  Assert( d_ce_sk.size()==1 );

  //first, make skolem substitution
  Trace("cegqi-refine") << "doCegConjectureRefine : construct skolem substitution..." << std::endl;
  std::vector< Node > sk_vars;
  std::vector< Node > sk_subs;
  //collect the substitution over all disjuncts
  for( unsigned k=0; k<d_ce_sk[0].size(); k++ ){
    Node ce_q = d_ce_sk[0][k];
    if( !ce_q.isNull() ){
      Assert( !d_inner_vars_disj[k].empty() );
      Assert( d_inner_vars_disj[k].size()==d_qe->getTermDatabase()->d_skolem_constants[ce_q].size() );
      std::vector< Node > model_values;
      getModelValues( d_qe->getTermDatabase()->d_skolem_constants[ce_q], model_values );
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
  
  
  std::map< Node, Node > csol_active;
  std::map< Node, std::vector< Node > > csol_ccond_nodes;
  std::map< Node, std::map< Node, bool > > csol_cpol;    
  if( options::sygusUnifCondSol() ){
    //previous non-ground conditional refinement lemmas must satisfy the current point
    if( !isGround() ){
      Trace("cegqi-refine") << "doCegConjectureRefine : check for new refinements of previous lemmas..." << std::endl;
      for( unsigned i=0; i<d_refinement_lemmas_ngr.size(); i++ ){
        Node prev_lem = d_refinement_lemmas_ngr[i];
        prev_lem = prev_lem.substitute( sk_vars.begin(), sk_vars.end(), sk_subs.begin(), sk_subs.end() );
        if( d_refinement_lemmas_reproc.find( prev_lem )==d_refinement_lemmas_reproc.end() ){
          d_refinement_lemmas_reproc[prev_lem] = true;
          //do auxiliary variable substitution
          std::vector< Node > subs;
          for( unsigned ii=0; ii<d_refinement_lemmas_aux_vars[i].size(); ii++ ){
            subs.push_back( NodeManager::currentNM()->mkSkolem( "y", d_refinement_lemmas_aux_vars[i][ii].getType(), 
                                                                "purification variable for non-ground sygus conditional solution" ) );
          }
          prev_lem = prev_lem.substitute( d_refinement_lemmas_aux_vars[i].begin(), d_refinement_lemmas_aux_vars[i].end(), subs.begin(), subs.end() );
          prev_lem = Rewriter::rewrite( prev_lem );
          Trace("sygus-unif") << "...previous conditional refinement lemma with new counterexample : " << prev_lem << std::endl;
          lems.push_back( prev_lem );
        }
      }
      if( !lems.empty() ){  
        Trace("cegqi-refine") << "...added lemmas, abort further refinement." << std::endl;
        d_ce_sk.clear();
        return;
      }
    }
    Trace("cegqi-refine") << "doCegConjectureRefine : conditional solution refinement, expand active conditional nodes" << std::endl;
    std::vector< Node > new_active_measure_sum;
    for( unsigned i=0; i<d_candidates.size(); i++ ){
      Node v = d_candidates[i];
      Node ac = getActiveConditional( v );
      Assert( !ac.isNull() );
      //compute the contextual conditions
      getContextConditionalNodes( v, ac, csol_ccond_nodes[v] );
      if( !csol_ccond_nodes[v].empty() ){
        //it will be conditionally evaluated, this is a placeholder
        csol_active[v] = Node::null();
      }
      Trace("sygus-unif") << "Active conditional for " << v << " is : " << ac << std::endl;
      //if it is a conditional
      bool is_active_conditional = false;
      if( !d_cinfo[ac].d_csol_cond.isNull() ){
        int pstatus = getProgressStatus( ac );
        Assert( pstatus!=0 );
        if( pstatus==-1 ){
          //inject new progress point TODO?
          Trace("sygus-unif") << "...progress status is " << pstatus << ", do not expand." << std::endl;
          Assert( false );
        }else{
          is_active_conditional = true;
          //expand this conditional
          Trace("sygus-unif") << "****** For " << v << ", expanding an active conditional node : " << ac << std::endl;
          d_cinfo[ac].d_csol_status = 0;  //TODO: prefer some branches more than others based on the grammar?
          Trace("sygus-unif") << "...expanded to " << d_cinfo[ac].d_csol_op << "( ";
          Trace("sygus-unif") << d_cinfo[ac].d_csol_cond << ", " << d_cinfo[ac].d_csol_var[0] << ", ";
          Trace("sygus-unif") << d_cinfo[ac].d_csol_var[1] << " )" << std::endl;
          registerCandidateConditional( d_cinfo[ac].d_csol_var[1-d_cinfo[ac].d_csol_status] );
          //add to measure sum
          Node acfc = getMeasureTermFactor( d_cinfo[ac].d_csol_cond );
          if( !acfc.isNull() ){
            new_active_measure_sum.push_back( acfc );
          }
          Node acfv = getMeasureTermFactor( d_cinfo[ac].d_csol_var[d_cinfo[ac].d_csol_status] );
          if( !acfv.isNull() ){
            new_active_measure_sum.push_back( acfv );
          }
          csol_active[v] = ac;
        }
      }
      if( !is_active_conditional ){
        Trace("sygus-unif") << "* For " << v << ", its active node " << ac << " is not a conditional node." << std::endl;
        //if we have not already included this in the measure, do so
        if( d_cinfo[ac].d_csol_status==-1 ){
          Node acf = getMeasureTermFactor( ac );
          if( !acf.isNull() ){
            new_active_measure_sum.push_back( acf );
          }
          d_cinfo[ac].d_csol_status = 2;
        }
      }
      if( !csol_ccond_nodes[v].empty() ){
        Trace("sygus-unif") << "...it is nested under " << csol_ccond_nodes[v].size() << " other conditionals" << std::endl;
      }
    }
    // must add to active measure
    if( !new_active_measure_sum.empty() ){
      Node mcsum = new_active_measure_sum.size()==1 ? new_active_measure_sum[0] : NodeManager::currentNM()->mkNode( kind::PLUS, new_active_measure_sum );
      Node mclem = NodeManager::currentNM()->mkNode( kind::LEQ, mcsum, d_active_measure_term );
      Trace("cegqi-lemma") << "Cegqi::Lemma : Measure component lemma : " << mclem << std::endl;
      d_qe->getOutputChannel().lemma( mclem );
      /*    
      for( unsigned i=0; i<new_active_measure_sum.size(); i++ ){
        Node mclem = NodeManager::currentNM()->mkNode( kind::LEQ, new_active_measure_sum[i], d_active_measure_term );
        Trace("cegqi-lemma") << "Cegqi::Lemma : Measure component lemma : " << mclem << std::endl;
        d_qe->getOutputChannel().lemma( mclem );
      }
      
      Node new_active_measure = NodeManager::currentNM()->mkSkolem( "K", NodeManager::currentNM()->integerType() );
      new_active_measure_sum.push_back( new_active_measure );
      Node namlem = NodeManager::currentNM()->mkNode( kind::GEQ, new_active_measure, NodeManager::currentNM()->mkConst(Rational(0)));
      Node ramlem = d_active_measure_term.eqNode( NodeManager::currentNM()->mkNode( kind::PLUS, new_active_measure_sum ) );
      namlem = NodeManager::currentNM()->mkNode( kind::AND, ramlem, namlem );
      Trace("cegqi-lemma") << "Cegqi::Lemma : Measure expansion : " << namlem << std::endl;
      d_qe->getOutputChannel().lemma( namlem );
      d_active_measure_term = new_active_measure;
      */
    }
  }
  
  //for conditional evaluation
  std::map< Node, Node > psubs_visited;
  std::map< Node, Node > psubs;
  std::vector< Node > lem_c;
  Assert( d_ce_sk[0].size()==d_base_disj.size() );
  std::vector< Node > inst_cond_c;
  Trace("cegqi-refine") << "doCegConjectureRefine : Construct refinement lemma..." << std::endl;
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
      if( options::sygusUnifCondSol() ){
        Trace("sygus-unif") << "Process " << c_disj << std::endl;
        c_disj = purifyConditionalEvaluations( c_disj, csol_active, psubs, psubs_visited );
        Trace("sygus-unif") << "Purified to : " << c_disj << std::endl;
        Trace("sygus-unif") << "...now with " << psubs.size() << " definitions." << std::endl;
      }else{
        //standard CEGIS refinement : plug in values, assert that d_candidates must satisfy entire specification
      }
      lem_c.push_back( c_disj );
    }
  }
  Assert( sk_vars.size()==sk_subs.size() );
  //add conditional correctness assumptions
  std::vector< Node > psubs_cond_ant;
  std::vector< Node > psubs_cond_conc;
  std::map< Node, std::vector< Node > > psubs_apply;
  std::vector< Node > paux_vars;
  if( options::sygusUnifCondSol() ){
    Trace("cegqi-refine") << "doCegConjectureRefine : add conditional assumptions for " << psubs.size() << " evaluations..." << std::endl;
    for( std::map< Node, Node >::iterator itp = psubs.begin(); itp != psubs.end(); ++itp ){
      Assert( csol_active.find( itp->first[0] )!=csol_active.end() );
      paux_vars.push_back( itp->second );
      std::vector< Node > args;
      for( unsigned a=1; a<itp->first.getNumChildren(); a++ ){
        args.push_back( itp->first[a] );
      }
      Node ac = csol_active[itp->first[0]];
      Assert( d_cinfo.find( ac )!=d_cinfo.end() );
      Node c = d_cinfo[ac].d_csol_cond;
      psubs_apply[ c ].push_back( itp->first );
      Trace("sygus-unif") << "   process assumption " << itp->first << " == " << itp->second << ", with current condition " << c;
      Trace("sygus-unif") << ", and " << csol_ccond_nodes[itp->first[0]].size() << " context conditionals." << std::endl;
      std::vector< Node> assm;
      if( !c.isNull() ){
        assm.push_back( mkConditional( ac, args, true ) );
      }
      for( unsigned j=0; j<csol_ccond_nodes[itp->first[0]].size(); j++ ){
        Node acc = csol_ccond_nodes[itp->first[0]][j];
        bool pol = ( d_cinfo[acc].d_csol_status==1 );
        assm.push_back( mkConditional( acc, args, pol ) );
      }
      Assert( !assm.empty() );
      Node c_ant = assm.size()==1 ? assm[0] : NodeManager::currentNM()->mkNode( kind::AND, assm );
      psubs_cond_ant.push_back( c_ant );
      // make the evaluation node
      Node eret = mkConditionalNode( ac, args, d_cinfo[ac].d_csol_status+1 );
      Node c_conc = eret.eqNode( itp->second );
      psubs_cond_conc.push_back( c_conc );
      Trace("sygus-unif") << "   ...made conditional correctness assumption : " << c_ant << " => " << c_conc << std::endl;
    }
  }else{
    Assert( psubs.empty() );
  }
  
  Node base_lem = lem_c.size()==1 ? lem_c[0] : NodeManager::currentNM()->mkNode( AND, lem_c );
  
  if( options::sygusUnifCondSol() ){
    Trace("sygus-unif-debug") << "We have base lemma : " << base_lem << std::endl;
    //progress lemmas
    Trace("cegqi-refine") << "doCegConjectureRefine : add progress lemmas..." << std::endl;
    std::map< Node, bool > cprocessed;
    for( std::map< Node, Node >::iterator itc = csol_active.begin(); itc !=csol_active.end(); ++itc ){
      Node x = itc->first;
      Node ac = itc->second;
      Assert( d_cinfo.find( ac )!=d_cinfo.end() );
      Node c = d_cinfo[ac].d_csol_cond;    
      if( !c.isNull() ){
        Trace("sygus-unif") << "  process conditional " << c << " for " << x << ", which was applied " << psubs_apply[c].size() << " times." << std::endl;
        //make the progress point
        Assert( x.getType().isDatatype() );
        const Datatype& dx = ((DatatypeType)x.getType().toType()).getDatatype();
        Node sbvl = Node::fromExpr( dx.getSygusVarList() );
        std::vector< Node > prgr_pt;
        for( unsigned a=0; a<sbvl.getNumChildren(); a++ ){
          prgr_pt.push_back( NodeManager::currentNM()->mkSkolem( "kp", sbvl[a].getType(), "progress point for sygus conditional" ) );
        }
        Node pdlem;    
        if( !psubs_apply[c].empty() ){
          std::vector< Node > prgr_domain_d;
          for( unsigned j=0; j<psubs_apply[c].size(); j++ ){
            std::vector< Node > prgr_domain;
            for( unsigned a=1; a<psubs_apply[c][j].getNumChildren(); a++ ){
              Assert( a<=prgr_pt.size() );
              prgr_domain.push_back( prgr_pt[a-1].eqNode( psubs_apply[c][j][a] ) );
            }
            if( !prgr_domain.empty() ){
              //the point is in the domain of this function application
              Node pdc = prgr_domain.size()==1 ? prgr_domain[0] : NodeManager::currentNM()->mkNode( AND, prgr_domain );
              prgr_domain_d.push_back( pdc );
            }
          }
          if( !prgr_domain_d.empty() ){
            //the progress point is in the domain of some function application
            pdlem = prgr_domain_d.size()==1 ? prgr_domain_d[0] : NodeManager::currentNM()->mkNode( OR, prgr_domain_d );
            pdlem = pdlem.substitute( sk_vars.begin(), sk_vars.end(), sk_subs.begin(), sk_subs.end() );
            Trace("sygus-unif") << "Progress domain point lemma is " << pdlem << std::endl;
            lems.push_back( pdlem );
          }
        }
        //the condition holds for the point, if this is an active condition
        Node cplem = mkConditional( ac, prgr_pt );
        if( !csol_ccond_nodes[x].empty() ){
          std::vector< Node > prgr_conj;
          prgr_conj.push_back( cplem );
          // ...and not for its context
          for( unsigned j=0; j<csol_ccond_nodes[x].size(); j++ ){
            Node acc = csol_ccond_nodes[x][j];
            bool pol = ( d_cinfo[acc].d_csol_status==1 );
            prgr_conj.push_back( mkConditional( acc, prgr_pt, pol ) );
          }
          cplem = NodeManager::currentNM()->mkNode( kind::AND, prgr_conj );
        }
        Assert( !d_cinfo[x].d_csol_progress_guard.isNull() );
        cplem = NodeManager::currentNM()->mkNode( kind::OR, d_cinfo[x].d_csol_progress_guard.negate(), cplem );
        Trace("sygus-unif") << "Progress lemma is " << cplem << std::endl;
        lems.push_back( cplem );
      }
    }
    /*
    if( !prgr_conj.empty() ){
      Node prgr_lem = prgr_conj.size()==1 ? prgr_conj[0] : NodeManager::currentNM()->mkNode( kind::AND, prgr_conj );
      prgr_lem = prgr_lem.substitute( sk_vars.begin(), sk_vars.end(), sk_subs.begin(), sk_subs.end() );
      prgr_lem = NodeManager::currentNM()->mkNode( OR, getGuard().negate(), prgr_lem );
      Trace("sygus-unif") << "Progress lemma is " << prgr_lem << std::endl;
      lems.push_back( prgr_lem );
    }
    */
  }
  
  Trace("cegqi-refine") << "doCegConjectureRefine : construct and finalize lemmas..." << std::endl;
  
  Node lem = base_lem;
  
  base_lem = base_lem.substitute( sk_vars.begin(), sk_vars.end(), sk_subs.begin(), sk_subs.end() );
  base_lem = Rewriter::rewrite( base_lem );
  d_refinement_lemmas_base.push_back( base_lem );
  
  if( options::sygusUnifCondSol() ){
    //add the conditional evaluation
    if( !psubs_cond_ant.empty() ){
      std::vector< Node > children;
      children.push_back( base_lem );
      std::vector< Node > pav;
      std::vector< Node > pcv;
      for( unsigned i=0; i<psubs_cond_ant.size(); i++ ){
        children.push_back( NodeManager::currentNM()->mkNode( kind::OR, psubs_cond_ant[i].negate(), psubs_cond_conc[i] ) );
        Node pa = psubs_cond_ant[i].substitute( sk_vars.begin(), sk_vars.end(), sk_subs.begin(), sk_subs.end() );
        pav.push_back( pa );
        Node pc = psubs_cond_conc[i].substitute( sk_vars.begin(), sk_vars.end(), sk_subs.begin(), sk_subs.end() );
        pcv.push_back( pc );
      }
      d_refinement_lemmas_ceval_ant.push_back( pav );
      d_refinement_lemmas_ceval_conc.push_back( pcv );
      lem = NodeManager::currentNM()->mkNode( AND, children );
    }
  }

  lem = NodeManager::currentNM()->mkNode( OR, getGuard().negate(), lem );
  
  if( options::sygusUnifCondSol() ){
    if( !isGround() ){
      //store the non-ground version of the lemma
      lem = Rewriter::rewrite( lem );
      d_refinement_lemmas_ngr.push_back( lem );
      d_refinement_lemmas_aux_vars.push_back( paux_vars );
    }
  }
  
  lem = lem.substitute( sk_vars.begin(), sk_vars.end(), sk_subs.begin(), sk_subs.end() );
  lem = Rewriter::rewrite( lem );
  d_refinement_lemmas.push_back( lem );
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
      std::vector< Node > lvs;
      TermDbSygus::printSygusTerm( ss, nv, lvs );
      Trace("cegqi-engine") << ss.str() << " ";
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
  Trace(c) << "Synthesis conjecture : " << d_quant << std::endl;
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

int CegConjecture::getProgressStatus( Node v ) {
  Assert( options::sygusUnifCondSol() );
  std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( v );
  if( it!=d_cinfo.end() ){
    if( !it->second.d_csol_cond.isNull() ){
      if( it->second.d_csol_status!=-1 ){
        Node plit = it->second.d_csol_progress_guard;
        Assert( !plit.isNull() );
        //check SAT value of plit
        bool value;
        if( d_qe->getValuation().hasSatValue( plit, value ) ) {
          if( !value ){
            return -1;
          }else{
            return 1;
          }
        }else{
          return 0;
        }
      }
    }
  }
  return -2;
}

Node CegConjecture::getNextDecisionRequestConditional( Node v, unsigned& priority ) {
  Assert( options::sygusUnifCondSol() );
  int pstatus = getProgressStatus( v );
  if( pstatus>=0 ){
    std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( v );
    Assert( it!=d_cinfo.end() );
    if( pstatus==1 ){
      //active, recurse
      Assert( it->second.d_csol_status==0 || it->second.d_csol_status==1 );
      return getNextDecisionRequestConditional( it->second.d_csol_var[1-it->second.d_csol_status], priority );
    }else if( pstatus==0 ){
      //needs decision
      priority = 1;
      return it->second.d_csol_progress_guard;
    }
  }
  return Node::null();
}

Node CegConjecture::getNextDecisionRequest( unsigned& priority ) {
  if( options::sygusUnifCondSol() ){
    for( unsigned i=0; i<d_candidates.size(); i++ ){
      Node lit = getNextDecisionRequestConditional( d_candidates[i], priority );
      if( !lit.isNull() ){
        return lit;
      }
    }
  }
  return Node::null();
}

CegInstantiation::CegInstantiation( QuantifiersEngine * qe, context::Context* c ) : QuantifiersModule( qe ){
  d_conj = new CegConjecture( qe, qe->getSatContext() );
  d_last_inst_si = false;
}

CegInstantiation::~CegInstantiation(){ 
  delete d_conj;
}

bool CegInstantiation::needsCheck( Theory::Effort e ) {
  return e>=Theory::EFFORT_LAST_CALL;
}

unsigned CegInstantiation::needsModel( Theory::Effort e ) {
  return d_conj->getCegConjectureSingleInv()->isSingleInvocation()
      ? QuantifiersEngine::QEFFORT_STANDARD : QuantifiersEngine::QEFFORT_MODEL;
}

void CegInstantiation::check( Theory::Effort e, unsigned quant_e ) {
  unsigned echeck = d_conj->getCegConjectureSingleInv()->isSingleInvocation() ?
      QuantifiersEngine::QEFFORT_STANDARD : QuantifiersEngine::QEFFORT_MODEL;
  if( quant_e==echeck ){
    Trace("cegqi-engine") << "---Counterexample Guided Instantiation Engine---" << std::endl;
    Trace("cegqi-engine-debug") << std::endl;
    bool active = false;
    bool value;
    if( d_quantEngine->getValuation().hasSatValue( d_conj->d_assert_quant, value ) ) {
      active = value;
    }else{
      Trace("cegqi-engine-debug") << "...no value for quantified formula." << std::endl;
    }
    Trace("cegqi-engine-debug") << "Current conjecture status : active : " << active << std::endl;
    std::vector< Node > lem;
    if( active && d_conj->needsCheck( lem ) ){
      checkCegConjecture( d_conj );
    }else{
      Trace("cegqi-engine-debug") << "...does not need check." << std::endl;
      for( unsigned i=0; i<lem.size(); i++ ){
        Trace("cegqi-lemma") << "Cegqi::Lemma : check lemma : " << lem[i] << std::endl;
        d_quantEngine->addLemma( lem[i] );
      }
    }
    Trace("cegqi-engine") << "Finished Counterexample Guided Instantiation engine." << std::endl;
  }
}

void CegInstantiation::preRegisterQuantifier( Node q ) {
  if( options::sygusDirectEval() ){
    if( q.getNumChildren()==3 && q[2].getKind()==INST_PATTERN_LIST && q[2][0].getKind()==INST_PATTERN ){  
      //check whether it is an evaluation axiom
      Node pat = q[2][0][0];
      if( pat.getKind()==APPLY_UF ){
        TypeNode tn = pat[0].getType();
        if( tn.isDatatype() ){
          const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
          if( dt.isSygus() ){
            //do unfolding if it induces Boolean structure, 
            //do direct evaluation if it does not induce Boolean structure,
            //  the reasoning is unfolding over these terms does not lead to helpful conflict analysis, and introduces many shared terms
            bool directEval = true;
            TypeNode ptn = pat.getType();
            if( ptn.isBoolean() ){
              directEval = false;
            }else{
              unsigned cindex = Datatype::indexOf(pat[0].getOperator().toExpr() );
              Node base = d_quantEngine->getTermDatabaseSygus()->getGenericBase( tn, dt, cindex );
              Trace("cegqi-debug") << "Generic base term for " << pat[0] << " is " << base << std::endl;
              if( base.getKind()==ITE ){
                directEval = false;
              }
            }
            if( directEval ){
              //take ownership of this quantified formula (will use direct evaluation instead of unfolding instantiation)
              d_quantEngine->setOwner( q, this );
              d_eval_axioms[q] = true;
            }
          }
        }
      }
    }
  }  
}

void CegInstantiation::registerQuantifier( Node q ) {
  if( d_quantEngine->getOwner( q )==this && d_eval_axioms.find( q )==d_eval_axioms.end() ){
    if( !d_conj->isAssigned() ){
      Trace("cegqi") << "Register conjecture : " << q << std::endl;
      d_conj->assign( q );

      //fairness
      if( d_conj->getCegqiFairMode()!=CEGQI_FAIR_NONE ){
        std::vector< Node > mc;
        if( options::sygusUnifCondSol() || 
            d_conj->getCegqiFairMode()==CEGQI_FAIR_DT_HEIGHT_PRED || d_conj->getCegqiFairMode()==CEGQI_FAIR_DT_SIZE_PRED  ){
          //measure term is a fresh constant
          mc.push_back( NodeManager::currentNM()->mkSkolem( "K", NodeManager::currentNM()->integerType() ) );
        }else{
          std::vector< Node > clist;
          d_conj->getCandidateList( clist, true );
          for( unsigned j=0; j<clist.size(); j++ ){
            TypeNode tn = clist[j].getType();
            if( d_conj->getCegqiFairMode()==CEGQI_FAIR_DT_SIZE ){
              if( tn.isDatatype() ){
                mc.push_back( NodeManager::currentNM()->mkNode( DT_SIZE, clist[j] ) );
              }
            }else if( d_conj->getCegqiFairMode()==CEGQI_FAIR_UF_DT_SIZE ){
              registerMeasuredType( tn );
              std::map< TypeNode, Node >::iterator it = d_uf_measure.find( tn );
              if( it!=d_uf_measure.end() ){
                mc.push_back( NodeManager::currentNM()->mkNode( APPLY_UF, it->second, clist[j] ) );
              }
            }
          }
        }
        if( !mc.empty() ){
          Node mt = mc.size()==1 ? mc[0] : NodeManager::currentNM()->mkNode( PLUS, mc );
          Trace("cegqi") << "Measure term is : " << mt << std::endl;
          d_conj->setMeasureTerm( mt );
        }
      }
    }else{
      Assert( d_conj->d_quant==q );
    }
  }else{
    Trace("cegqi-debug") << "Register quantifier : " << q << std::endl;
  }
}

void CegInstantiation::assertNode( Node n ) {
}

Node CegInstantiation::getNextDecisionRequest( unsigned& priority ) {
  //enforce fairness
  if( d_conj->isAssigned() ){
    d_conj->initializeGuard();
    // 
    std::vector< Node > req_dec;
    const CegConjectureSingleInv* ceg_si = d_conj->getCegConjectureSingleInv();
    if( ! ceg_si->d_full_guard.isNull() ){
      req_dec.push_back( ceg_si->d_full_guard );
    }
    //must decide ns guard before s guard
    if( !ceg_si->d_ns_guard.isNull() ){
      req_dec.push_back( ceg_si->d_ns_guard );
    }
    req_dec.push_back( d_conj->getGuard() );
    for( unsigned i=0; i<req_dec.size(); i++ ){
      bool value;
      if( !d_quantEngine->getValuation().hasSatValue( req_dec[i], value ) ) {
        Trace("cegqi-debug") << "CEGQI : Decide next on : " << req_dec[i] << "..." << std::endl;
        priority = 0;
        return req_dec[i];
      }else{
        Trace("cegqi-debug2") << "CEGQI : " << req_dec[i] << " already has value " << value << std::endl;
      }
    }
    
    //ask the conjecture directly
    Node lit = d_conj->getNextDecisionRequest( priority );
    if( !lit.isNull() ){
      return lit;
    }

    if( d_conj->getCegqiFairMode()!=CEGQI_FAIR_NONE ){
      Node lit = d_conj->getFairnessLiteral( d_conj->getCurrentTermSize() );
      bool value;
      if( d_quantEngine->getValuation().hasSatValue( lit, value ) ) {
        if( !value ){
          d_conj->incrementCurrentTermSize();
          lit = d_conj->getFairnessLiteral( d_conj->getCurrentTermSize() );
          Trace("cegqi-debug") << "CEGQI : Decide on next lit : " << lit << "..." << std::endl;
          priority = 1;
          return lit;
        }
      }else{
        Trace("cegqi-debug") << "CEGQI : Decide on current lit : " << lit << "..." << std::endl;
        priority = 1;
        return lit;
      }
    }
  }

  return Node::null();
}

void CegInstantiation::checkCegConjecture( CegConjecture * conj ) {
  Node q = conj->d_quant;
  Node aq = conj->d_assert_quant;
  if( Trace.isOn("cegqi-engine-debug") ){
    conj->debugPrint("cegqi-engine-debug");
    Trace("cegqi-engine-debug") << std::endl;
  }
  if( conj->getCegqiFairMode()!=CEGQI_FAIR_NONE ){
    Trace("cegqi-engine") << "  * Current term size : " << conj->getCurrentTermSize() << std::endl;
  }  

  if( !conj->needsRefinement() ){
    if( conj->d_syntax_guided ){
      std::vector< Node > clems;
      conj->doCegConjectureSingleInvCheck( clems );
      if( !clems.empty() ){
        d_last_inst_si = true;
        for( unsigned j=0; j<clems.size(); j++ ){
          Trace("cegqi-lemma") << "Cegqi::Lemma : single invocation instantiation : " << clems[j] << std::endl;
          d_quantEngine->addLemma( clems[j] );
        }
        d_statistics.d_cegqi_si_lemmas += clems.size();
        Trace("cegqi-engine") << "  ...try single invocation." << std::endl;
        return;
      }
      //ignore return value here
      std::vector< Node > clist;
      conj->getCandidateList( clist );
      std::vector< Node > model_values;
      conj->getModelValues( clist, model_values );
      if( options::sygusDirectEval() ){
        bool addedEvalLemmas = false;
        if( options::sygusCRefEval() ){
          Trace("cegqi-debug") << "Do cref evaluation..." << std::endl;
          // see if any refinement lemma is refuted by evaluation
          std::vector< Node > cre_lems;
          getCRefEvaluationLemmas( conj, clist, model_values, cre_lems );
          if( !cre_lems.empty() ){
            Trace("cegqi-engine") << "  *** Do conjecture refinement evaluation..." << std::endl;
            for( unsigned j=0; j<cre_lems.size(); j++ ){
              Node lem = cre_lems[j];
              Trace("cegqi-lemma") << "Cegqi::Lemma : cref evaluation : " << lem << std::endl;
              if( d_quantEngine->addLemma( lem ) ){
                addedEvalLemmas = true;
              }
            }
            if( addedEvalLemmas ){
              return;
            }
          }
        }
        Trace("cegqi-debug") << "Do direct evaluation..." << std::endl;
        std::vector< Node > eager_terms; 
        std::vector< Node > eager_vals; 
        std::vector< Node > eager_exps;
        for( unsigned j=0; j<clist.size(); j++ ){
          Trace("cegqi-debug") << "  register " << clist[j] << " -> " << model_values[j] << std::endl;
          d_quantEngine->getTermDatabaseSygus()->registerModelValue( clist[j], model_values[j], eager_terms, eager_vals, eager_exps );
        }
        Trace("cegqi-debug") << "...produced " << eager_terms.size()  << " eager evaluation lemmas." << std::endl;
        if( !eager_terms.empty() ){
          Trace("cegqi-engine") << "  *** Do direct evaluation..." << std::endl;
          for( unsigned j=0; j<eager_terms.size(); j++ ){
            Node lem = NodeManager::currentNM()->mkNode( kind::OR, eager_exps[j].negate(), eager_terms[j].eqNode( eager_vals[j] ) );
            if( d_quantEngine->getTheoryEngine()->isTheoryEnabled(THEORY_BV) ){
              //FIXME: hack to incorporate hacks from BV for division by zero
              lem = bv::TheoryBVRewriter::eliminateBVSDiv( lem );
            }
            Trace("cegqi-lemma") << "Cegqi::Lemma : evaluation : " << lem << std::endl;
            if( d_quantEngine->addLemma( lem ) ){
              addedEvalLemmas = true;
            }
          }
        }
        if( addedEvalLemmas ){
          return;
        }
      }
      //check if we must apply fairness lemmas
      if( conj->getCegqiFairMode()==CEGQI_FAIR_UF_DT_SIZE ){
        Trace("cegqi-debug") << "Get measure lemmas..." << std::endl;
        std::vector< Node > lems;
        for( unsigned j=0; j<clist.size(); j++ ){
          Trace("cegqi-debug") << "  get measure lemmas for " << clist[j] << " -> " << model_values[j] << std::endl;
          getMeasureLemmas( clist[j], model_values[j], lems );
        }
        Trace("cegqi-debug") << "...produced " << lems.size() << " measure lemmas." << std::endl;
        if( !lems.empty() ){
          Trace("cegqi-engine") << "  *** Do measure refinement..." << std::endl;
          for( unsigned j=0; j<lems.size(); j++ ){
            Trace("cegqi-lemma") << "Cegqi::Lemma : measure : " << lems[j] << std::endl;
            d_quantEngine->addLemma( lems[j] );
          }
          Trace("cegqi-engine") << "  ...refine size." << std::endl;
          return;
        }
      }
      
      Trace("cegqi-engine") << "  *** Check candidate phase..." << std::endl;
      std::vector< Node > cclems;
      conj->doCegConjectureCheck( cclems, model_values );
      bool addedLemma = false;
      for( unsigned i=0; i<cclems.size(); i++ ){
        Node lem = cclems[i];
        d_last_inst_si = false;
        //eagerly unfold applications of evaluation function
        if( options::sygusDirectEval() ){
          Trace("cegqi-eager") << "pre-unfold counterexample : " << lem << std::endl;
          std::map< Node, Node > visited_n;
          lem = getEagerUnfold( lem, visited_n );
        }
        Trace("cegqi-lemma") << "Cegqi::Lemma : counterexample : " << lem << std::endl;
        if( d_quantEngine->addLemma( lem ) ){
          ++(d_statistics.d_cegqi_lemmas_ce);
          addedLemma = true;
        }else{
          //this may happen if we eagerly unfold, simplify to true
          if( !options::sygusDirectEval() ){
            Trace("cegqi-warn") << "  ...FAILED to add candidate!" << std::endl;
          }else{
            Trace("cegqi-engine-debug") << "  ...FAILED to add candidate!" << std::endl;
          }
        }
      }
      if( addedLemma ){
        Trace("cegqi-engine") << "  ...check for counterexample." << std::endl;
      }else{
        if( conj->needsRefinement() ){
          //immediately go to refine candidate
          checkCegConjecture( conj );
          return;
        }
      } 
    }else{
      Assert( aq==q );
      std::vector< Node > model_terms;
      std::vector< Node > clist;
      conj->getCandidateList( clist, true );
      Assert( clist.size()==q[0].getNumChildren() );
      conj->getModelValues( clist, model_terms );
      if( d_quantEngine->addInstantiation( q, model_terms ) ){
        conj->recordInstantiation( model_terms );
      }else{
        Assert( false );
      }
    }
  }else{
    Trace("cegqi-engine") << "  *** Refine candidate phase..." << std::endl;
    std::vector< Node > rlems;
    conj->doCegConjectureRefine( rlems );
    bool addedLemma = false;
    for( unsigned i=0; i<rlems.size(); i++ ){
      Node lem = rlems[i];
      Trace("cegqi-lemma") << "Cegqi::Lemma : candidate refinement : " << lem << std::endl;
      bool res = d_quantEngine->addLemma( lem );
      if( res ){
        ++(d_statistics.d_cegqi_lemmas_refine);
        conj->d_refine_count++;
        addedLemma = true;
      }else{
        Trace("cegqi-warn") << "  ...FAILED to add refinement!" << std::endl;
      }
    }
    if( addedLemma ){
      Trace("cegqi-engine") << "  ...refine candidate." << std::endl;
    }
  }
}

void CegInstantiation::getCRefEvaluationLemmas( CegConjecture * conj, std::vector< Node >& vs, std::vector< Node >& ms, std::vector< Node >& lems ) {
  if( conj->getNumRefinementLemmas()>0 ){
    Assert( vs.size()==ms.size() );
    std::map< Node, Node > vtm;
    for( unsigned i=0; i<vs.size(); i++ ){
      vtm[vs[i]] = ms[i];
    }
    /*
    if( options::sygusUnifCondSol() ){
      // first, check progress lemmas  TODO?
      for( unsigned i=0; i<conj->getNumRefinementLemmas(); i++ ){
        Node plem = conj->getConditionalProgressLemma( i );
        std::vector< Node > pp;
        conj->
        std::map< Node, Node > visitedp;
        std::map< Node, std::vector< Node > > expp;
        conj->getModelValues
      }
    }
    */
    for( unsigned i=0; i<conj->getNumRefinementLemmas(); i++ ){
      Node lem;
      std::map< Node, Node > visited;
      std::map< Node, std::vector< Node > > exp;
      if( options::sygusUnifCondSol() ){
        for( unsigned j=0; j<conj->getNumConditionalEvaluations( i ); j++ ){
          std::map< Node, Node > visitedc;
          std::map< Node, std::vector< Node > > expc;
          Node ce = conj->getConditionalEvaluationAntec( i, j );
          Node cee = crefEvaluate( ce, vtm, visitedc, expc );
          Trace("sygus-cref-eval") << "Check conditional evaluation condition : " << ce << ", evaluates to " << cee << std::endl;
          if( !cee.isNull() && cee==d_quantEngine->getTermDatabase()->d_true  ){
            Node conc = conj->getConditionalEvaluationConc( i, j );
            // the conditional holds, we will apply this as a substitution
            for( unsigned r=0; r<2; r++ ){
              if( conc[r].isVar() ){
                Node v = conc[r];
                Node c = conc[1-r];
                Assert( exp.find( v )==exp.end() );
                visited[v] = c;
                //exp[v].insert( exp[v].end(), expc[ce].begin(), expc[ce].end() );
                exp[v].push_back( ce );
                Trace("sygus-cref-eval") << "   consider " << v << " -> " << c << " with expanation " << ce << std::endl;
                break;
              }
            }
          }
        }
        //if at least one conditional fires
        if( !visited.empty() ){
          lem = conj->getRefinementBaseLemma( i );
        }
      }else{
        lem = conj->getRefinementBaseLemma( i );
      }
      if( !lem.isNull() ){
        Trace("sygus-cref-eval") << "Check refinement lemma " << lem << " against current model." << std::endl;
        Node elem = crefEvaluate( lem, vtm, visited, exp );
        Trace("sygus-cref-eval") << "...evaluated to " << elem << ", exp size = " << exp[lem].size() << std::endl;
        if( !elem.isNull() && elem==d_quantEngine->getTermDatabase()->d_false ){
          elem = conj->getGuard().negate();
          Node cre_lem;
          if( !exp[lem].empty() ){
            Node en = exp[lem].size()==1 ? exp[lem][0] : NodeManager::currentNM()->mkNode( kind::AND, exp[lem] );
            cre_lem = NodeManager::currentNM()->mkNode( kind::OR, en.negate(), elem );
          }else{
            cre_lem = elem;
          }
          if( std::find( lems.begin(), lems.end(), cre_lem )==lems.end() ){
            Trace("sygus-cref-eval") << "...produced lemma : " << cre_lem << std::endl;
            lems.push_back( cre_lem );
          }
        }
      }
    }
  }
}

Node CegInstantiation::crefEvaluate( Node n, std::map< Node, Node >& vtm, std::map< Node, Node >& visited, std::map< Node, std::vector< Node > >& exp ){
  std::map< Node, Node >::iterator itv = visited.find( n );
  Node ret;
  std::vector< Node > exp_c;
  if( itv!=visited.end() ){
    if( !itv->second.isConst() ){
      //we stored a partially evaluated node, actually evaluate the result now
      ret = crefEvaluate( itv->second, vtm, visited, exp );
      exp_c.push_back( itv->second );
    }else{
      return itv->second;
    }
  }else{
    if( n.getKind()==kind::APPLY_UF ){
      //it is an evaluation function
      Trace("sygus-cref-eval-debug") << "Compute evaluation for : " << n << std::endl;
      //unfold by one step 
      Node nn = d_quantEngine->getTermDatabaseSygus()->unfold( n, vtm, exp[n] );
      Trace("sygus-cref-eval-debug") << "...unfolded once to " << nn << std::endl;
      Assert( nn!=n );
      //it is the result of evaluating the unfolding
      ret = crefEvaluate( nn, vtm, visited, exp );
      //carry explanation
      exp_c.push_back( nn );
    }
    if( ret.isNull() ){
      if( n.getNumChildren()>0 ){
        std::vector< Node > children;
        bool childChanged = false;
        if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
          children.push_back( n.getOperator() );
        }
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          Node nc = crefEvaluate( n[i], vtm, visited, exp );
          childChanged = nc!=n[i] || childChanged;
          children.push_back( nc );
          //Boolean short circuiting
          if( n.getKind()==kind::AND ){
            if( nc==d_quantEngine->getTermDatabase()->d_false ){
              ret = nc;
              exp_c.clear();
            }
          }else if( n.getKind()==kind::OR ){
            if( nc==d_quantEngine->getTermDatabase()->d_true ){
              ret = nc;
              exp_c.clear();
            }
          }else if( n.getKind()==kind::ITE && i==0 ){
            int index = -1;
            if( nc==d_quantEngine->getTermDatabase()->d_true ){
              index = 1;
            }else if( nc==d_quantEngine->getTermDatabase()->d_false ){
              index = 2;
            }
            if( index!=-1 ){
              ret = crefEvaluate( n[index], vtm, visited, exp );
              exp_c.push_back( n[index] );
            }
          }
          //carry explanation
          exp_c.push_back( n[i] );
          if( !ret.isNull() ){
            break;
          }
        }
        if( ret.isNull() ){
          if( childChanged ){
            ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
            ret = Rewriter::rewrite( ret );
          }else{
            ret = n;
          }
        }
      }else{
        ret = n;
      }
    }
  }
  //carry explanation from children
  for( unsigned i=0; i<exp_c.size(); i++ ){
    Node nn = exp_c[i];
    std::map< Node, std::vector< Node > >::iterator itx = exp.find( nn );
    if( itx!=exp.end() ){
      for( unsigned j=0; j<itx->second.size(); j++ ){
        if( std::find( exp[n].begin(), exp[n].end(), itx->second[j] )==exp[n].end() ){
          exp[n].push_back( itx->second[j] );
        }
      }
    }
  }
  Trace("sygus-cref-eval-debug") << "... evaluation of " << n << " is (" << ret.getKind() << ") " << ret << std::endl;
  Trace("sygus-cref-eval-debug") << "...... exp size = " << exp[n].size() << std::endl;
  Assert( ret.isNull() || ret.isConst() );
  visited[n] = ret;
  return ret;
}

void CegInstantiation::registerMeasuredType( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_uf_measure.find( tn );
  if( it==d_uf_measure.end() ){
    if( tn.isDatatype() ){
      TypeNode op_tn = NodeManager::currentNM()->mkFunctionType( tn, NodeManager::currentNM()->integerType() );
      Node op = NodeManager::currentNM()->mkSkolem( "tsize", op_tn, "was created by ceg instantiation to enforce fairness." );
      d_uf_measure[tn] = op;
    }
  }
}

Node CegInstantiation::getSizeTerm( Node n, TypeNode tn, std::vector< Node >& lems ) {
  std::map< Node, Node >::iterator itt = d_size_term.find( n );
  if( itt==d_size_term.end() ){
    registerMeasuredType( tn );
    Node sn = NodeManager::currentNM()->mkNode( APPLY_UF, d_uf_measure[tn], n );
    lems.push_back( NodeManager::currentNM()->mkNode( LEQ, NodeManager::currentNM()->mkConst( Rational(0) ), sn ) );
    d_size_term[n] = sn;
    return sn;
  }else{
    return itt->second;
  }
}

void CegInstantiation::getMeasureLemmas( Node n, Node v, std::vector< Node >& lems ) {
  Trace("cegqi-lemma-debug") << "Get measure lemma " << n << " " << v << std::endl;
  Assert( n.getType()==v.getType() );
  TypeNode tn = n.getType();
  if( tn.isDatatype() ){
    Assert( v.getKind()==APPLY_CONSTRUCTOR );
    const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
    int index = Datatype::indexOf( v.getOperator().toExpr() );
    std::map< int, Node >::iterator it = d_size_term_lemma[n].find( index );
    if( it==d_size_term_lemma[n].end() ){
      Node lhs = getSizeTerm( n, tn, lems );
      //add measure lemma
      std::vector< Node > sumc;
      for( unsigned j=0; j<dt[index].getNumArgs(); j++ ){
        TypeNode tnc = v[j].getType();
        if( tnc.isDatatype() ){
          Node seln = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[index][j].getSelector() ), n );
          sumc.push_back( getSizeTerm( seln, tnc, lems ) );
        }
      }
      Node rhs;
      if( !sumc.empty() ){
        sumc.push_back( NodeManager::currentNM()->mkConst( Rational(1) ) );
        rhs = NodeManager::currentNM()->mkNode( PLUS, sumc );
      }else{
        rhs = NodeManager::currentNM()->mkConst( Rational(0) );
      }
      Node lem = lhs.eqNode( rhs );
      Node cond = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( dt[index].getTester() ), n );
      lem = NodeManager::currentNM()->mkNode( OR, cond.negate(), lem );

      d_size_term_lemma[n][index] = lem;
      Trace("cegqi-lemma-debug") << "...constructed lemma " << lem << std::endl;
      lems.push_back( lem );
      //return;
    }
    //get lemmas for children
    for( unsigned i=0; i<v.getNumChildren(); i++ ){
      Node nn = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[index][i].getSelector() ), n );
      getMeasureLemmas( nn, v[i], lems );
    }

  }
}

Node CegInstantiation::getEagerUnfold( Node n, std::map< Node, Node >& visited ) {
  std::map< Node, Node >::iterator itv = visited.find( n );
  if( itv==visited.end() ){
    Trace("cegqi-eager-debug") << "getEagerUnfold " << n << std::endl;
    Node ret;
    if( n.getKind()==APPLY_UF ){
      TypeNode tn = n[0].getType();
      Trace("cegqi-eager-debug") << "check " << n[0].getType() << std::endl;
      if( tn.isDatatype() ){
        const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
        if( dt.isSygus() ){ 
          Trace("cegqi-eager") << "Unfold eager : " << n << std::endl;
          Node bTerm = d_quantEngine->getTermDatabaseSygus()->sygusToBuiltin( n[0], tn );
          Trace("cegqi-eager") << "Built-in term : " << bTerm << std::endl;
          std::vector< Node > vars;
          std::vector< Node > subs;
          Node var_list = Node::fromExpr( dt.getSygusVarList() );
          Assert( var_list.getNumChildren()+1==n.getNumChildren() );
          for( unsigned j=0; j<var_list.getNumChildren(); j++ ){
            vars.push_back( var_list[j] );
          }
          for( unsigned j=1; j<n.getNumChildren(); j++ ){
            Node nc = getEagerUnfold( n[j], visited );
            subs.push_back( nc );
            Assert( subs[j-1].getType()==var_list[j-1].getType() );
          }
          Assert( vars.size()==subs.size() );
          bTerm = bTerm.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
          Trace("cegqi-eager") << "Built-in term after subs : " << bTerm << std::endl;
          Trace("cegqi-eager-debug") << "Types : " << bTerm.getType() << " " << n.getType() << std::endl;
          Assert( n.getType()==bTerm.getType() );
          ret = bTerm; 
        }
      }
    }
    if( ret.isNull() ){
      if( n.getKind()!=FORALL ){
        bool childChanged = false;
        std::vector< Node > children;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          Node nc = getEagerUnfold( n[i], visited );
          childChanged = childChanged || n[i]!=nc;
          children.push_back( nc );
        }
        if( childChanged ){
          if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
            children.insert( children.begin(), n.getOperator() );
          }
          ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
        }
      }
      if( ret.isNull() ){
        ret = n;
      }
    }
    visited[n] = ret;
    return ret;
  }else{
    return itv->second;
  }
}

void CegInstantiation::printSynthSolution( std::ostream& out ) {
  if( d_conj->isAssigned() ){
    Trace("cegqi-debug") << "Printing synth solution..." << std::endl;
    //if( !(Trace.isOn("cegqi-stats")) ){
    //  out << "Solution:" << std::endl;
    //}
    for( unsigned i=0; i<d_conj->d_quant[0].getNumChildren(); i++ ){
      Node prog = d_conj->d_quant[0][i];
      Trace("cegqi-debug") << "  print solution for " << prog << std::endl;
      std::stringstream ss;
      ss << prog;
      std::string f(ss.str());
      f.erase(f.begin());
      TypeNode tn = prog.getType();
      Assert( tn.isDatatype() );
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      Assert( dt.isSygus() );
      //get the solution
      Node sol;
      int status = -1;
      if( d_last_inst_si ){
        Assert( d_conj->getCegConjectureSingleInv() != NULL );
        sol = d_conj->getSingleInvocationSolution( i, tn, status );
        sol = sol.getKind()==LAMBDA ? sol[1] : sol;
      }else{
        Node cprog = d_conj->getCandidate( i );
        if( !d_conj->d_cinfo[cprog].d_inst.empty() ){
          sol = d_conj->d_cinfo[cprog].d_inst.back();
          // Check if this was based on a template, if so, we must do
          // Reconstruction
          if( d_conj->d_assert_quant!=d_conj->d_quant ){
            Node sygus_sol = sol;
            Trace("cegqi-inv") << "Sygus version of solution is : " << sol
                               << ", type : " << sol.getType() << std::endl;
            std::vector< Node > subs;
            Expr svl = dt.getSygusVarList();
            for( unsigned j=0; j<svl.getNumChildren(); j++ ){
              subs.push_back( Node::fromExpr( svl[j] ) );
            }
            bool templIsPost = false;
            Node templ;
            if( options::sygusInvTemplMode() == SYGUS_INV_TEMPL_MODE_PRE ){
              const CegConjectureSingleInv* ceg_si = d_conj->getCegConjectureSingleInv();
              if(ceg_si->d_trans_pre.find( prog ) != ceg_si->d_trans_pre.end()){
                templ = ceg_si->getTransPre(prog);
                templIsPost = false;
              }
            }else if(options::sygusInvTemplMode() == SYGUS_INV_TEMPL_MODE_POST){
              const CegConjectureSingleInv* ceg_si = d_conj->getCegConjectureSingleInv();
              if(ceg_si->d_trans_post.find(prog) != ceg_si->d_trans_post.end()){
                templ = ceg_si->getTransPost(prog);
                templIsPost = true;
              }
            }
            Trace("cegqi-inv") << "Template is " << templ << std::endl;
            if( !templ.isNull() ){
              std::vector<Node>& templ_vars = d_conj->getProgTempVars(prog);
              std::vector< Node > vars;
              vars.insert( vars.end(), templ_vars.begin(), templ_vars.end() );
              Node vl = Node::fromExpr( dt.getSygusVarList() );
              Assert(vars.size() == subs.size());
              if( Trace.isOn("cegqi-inv-debug") ){
                for( unsigned j=0; j<vars.size(); j++ ){
                  Trace("cegqi-inv-debug") << "  subs : " << vars[j] << " -> " << subs[j] << std::endl;
                }
              }
              //apply the substitution to the template
              templ = templ.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
              TermDbSygus* sygusDb = getTermDatabase()->getTermDatabaseSygus();
              sol = sygusDb->sygusToBuiltin( sol, sol.getType() );
              Trace("cegqi-inv") << "Builtin version of solution is : "
                                 << sol << ", type : " << sol.getType()
                                 << std::endl;
              sol = NodeManager::currentNM()->mkNode( templIsPost ? AND : OR, sol, templ );
            }
            if( sol==sygus_sol ){
              sol = sygus_sol;
              status = 1;
            }else{
              Trace("cegqi-inv-debug") << "With template : " << sol << std::endl;
              sol = Rewriter::rewrite( sol );
              Trace("cegqi-inv-debug") << "Simplified : " << sol << std::endl;
              sol = d_conj->reconstructToSyntaxSingleInvocation(sol, tn, status);
              sol = sol.getKind()==LAMBDA ? sol[1] : sol;
            }
          }else{
            status = 1;
          }
        }else{
          Trace("cegqi-warn") << "WARNING : No recorded instantiations for syntax-guided solution!" << std::endl;
        }
      }
      if( !(Trace.isOn("cegqi-stats")) ){
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
          if( sol.isNull() ){
            out << "?";
          }else{
            std::vector< Node > lvs;
            TermDbSygus::printSygusTerm( out, sol, lvs );
          }
        }
        out << ")" << std::endl;
      }
    }
  }else{
    Assert( false );
  }
}

void CegInstantiation::collectDisjuncts( Node n, std::vector< Node >& d ) {
  if( n.getKind()==OR ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      collectDisjuncts( n[i], d );
    }
  }else{
    d.push_back( n );
  }
}

void CegInstantiation::preregisterAssertion( Node n ) {
  //check if it sygus conjecture
  if( TermDb::isSygusConjecture( n ) ){
    //this is a sygus conjecture
    Trace("cegqi") << "Preregister sygus conjecture : " << n << std::endl;
    d_conj->preregisterConjecture( n );
  }
}

CegInstantiation::Statistics::Statistics():
  d_cegqi_lemmas_ce("CegInstantiation::cegqi_lemmas_ce", 0),
  d_cegqi_lemmas_refine("CegInstantiation::cegqi_lemmas_refine", 0),
  d_cegqi_si_lemmas("CegInstantiation::cegqi_lemmas_si", 0)
{
  smtStatisticsRegistry()->registerStat(&d_cegqi_lemmas_ce);
  smtStatisticsRegistry()->registerStat(&d_cegqi_lemmas_refine);
  smtStatisticsRegistry()->registerStat(&d_cegqi_si_lemmas);
}

CegInstantiation::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_lemmas_ce);
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_lemmas_refine);
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_si_lemmas);
}

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */
