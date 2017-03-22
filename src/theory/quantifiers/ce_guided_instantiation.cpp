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
  d_incomplete_candidate_values = false;
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
    if( options::cegqiUnifCondSol() ){
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
  if( tn.isDatatype() ){
    const Datatype& dt = ((DatatypeType)tn.toType()).getDatatype();
    if( dt.isSygus() ){
      type_valid = true;
      for( unsigned j=0; j<dt.getNumConstructors(); j++ ){
        Node op = Node::fromExpr( dt[j].getSygusOp() );
        if( op.getKind() == kind::BUILTIN ){
          Kind sk = NodeManager::operatorToKind( op );
          if( sk==kind::ITE ){
            // we can do unification
            d_cinfo[v].d_csol_op = Node::fromExpr( dt[j].getConstructor() );
            Trace("cegqi") << "Can do synthesis unification for variable " << v << ", based on operator " << d_cinfo[v].d_csol_op << std::endl;
            Assert( dt[j].getNumArgs()==3 );
            for( unsigned k=0; k<3; k++ ){
              Type t = dt[j][k].getRangeType();
              if( k==0 ){
                d_cinfo[v].d_csol_cond = NodeManager::currentNM()->mkSkolem( "c", TypeNode::fromType( t ) );
              }else{
                d_cinfo[v].d_csol_var[k-1] = NodeManager::currentNM()->mkSkolem( "e", TypeNode::fromType( t ) );
              }
            }
            break;
          }
        }
      }
    }
  }
  //mark active
  if( d_cinfo[v].d_csol_cond.isNull() ){
    d_cinfo[v].d_csol_status = 0;
  }
  if( !type_valid ){
    Assert( false );
  }
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
  return !d_ce_sk.empty() || d_incomplete_candidate_values;
}

void CegConjecture::getConditionalCandidateList( std::vector< Node >& clist, Node curr, bool reqAdd ){
  Assert( options::cegqiUnifCondSol() );
  std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( curr );
  if( it!=d_cinfo.end() ){
    if( !it->second.d_csol_cond.isNull() ){
      if( it->second.d_csol_status!=-1 ){
        Assert( it->second.d_csol_status==0 || it->second.d_csol_status==1 );
        //interested in model value for condition and branched variables
        clist.push_back( it->second.d_csol_cond );
        //assume_flat_ITEs
        clist.push_back( it->second.d_csol_var[it->second.d_csol_status] );
        //conditionally get the other branch
        getConditionalCandidateList( clist, it->second.d_csol_var[1-it->second.d_csol_status], false );
        return;
      }else{
        //otherwise, yet to explore branch
        if( !reqAdd ){
          // if we are not top-level, we can ignore this (it won't be part of solution)
          return;
        }
      }
    }else{
      // a standard variable not handlable by unification
    }
    clist.push_back( curr );
  }
}

void CegConjecture::getCandidateList( std::vector< Node >& clist, bool forceOrig ) {
  if( options::cegqiUnifCondSol() && !forceOrig ){
    for( unsigned i=0; i<d_candidates.size(); i++ ){
      getConditionalCandidateList( clist, d_candidates[i], true );
    }
  }else{
    clist.insert( clist.end(), d_candidates.begin(), d_candidates.end() );
  }
}

Node CegConjecture::constructConditionalCandidate( std::map< Node, Node >& cmv, Node curr ) {
  Assert( options::cegqiUnifCondSol() );
  std::map< Node, Node >::iterator itc = cmv.find( curr );
  if( itc!=cmv.end() ){
    return itc->second;
  }else{
    std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( curr );
    if( it!=d_cinfo.end() ){
      if( !it->second.d_csol_cond.isNull() ){
        if( it->second.d_csol_status!=-1 ){
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
  return Node::null();
}

bool CegConjecture::constructCandidates( std::vector< Node >& clist, std::vector< Node >& model_values, std::vector< Node >& candidate_values ) {
  Assert( clist.size()==model_values.size() );
  if( options::cegqiUnifCondSol() ){
    std::map< Node, Node > cmv;
    for( unsigned i=0; i<clist.size(); i++ ){
      cmv[ clist[i] ] = model_values[i];
    }
    for( unsigned i=0; i<d_candidates.size(); i++ ){
      Node n = constructConditionalCandidate( cmv, d_candidates[i] );
      Trace("cegqi-candidate") << "...constructed conditional candidate " << n << " for " << d_candidates[i] << std::endl;
      candidate_values.push_back( n );
      if( n.isNull() ){
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
    d_incomplete_candidate_values = false;
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
    if( options::cegqiUnifCondSol() ){
      //TODO
      hasActiveConditionalNode = true;
    }
    //check whether we will run CEGIS on inner skolem variables
    bool sk_refine = ( !isGround() || d_refine_count==0 || hasActiveConditionalNode );
    if( sk_refine ){
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
    d_incomplete_candidate_values = true;
    Assert( false );
  }
}

Node CegConjecture::getActiveConditional( Node curr ) {
  Assert( options::cegqiUnifCondSol() );
  std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( curr );
  Assert( it!=d_cinfo.end() );
  if( !it->second.d_csol_cond.isNull() ){
    if( it->second.d_csol_status==-1 ){
      //yet to branch, this is the one
      return curr;
    }else{
      Assert( it->second.d_csol_status==0 || it->second.d_csol_status==1 );
      return getActiveConditional( it->second.d_csol_var[1-it->second.d_csol_status] );
    }
  }else{
    //not a conditional
    return curr;
  }
}

void CegConjecture::getContextConditionals( Node curr, Node x, std::vector< Node >& conds, std::vector< Node >& rets, std::map< Node, bool >& cpols ) {
  if( curr!=x ){
    std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( curr );
    if( !it->second.d_csol_cond.isNull() ){
      if( it->second.d_csol_status!=-1 ){
        conds.push_back( it->second.d_csol_cond );
        rets.push_back( it->second.d_csol_var[it->second.d_csol_status] );
        cpols[it->second.d_csol_cond] = ( it->second.d_csol_status==1  );
        getContextConditionals( it->second.d_csol_var[1-it->second.d_csol_status], x, conds, rets, cpols );
      }
    }
  }
}

Node CegConjecture::mkConditional( Node c, std::vector< Node >& args, bool pol ) {
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
  Node ret = NodeManager::currentNM()->mkNode( kind::APPLY_UF, condc );
  if( !pol ){
    ret = ret.negate();
  }
  return ret;
}
  
  
Node CegConjecture::purifyConditionalEvaluations( Node n, std::map< Node, Node >& csol_cond, std::map< Node, Node >& psubs, std::map< Node, Node >& visited ){
  std::map< Node, Node >::iterator itv = visited.find( n );
  if( itv!=visited.end() ){
    return itv->second;
  }else{
    Node ret;
    if( n.getKind()==APPLY_UF ){
      std::map< Node, Node >::iterator itc = csol_cond.find( n[0] );
      if( itc!=csol_cond.end() ){
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
          Node nc = purifyConditionalEvaluations( n[i], csol_cond, psubs, visited );
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
  std::map< Node, Node > csol_cond;
  std::map< Node, std::vector< Node > > csol_ccond;
  std::map< Node, std::vector< Node > > csol_ccond_ret;
  std::map< Node, std::map< Node, bool > > csol_cpol;
  std::vector< Node > csol_vals;
  if( options::cegqiUnifCondSol() ){
    std::vector< Node > new_active_measure_sum;
    Trace("cegqi-unif") << "Conditional solution refinement, expand active conditional nodes" << std::endl;
    for( unsigned i=0; i<d_candidates.size(); i++ ){
      Node v = d_candidates[i];
      Node ac = getActiveConditional( v );
      Assert( !ac.isNull() );
      //compute the contextual conditions
      getContextConditionals( v, ac, csol_ccond[v], csol_ccond_ret[v], csol_cpol[v] );
      if( !csol_ccond[v].empty() ){
        //it will be conditionally evaluated, this is a placeholder
        csol_cond[v] = Node::null();
      }
      //if it is a conditional
      if( !d_cinfo[ac].d_csol_cond.isNull() ){
        //activate
        Trace("cegqi-unif") << "****** For " << v << ", expanding an active conditional node : " << ac << std::endl;
        d_cinfo[ac].d_csol_status = 0;  //TODO
        Trace("cegqi-unif") << "...expanded to " << d_cinfo[ac].d_csol_op << "( ";
        Trace("cegqi-unif") << d_cinfo[ac].d_csol_cond << ", " << d_cinfo[ac].d_csol_var[0] << ", ";
        Trace("cegqi-unif") << d_cinfo[ac].d_csol_var[1] << " )" << std::endl;
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
        csol_cond[v] = d_cinfo[ac].d_csol_cond;
        csol_vals.push_back( d_cinfo[ac].d_csol_var[d_cinfo[ac].d_csol_status] );
      }else{
        Trace("cegqi-unif") << "* For " << v << ", its active node " << ac << " is not a conditional node." << std::endl;
        //if we have not already included this in the measure, do so
        if( d_cinfo[ac].d_csol_status==0 ){
          Node acf = getMeasureTermFactor( ac );
          if( !acf.isNull() ){
            new_active_measure_sum.push_back( acf );
          }
          d_cinfo[ac].d_csol_status = 1;
        }
        csol_vals.push_back( ac );
      }
      if( !csol_ccond[v].empty() ){
        Trace("cegqi-unif") << "...it is nested under " << csol_ccond[v].size() << " other conditionals" << std::endl;
      }
    }
    // must add to active measure
    if( !new_active_measure_sum.empty() ){
      Node new_active_measure = NodeManager::currentNM()->mkSkolem( "K", NodeManager::currentNM()->integerType() );
      new_active_measure_sum.push_back( new_active_measure );
      Node namlem = NodeManager::currentNM()->mkNode( kind::GEQ, new_active_measure, NodeManager::currentNM()->mkConst(Rational(0)));
      Node ramlem = d_active_measure_term.eqNode( NodeManager::currentNM()->mkNode( kind::PLUS, new_active_measure_sum ) );
      namlem = NodeManager::currentNM()->mkNode( kind::AND, ramlem, namlem );
      Trace("cegqi-lemma") << "Cegqi::Lemma : Measure expansion : " << namlem << std::endl;
      d_qe->getOutputChannel().lemma( namlem );
      d_active_measure_term = new_active_measure;
    }
  }
  Trace("cegqi-refine") << "Refine " << d_ce_sk.size() << " points." << std::endl;
  //for conditional evaluation
  std::map< Node, Node > psubs_visited;
  std::map< Node, Node > psubs;
  //skolem substitution
  std::vector< Node > sk_vars;
  std::vector< Node > sk_subs;
  for( unsigned j=0; j<d_ce_sk.size(); j++ ){
    bool success = true;
    std::vector< Node > lem_c;
    Assert( d_ce_sk[j].size()==d_base_disj.size() );
    std::vector< Node > inst_cond_c;
    for( unsigned k=0; k<d_ce_sk[j].size(); k++ ){
      Node ce_q = d_ce_sk[j][k];
      Trace("cegqi-refine") << "  For counterexample point " << j << ", disjunct " << k << " : " << ce_q << " " << d_base_disj[k] << std::endl;
      Node c_disj;
      if( !ce_q.isNull() ){
        Assert( d_base_disj[k].getKind()==kind::NOT && d_base_disj[k][0].getKind()==kind::FORALL );
        c_disj = d_base_disj[k][0][1];
      }else{
        if( d_inner_vars_disj[k].empty() ){
          c_disj = d_base_disj[k].negate();
        }else{
          //denegrate case : quantified disjunct was trivially true and does not need to be refined
          Trace("cegqi-refine") << "*** skip " << d_base_disj[k] << std::endl;
          //add trivial substitution (in case we need substitution for previous cex's)
          for( unsigned i=0; i<d_inner_vars_disj[k].size(); i++ ){
            sk_vars.push_back( d_inner_vars_disj[k][i] );
            sk_subs.push_back( getModelValue( d_inner_vars_disj[k][i] ) ); // will return dummy value
          }
        }
      }
      //compute the body, inst_cond
      if( options::cegqiUnifCondSol() && !c_disj.isNull() ){
        Trace("cegqi-unif") << "Process " << c_disj << std::endl;
        c_disj = purifyConditionalEvaluations( c_disj, csol_cond, psubs, psubs_visited );
        Trace("cegqi-unif") << "Purified to : " << c_disj << std::endl;
        Trace("cegqi-unif") << "...now with " << psubs.size() << " definitions." << std::endl;
      }else{
        //standard CEGIS refinement : plug in values, assert that d_candidates must satisfy entire specification
      }
      //collect the substitution over all disjuncts
      if( !ce_q.isNull() ){
        Assert( !d_inner_vars_disj[k].empty() );
        Assert( d_inner_vars_disj[k].size()==d_qe->getTermDatabase()->d_skolem_constants[ce_q].size() );
        std::vector< Node > model_values;
        if( getModelValues( d_qe->getTermDatabase()->d_skolem_constants[ce_q], model_values ) ){
          sk_vars.insert( sk_vars.end(), d_inner_vars_disj[k].begin(), d_inner_vars_disj[k].end() );
          sk_subs.insert( sk_subs.end(), model_values.begin(), model_values.end() );
        }else{
          success = false;
          break;
        }
      }
      //add to the lemma
      if( !c_disj.isNull() ){
        lem_c.push_back( c_disj );
      }
    }
    if( success ){
      Trace("cegqi-unif") << "Add conditional assumptions for " << psubs.size() << " evaluations." << std::endl;
      //add conditional correctness assumptions
      std::map< Node, Node > psubs_condc;
      std::map< Node, std::vector< Node > > psubs_apply;
      std::vector< Node > paux_vars;
      for( std::map< Node, Node >::iterator itp = psubs.begin(); itp != psubs.end(); ++itp ){
        Assert( csol_cond.find( itp->first[0] )!=csol_cond.end() );
        paux_vars.push_back( itp->second );
        std::vector< Node > args;
        for( unsigned a=1; a<itp->first.getNumChildren(); a++ ){
          args.push_back( itp->first[a] );
        }
        Node c = csol_cond[itp->first[0]];
        psubs_apply[ c ].push_back( itp->first );
        Trace("cegqi-unif") << "   process assumption " << itp->first << " == " << itp->second << ", with current condition " << c;
        Trace("cegqi-unif") << ", and " << csol_ccond[itp->first[0]].size() << " context conditionals." << std::endl;
        std::vector< Node> assm;
        if( !c.isNull() ){
          assm.push_back( mkConditional( c, args ) );
        }
        for( unsigned j=0; j<csol_ccond[itp->first[0]].size(); j++ ){
          Node cc = csol_ccond[itp->first[0]][j];
          assm.push_back( mkConditional( cc, args, csol_cpol[itp->first[0]][cc] ) );
        }
        Assert( !assm.empty() );
        Node condn = assm.size()==1 ? assm[0] : NodeManager::currentNM()->mkNode( kind::AND, assm );
        Node cond = NodeManager::currentNM()->mkNode( kind::IMPLIES, condn, itp->first.eqNode( itp->second ) );
        psubs_condc[itp->first] = cond;
        Trace("cegqi-unif") << "   ...made conditional correctness assumption : " << cond << std::endl;
      }
      for( std::map< Node, Node >::iterator itp = psubs_condc.begin(); itp != psubs_condc.end(); ++itp ){
        lem_c.push_back( itp->second );
      }
      
      Node lem = lem_c.size()==1 ? lem_c[0] : NodeManager::currentNM()->mkNode( AND, lem_c );
      //substitute the actual return values
      if( options::cegqiUnifCondSol() ){
        Assert( d_candidates.size()==csol_vals.size() );
        lem = lem.substitute( d_candidates.begin(), d_candidates.end(), csol_vals.begin(), csol_vals.end() );
      }
      
      //previous non-ground conditional refinement lemmas must satisfy the current point
      for( unsigned i=0; i<d_refinement_lemmas.size(); i++ ){
        Node prev_lem = d_refinement_lemmas[i];
        prev_lem = prev_lem.substitute( sk_vars.begin(), sk_vars.end(), sk_subs.begin(), sk_subs.end() );
        //do auxiliary variable substitution
        std::vector< Node > subs;
        for( unsigned ii=0; ii<d_refinement_lemmas_aux_vars[i].size(); ii++ ){
          subs.push_back( NodeManager::currentNM()->mkSkolem( "y", d_refinement_lemmas_aux_vars[i][ii].getType(), 
                                                              "purification variable for non-ground sygus conditional solution" ) );
        }
        prev_lem = prev_lem.substitute( d_refinement_lemmas_aux_vars[i].begin(), d_refinement_lemmas_aux_vars[i].end(), subs.begin(), subs.end() );
        prev_lem = Rewriter::rewrite( prev_lem );
        prev_lem = NodeManager::currentNM()->mkNode( OR, getGuard().negate(), prev_lem );
        Trace("cegqi-unif") << "...previous conditional refinement lemma with new counterexample : " << prev_lem << std::endl;
        lems.push_back( prev_lem );
      }
      if( !isGround() && !csol_cond.empty() ){
        Trace("cegqi-unif") << "Lemma " << lem << " is a non-ground conditional refinement lemma, store it for future instantiation." << std::endl;
        d_refinement_lemmas.push_back( lem );
        d_refinement_lemmas_aux_vars.push_back( paux_vars );
      }
      
      if( options::cegqiUnifCondSol() ){
        Trace("cegqi-unif") << "We have lemma : " << lem << std::endl;
        Trace("cegqi-unif") << "Now add progress assertions..." << std::endl;
        std::vector< Node > prgr_conj;
        std::map< Node, bool > cprocessed;
        for( std::map< Node, Node >::iterator itc = csol_cond.begin(); itc !=csol_cond.end(); ++itc ){
          Node x = itc->first;
          Node c = itc->second;          
          if( !c.isNull() ){
            Trace("cegqi-unif") << "  process conditional " << c << " for " << x << ", which was applied " << psubs_apply[c].size() << " times." << std::endl;
            //make the progress point
            Assert( x.getType().isDatatype() );
            const Datatype& dx = ((DatatypeType)x.getType().toType()).getDatatype();
            Node sbvl = Node::fromExpr( dx.getSygusVarList() );
            std::vector< Node > prgr_pt;
            for( unsigned a=0; a<sbvl.getNumChildren(); a++ ){
              prgr_pt.push_back( NodeManager::currentNM()->mkSkolem( "kp", sbvl[a].getType(), "progress point for sygus conditional" ) );
            }
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
                Node pdlem = prgr_domain_d.size()==1 ? prgr_domain_d[0] : NodeManager::currentNM()->mkNode( OR, prgr_domain_d );
                prgr_conj.push_back( pdlem );
              }
            }
            //the condition holds for the point
            prgr_conj.push_back( mkConditional( c, prgr_pt ) );
            // ...and not for its context, if this return point is different from them
            //for( unsigned j=0; j<csol_ccond[x].size(); j++ ){
            //  Node cc = csol_ccond[x][j];
            //  prgr_conj.push_back( mkConditional( cc, prgr_pt, csol_cpol[x][cc] ) );
            //}
            //FIXME
          }
        }
        if( !prgr_conj.empty() ){
          Node prgr_lem = prgr_conj.size()==1 ? prgr_conj[0] : NodeManager::currentNM()->mkNode( kind::AND, prgr_conj );
          prgr_lem = prgr_lem.substitute( d_candidates.begin(), d_candidates.end(), csol_vals.begin(), csol_vals.end() );
          Trace("cegqi-unif") << "Progress lemma is " << prgr_lem << std::endl;
          lem = NodeManager::currentNM()->mkNode( kind::AND, lem, prgr_lem );
        }
        //make in terms of new values
        Assert( csol_vals.size()==d_candidates.size() );
        Trace("cegqi-unif") << "Now rewrite in terms of new evaluation branches...got " << lem << std::endl;
      }
      //apply the substitution
      Assert( sk_vars.size()==sk_subs.size() );
      lem = lem.substitute( sk_vars.begin(), sk_vars.end(), sk_subs.begin(), sk_subs.end() );
      lem = NodeManager::currentNM()->mkNode( OR, getGuard().negate(), lem );
      lem = Rewriter::rewrite( lem );
      lems.push_back( lem );
    }
  }
  d_ce_sk.clear();
  d_incomplete_candidate_values = false;
}

void CegConjecture::preregisterConjecture( Node q ) {
  d_ceg_si->preregisterConjecture( q );
}

bool CegConjecture::getModelValues( std::vector< Node >& n, std::vector< Node >& v ) {
  bool success = true;
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
    if( nv.isNull() ){
      Trace("cegqi-warn") << "WARNING: failed getModelValues." << std::endl;
      success = false;
    }
  }
  Trace("cegqi-engine") << std::endl;
  return success;
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
            if( ptn.isBoolean() || ptn.isBitVector() ){
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
        if( options::cegqiUnifCondSol() || 
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
      if( conj->getModelValues( clist, model_values ) ){
        if( options::sygusDirectEval() ){
          Trace("cegqi-debug") << "Do direct evaluation..." << std::endl;
          std::vector< Node > eager_eval_lem;
          for( unsigned j=0; j<clist.size(); j++ ){
          Trace("cegqi-debug") << "  register " << clist[j] << " -> " << model_values[j] << std::endl;
            d_quantEngine->getTermDatabaseSygus()->registerModelValue( clist[j], model_values[j], eager_eval_lem );
          }
          Trace("cegqi-debug") << "...produced " << eager_eval_lem.size()  << " eager evaluation lemmas." << std::endl;
          if( !eager_eval_lem.empty() ){
            Trace("cegqi-engine") << "  *** Do direct evaluation..." << std::endl;
            for( unsigned j=0; j<eager_eval_lem.size(); j++ ){
              Node lem = eager_eval_lem[j];
              if( d_quantEngine->getTheoryEngine()->isTheoryEnabled(THEORY_BV) ){
                //FIXME: hack to incorporate hacks from BV for division by zero
                lem = bv::TheoryBVRewriter::eliminateBVSDiv( lem );
              }
              Trace("cegqi-lemma") << "Cegqi::Lemma : evaluation : " << lem << std::endl;
              d_quantEngine->addLemma( lem );
            }
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
      }
    }else{
      Assert( aq==q );
      std::vector< Node > model_terms;
      std::vector< Node > clist;
      conj->getCandidateList( clist, true );
      Assert( clist.size()==q[0].getNumChildren() );
      if( conj->getModelValues( clist, model_terms ) ){
        conj->recordInstantiation( model_terms );
        d_quantEngine->addInstantiation( q, model_terms );
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
            if( !templ.isNull() ){
              std::vector<Node>& templ_vars = d_conj->getProgTempVars(prog);
              
              //take into consideration Boolean term conversion (this step can be eliminated when boolean term conversion is eliminated)
              std::vector< Node > vars;
              vars.insert( vars.end(), templ_vars.begin(), templ_vars.end() );
              Node vl = Node::fromExpr( dt.getSygusVarList() );
              Assert(vars.size() == subs.size());
              for( unsigned j=0; j<templ_vars.size(); j++ ){
                if( vl[j].getType().isBoolean() ){
                  Node c = NodeManager::currentNM()->mkConst(BitVector(1u, 1u));
                  vars[j] = vars[j].eqNode( c );
                }
                Assert( vars[j].getType()==subs[j].getType() );
              }
              
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
