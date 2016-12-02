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
    : d_qe( qe ), d_curr_lit( c, 0 )
{
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
  }else if( d_qe->getTermDatabase()->isQAttrSynthesis( d_assert_quant ) ){
    d_syntax_guided = false;
  }else{
    Assert( false );
  }
}

void CegConjecture::initializeGuard( QuantifiersEngine * qe ){
  if( isAssigned() ){
    if( !d_syntax_guided ){
      if( d_nsg_guard.isNull() ){
        d_nsg_guard = Rewriter::rewrite( NodeManager::currentNM()->mkSkolem( "G", NodeManager::currentNM()->booleanType() ) );
        d_nsg_guard = qe->getValuation().ensureLiteral( d_nsg_guard );
        AlwaysAssert( !d_nsg_guard.isNull() );
        qe->getOutputChannel().requirePhase( d_nsg_guard, true );
        //add immediate lemma
        Node lem = NodeManager::currentNM()->mkNode( OR, d_nsg_guard.negate(), d_base_inst.negate() );
        Trace("cegqi-lemma") << "Cegqi::Lemma : non-syntax-guided : " << lem << std::endl;
        qe->getOutputChannel().lemma( lem );
      }
    }else if( d_ceg_si->d_si_guard.isNull() ){
      std::vector< Node > lems;
      d_ceg_si->getInitialSingleInvLemma( lems );
      for( unsigned i=0; i<lems.size(); i++ ){
        Trace("cegqi-lemma") << "Cegqi::Lemma : single invocation " << i << " : " << lems[i] << std::endl;
        qe->getOutputChannel().lemma( lems[i] );
        if( Trace.isOn("cegqi-debug") ){
          Node rlem = Rewriter::rewrite( lems[i] );
          Trace("cegqi-debug") << "...rewritten : " << rlem << std::endl;
        }
      }
    }
    Assert( !getGuard().isNull() );
  }
}

Node CegConjecture::getLiteral( QuantifiersEngine * qe, int i ) {
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
      qe->getOutputChannel().lemma( lem );
      qe->getOutputChannel().requirePhase( lit, true );

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
        qe->getOutputChannel().lemma( hlem );
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

void CegConjecture::preregisterConjecture( Node q ) {
  d_ceg_si->preregisterConjecture( q );
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
        for( unsigned j=0; j<d_conj->d_candidates.size(); j++ ){
          TypeNode tn = d_conj->d_candidates[j].getType();
          if( d_conj->getCegqiFairMode()==CEGQI_FAIR_DT_SIZE ){
            if( tn.isDatatype() ){
              mc.push_back( NodeManager::currentNM()->mkNode( DT_SIZE, d_conj->d_candidates[j] ) );
            }
          }else if( d_conj->getCegqiFairMode()==CEGQI_FAIR_UF_DT_SIZE ){
            registerMeasuredType( tn );
            std::map< TypeNode, Node >::iterator it = d_uf_measure.find( tn );
            if( it!=d_uf_measure.end() ){
              mc.push_back( NodeManager::currentNM()->mkNode( APPLY_UF, it->second, d_conj->d_candidates[j] ) );
            }
          }else if( d_conj->getCegqiFairMode()==CEGQI_FAIR_DT_HEIGHT_PRED || d_conj->getCegqiFairMode()==CEGQI_FAIR_DT_SIZE_PRED  ){
            //measure term is a fresh constant
            mc.push_back( NodeManager::currentNM()->mkSkolem( "K", NodeManager::currentNM()->integerType() ) );
          }
        }
        if( !mc.empty() ){
          d_conj->d_measure_term = mc.size()==1 ? mc[0] : NodeManager::currentNM()->mkNode( PLUS, mc );
          Trace("cegqi") << "Measure term is : " << d_conj->d_measure_term << std::endl;
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
    d_conj->initializeGuard( d_quantEngine );
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
      Node lit = d_conj->getLiteral( d_quantEngine, d_conj->d_curr_lit.get() );
      bool value;
      if( d_quantEngine->getValuation().hasSatValue( lit, value ) ) {
        if( !value ){
          d_conj->d_curr_lit.set( d_conj->d_curr_lit.get() + 1 );
          lit = d_conj->getLiteral( d_quantEngine, d_conj->d_curr_lit.get() );
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
  Trace("cegqi-engine-debug") << "Synthesis conjecture : " << q << std::endl;
  Trace("cegqi-engine-debug") << "  * Candidate program/output symbol : ";
  for( unsigned i=0; i<conj->d_candidates.size(); i++ ){
    Trace("cegqi-engine-debug") << conj->d_candidates[i] << " ";
  }
  Trace("cegqi-engine-debug") << std::endl;
  Trace("cegqi-engine-debug") << "  * Candidate ce skolems : ";
  for( unsigned i=0; i<conj->d_ce_sk.size(); i++ ){
    Trace("cegqi-engine-debug") << conj->d_ce_sk[i] << " ";
  }
  Trace("cegqi-engine-debug") << std::endl;
  if( conj->getCegqiFairMode()!=CEGQI_FAIR_NONE ){
    Trace("cegqi-engine") << "  * Current term size : " << conj->d_curr_lit.get() << std::endl;
  }

  if( conj->d_ce_sk.empty() ){
    Trace("cegqi-engine") << "  *** Check candidate phase..." << std::endl;
    if( conj->d_syntax_guided ){
      if( conj->getCegConjectureSingleInv() != NULL ){
        std::vector< Node > lems;
        if( conj->doCegConjectureCheck( lems ) ){
          if( !lems.empty() ){
            d_last_inst_si = true;
            for( unsigned j=0; j<lems.size(); j++ ){
              Trace("cegqi-lemma") << "Cegqi::Lemma : single invocation instantiation : " << lems[j] << std::endl;
              d_quantEngine->addLemma( lems[j] );
            }
            d_statistics.d_cegqi_si_lemmas += lems.size();
            Trace("cegqi-engine") << "  ...try single invocation." << std::endl;
          }
          return;
        }
      }
      std::vector< Node > model_values;
      if( getModelValues( conj, conj->d_candidates, model_values ) ){
        if( options::sygusDirectEval() ){
          std::vector< Node > eager_eval_lem;
          for( unsigned j=0; j<conj->d_candidates.size(); j++ ){
            d_quantEngine->getTermDatabaseSygus()->registerModelValue( conj->d_candidates[j], model_values[j], eager_eval_lem );
          }
          if( !eager_eval_lem.empty() ){
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
          std::vector< Node > lems;
          for( unsigned j=0; j<conj->d_candidates.size(); j++ ){
            getMeasureLemmas( conj->d_candidates[j], model_values[j], lems );
          }
          if( !lems.empty() ){
            for( unsigned j=0; j<lems.size(); j++ ){
              Trace("cegqi-lemma") << "Cegqi::Lemma : measure : " << lems[j] << std::endl;
              d_quantEngine->addLemma( lems[j] );
            }
            Trace("cegqi-engine") << "  ...refine size." << std::endl;
            return;
          }
        }
        //must get a counterexample to the value of the current candidate
        Assert( conj->d_candidates.size()==model_values.size() );
        Node inst = conj->d_base_inst.substitute( conj->d_candidates.begin(), conj->d_candidates.end(), model_values.begin(), model_values.end() );
        //check whether we will run CEGIS on inner skolem variables
        bool sk_refine = ( !conj->isGround() || conj->d_refine_count==0 );
        if( sk_refine ){
          conj->d_ce_sk.push_back( std::vector< Node >() );
        }
        std::vector< Node > ic;
        ic.push_back( aq.negate() );
        std::vector< Node > d;
        collectDisjuncts( inst, d );
        Assert( d.size()==conj->d_base_disj.size() );
        //immediately skolemize inner existentials
        for( unsigned i=0; i<d.size(); i++ ){
          Node dr = Rewriter::rewrite( d[i] );
          if( dr.getKind()==NOT && dr[0].getKind()==FORALL ){
            ic.push_back( getTermDatabase()->getSkolemizedBody( dr[0] ).negate() );
            if( sk_refine ){
              conj->d_ce_sk.back().push_back( dr[0] );
            }
          }else{
            ic.push_back( dr );
            if( sk_refine ){
              conj->d_ce_sk.back().push_back( Node::null() );
            }
            if( !conj->d_inner_vars_disj[i].empty() ){
              Trace("cegqi-debug") << "*** quantified disjunct : " << d[i] << " simplifies to " << dr << std::endl;
            }
          }
        }
        Node lem = NodeManager::currentNM()->mkNode( OR, ic );
        lem = Rewriter::rewrite( lem );
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
          Trace("cegqi-engine") << "  ...find counterexample." << std::endl;
        }else{
          //this may happen if we eagerly unfold, simplify to true
          if( !options::sygusDirectEval() ){
            Trace("cegqi-engine") << "  ...FAILED to add candidate!" << std::endl;
          }else{
            Trace("cegqi-engine-debug") << "  ...FAILED to add candidate!" << std::endl;
          }
          if( conj->d_refine_count==0  ){
            //immediately go to refine candidate
            checkCegConjecture( conj );
            return;
          }
        }
      }

    }else{
      Assert( aq==q );
      std::vector< Node > model_terms;
      if( getModelValues( conj, conj->d_candidates, model_terms ) ){
        d_quantEngine->addInstantiation( q, model_terms );
      }
    }
  }else{
    Trace("cegqi-engine") << "  *** Refine candidate phase..." << std::endl;
    for( unsigned j=0; j<conj->d_ce_sk.size(); j++ ){
      bool success = true;
      std::vector< Node > lem_c;
      Assert( conj->d_ce_sk[j].size()==conj->d_base_disj.size() );
      for( unsigned k=0; k<conj->d_ce_sk[j].size(); k++ ){
        Node ce_q = conj->d_ce_sk[j][k];
        Node c_disj = conj->d_base_disj[k];
        if( !ce_q.isNull() ){
          Assert( !conj->d_inner_vars_disj[k].empty() );
          Assert( conj->d_inner_vars_disj[k].size()==getTermDatabase()->d_skolem_constants[ce_q].size() );
          std::vector< Node > model_values;
          if( getModelValues( NULL, getTermDatabase()->d_skolem_constants[ce_q], model_values ) ){
            //candidate refinement : the next candidate must satisfy the counterexample found for the current model of the candidate
            Node inst_ce_refine = conj->d_base_disj[k][0][1].substitute( conj->d_inner_vars_disj[k].begin(), conj->d_inner_vars_disj[k].end(),
                                                                         model_values.begin(), model_values.end() );
            lem_c.push_back( inst_ce_refine );
          }else{
            success = false;
            break;
          }
        }else{
          if( conj->d_inner_vars_disj[k].empty() ){
            lem_c.push_back( conj->d_base_disj[k].negate() );
          }else{
            //denegrate case : quantified disjunct was trivially true and does not need to be refined
            Trace("cegqi-debug") << "*** skip " << conj->d_base_disj[k] << std::endl;
          }
        }
      }
      if( success ){
        Node lem = lem_c.size()==1 ? lem_c[0] : NodeManager::currentNM()->mkNode( AND, lem_c );
        lem = NodeManager::currentNM()->mkNode( OR, conj->getGuard().negate(), lem );
        lem = Rewriter::rewrite( lem );
        Trace("cegqi-lemma") << "Cegqi::Lemma : candidate refinement : " << lem << std::endl;
        Trace("cegqi-engine") << "  ...refine candidate." << std::endl;
        bool res = d_quantEngine->addLemma( lem );
        if( res ){
          ++(d_statistics.d_cegqi_lemmas_refine);
          conj->d_refine_count++;
        }else{
          Trace("cegqi-engine") << "  ...FAILED to add refinement!" << std::endl;
        }
      }
    }
    conj->d_ce_sk.clear();
  }
}

bool CegInstantiation::getModelValues( CegConjecture * conj, std::vector< Node >& n, std::vector< Node >& v ) {
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
      success = false;
    }
    if( conj ){
      conj->d_candidate_inst[i].push_back( nv );
    }
  }
  Trace("cegqi-engine") << std::endl;
  return success;
}

Node CegInstantiation::getModelValue( Node n ) {
  Trace("cegqi-mv") << "getModelValue for : " << n << std::endl;
  return d_quantEngine->getModel()->getValue( n );
}

Node CegInstantiation::getModelTerm( Node n ){
  //TODO
  return getModelValue( n );
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
            if( var_list[j-1].getType().isBoolean() ){   
              //TODO: remove this case when boolean term conversion is eliminated
              Node c = NodeManager::currentNM()->mkConst(BitVector(1u, 1u));
              subs.push_back( nc.eqNode( c ) );
            }else{
              subs.push_back( nc );
            }
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
        if( !d_conj->d_candidate_inst[i].empty() ){
          sol = d_conj->d_candidate_inst[i].back();
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
