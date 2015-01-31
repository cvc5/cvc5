/*********************                                                        */
/*! \file ce_guided_instantiation.cpp
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
 **
 **/

#include "theory/quantifiers/ce_guided_instantiation.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "util/datatype.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace std;

namespace CVC4 {

void CegInstantiation::collectDisjuncts( Node n, std::vector< Node >& d ) {
  if( n.getKind()==OR ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      collectDisjuncts( n[i], d );
    }
  }else{
    d.push_back( n );
  }
}

CegInstantiation::CegConjecture::CegConjecture( context::Context* c ) : d_active( c, false ), d_infeasible( c, false ), d_curr_lit( c, 0 ){
  d_refine_count = 0;
}

void CegInstantiation::CegConjecture::assign( QuantifiersEngine * qe, Node q ) {
  Assert( d_quant.isNull() );
  Assert( q.getKind()==FORALL );
  d_quant = q;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    d_candidates.push_back( NodeManager::currentNM()->mkSkolem( "e", q[0][i].getType() ) );
  }
  //construct base instantiation
  d_base_inst = Rewriter::rewrite( qe->getInstantiation( q, d_candidates ) );
  Trace("cegqi") << "Base instantiation is : " << d_base_inst << std::endl;
  if( qe->getTermDatabase()->isQAttrSygus( q ) ){
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
    if( options::sygusSingleInv() ){
      analyzeSygusConjecture();
    }
  }else if( qe->getTermDatabase()->isQAttrSynthesis( q ) ){
    d_syntax_guided = false;
  }else{
    Assert( false );
  }
}



void CegInstantiation::CegConjecture::analyzeSygusConjecture() {
  Node q = d_quant;
  // conj -> conj*
  std::map< Node, std::vector< Node > > children;
  // conj X prog -> inv*
  std::map< Node, std::map< Node, std::vector< Node > > > prog_invoke;
  std::vector< Node > progs;
  std::map< Node, std::map< Node, bool > > contains;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    progs.push_back( q[0][i] );
  }
  //collect information about conjunctions
  if( analyzeSygusConjunct( Node::null(), q[1], children, prog_invoke, progs, contains, true ) ){
    //try to phrase as single invocation property
    bool singleInvocation = true;
    Trace("cegqi-analyze") << "...success." << std::endl;
    std::map< Node, std::vector< Node > > invocations;
    std::map< Node, std::map< int, std::vector< Node > > > single_invoke_args;
    std::map< Node, std::map< int, std::map< Node, std::vector< Node > > > > single_invoke_args_from;
    for( std::map< Node, std::vector< Node > >::iterator it = children.begin(); it != children.end(); ++it ){
      for( unsigned j=0; j<it->second.size(); j++ ){
        Node conj = it->second[j];
        Trace("cegqi-analyze-debug") << "Process child " << conj << " from " << it->first << std::endl;
        std::map< Node, std::map< Node, std::vector< Node > > >::iterator itp = prog_invoke.find( conj );
        if( itp!=prog_invoke.end() ){
          for( std::map< Node, std::vector< Node > >::iterator it2 = itp->second.begin(); it2 != itp->second.end(); ++it2 ){
            if( it2->second.size()>1 ){
              singleInvocation = false;
              break;
            }else if( it2->second.size()==1 ){
              Node prog = it2->first;
              Node inv = it2->second[0];
              Assert( inv[0]==prog );
              invocations[prog].push_back( inv );
              for( unsigned k=1; k<inv.getNumChildren(); k++ ){
                Node arg = inv[k];
                Trace("cegqi-analyze-debug") << "process : " << arg << " occurs in position " << k-1 << " in invocation " << inv << " of " << prog << " in " << conj << std::endl;
                single_invoke_args_from[prog][k-1][arg].push_back( conj );
                if( std::find( single_invoke_args[prog][k-1].begin(), single_invoke_args[prog][k-1].end(), arg )==single_invoke_args[prog][k-1].end() ){
                  single_invoke_args[prog][k-1].push_back( arg );
                }
              }
            }
          }
        }
      }
    }
    if( singleInvocation ){
      Trace("cegqi-analyze") << "Property is single invocation with : " << std::endl;
      std::vector< Node > pbvs;
      std::vector< Node > new_vars;
      std::map< Node, std::vector< Node > > new_assumptions;
      for( std::map< Node, std::vector< Node > >::iterator it = invocations.begin(); it != invocations.end(); ++it ){
        Assert( !it->second.empty() );
        Node prog = it->first;
        Node inv = it->second[0];
        std::vector< Node > invc;
        invc.push_back( inv.getOperator() );
        invc.push_back( prog );
        Node pv = NodeManager::currentNM()->mkBoundVar( "F", inv.getType() );
        d_single_inv_map[prog] = pv;
        d_single_inv_map_to_prog[pv] = prog;
        pbvs.push_back( pv );
        Trace("cegqi-analyze-debug2") << "Make variable " << pv << " for " << prog << std::endl;
        for( unsigned k=1; k<inv.getNumChildren(); k++ ){
          Assert( !single_invoke_args[prog][k-1].empty() );
          if( single_invoke_args[prog][k-1].size()==1 ){
            invc.push_back( single_invoke_args[prog][k-1][0] );
          }else{
            //introduce fresh variable, assign all
            Node v = NodeManager::currentNM()->mkSkolem( "a", single_invoke_args[prog][k-1][0].getType(), "single invocation arg" );
            new_vars.push_back( v );
            invc.push_back( v );

            for( unsigned i=0; i<single_invoke_args[prog][k-1].size(); i++ ){
              Node arg = single_invoke_args[prog][k-1][i];
              Node asum = NodeManager::currentNM()->mkNode( arg.getType().isBoolean() ? IFF : EQUAL, v, arg ).negate();
              Trace("cegqi-analyze-debug") << "  ..." << arg << " occurs in ";
              Trace("cegqi-analyze-debug") << single_invoke_args_from[prog][k-1][arg].size() << " invocations at position " << (k-1) << " of " << prog << "." << std::endl;
              for( unsigned j=0; j<single_invoke_args_from[prog][k-1][arg].size(); j++ ){
                Node conj = single_invoke_args_from[prog][k-1][arg][j];
                Trace("cegqi-analyze-debug") << "  ..." << arg << " occurs in invocation " << inv << " of " << prog << " in " << conj << std::endl;
                Trace("cegqi-analyze-debug") << "  ...add assumption " << asum << " to " << conj << std::endl;
                if( std::find( new_assumptions[conj].begin(), new_assumptions[conj].end(), asum )==new_assumptions[conj].end() ){
                  new_assumptions[conj].push_back( asum );
                }
              }
            }
          }
        }
        Node sinv = NodeManager::currentNM()->mkNode( APPLY_UF, invc );
        Trace("cegqi-analyze") << "  " << prog << " -> " << sinv << std::endl;
        d_single_inv_app_map[prog] = sinv;
      }
      //construct the single invocation version of the property
      Trace("cegqi-analyze") << "Single invocation formula conjuncts are : " << std::endl;
      //std::vector< Node > si_conj;
      Assert( !pbvs.empty() );
      Node pbvl = NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, pbvs );
      for( std::map< Node, std::vector< Node > >::iterator it = children.begin(); it != children.end(); ++it ){
        //should hold since we prevent miniscoping
        Assert( d_single_inv.isNull() );
        std::vector< Node > tmp;
        for( unsigned i=0; i<it->second.size(); i++ ){
          Node c = it->second[i];
          std::vector< Node > disj;
          //insert new assumptions
          disj.insert( disj.end(), new_assumptions[c].begin(), new_assumptions[c].end() );
          //get replaced version
          Node cr;
          std::map< Node, std::map< Node, std::vector< Node > > >::iterator itp = prog_invoke.find( c );
          if( itp!=prog_invoke.end() ){
            std::vector< Node > terms;
            std::vector< Node > subs;
            for( std::map< Node, std::vector< Node > >::iterator it2 = itp->second.begin(); it2 != itp->second.end(); ++it2 ){
              if( !it2->second.empty() ){
                Node prog = it2->first;
                Node inv = it2->second[0];
                Assert( it2->second.size()==1 );
                terms.push_back( inv );
                subs.push_back( d_single_inv_map[prog] );
                Trace("cegqi-analyze-debug2") << "subs : " << inv << " -> var for " << prog << " : " << d_single_inv_map[prog] << std::endl;
              }
            }
            cr = c.substitute( terms.begin(), terms.end(), subs.begin(), subs.end() );
          }else{
            cr = c;
          }
          if( cr.getKind()==OR ){
            for( unsigned j=0; j<cr.getNumChildren(); j++ ){
              disj.push_back( cr[j] );
            }
          }else{
            disj.push_back( cr );
          }
          Node curr = disj.size()==1 ? disj[0] : NodeManager::currentNM()->mkNode( OR, disj );
          Trace("cegqi-analyze") << "    " << curr;
          tmp.push_back( curr.negate() );
          if( !it->first.isNull() ){
            Trace("cegqi-analyze-debug") << " under " << it->first;
          }
          Trace("cegqi-analyze") << std::endl;
        }
        Assert( !tmp.empty() );
        Node bd = tmp.size()==1 ? tmp[0] : NodeManager::currentNM()->mkNode( OR, tmp );
        if( !it->first.isNull() ){
          // apply substitution for skolem variables
          std::vector< Node > vars;
          d_single_inv_arg_sk.clear();
          for( unsigned j=0; j<it->first.getNumChildren(); j++ ){
            std::stringstream ss;
            ss << "k_" << it->first[j];
            Node v = NodeManager::currentNM()->mkSkolem( ss.str(), it->first[j].getType(), "single invocation skolem" );
            vars.push_back( it->first[j] );
            d_single_inv_arg_sk.push_back( v );
          }
          bd = bd.substitute( vars.begin(), vars.end(), d_single_inv_arg_sk.begin(), d_single_inv_arg_sk.end() );

          Trace("cegqi-analyze-debug") << "    -> " << bd << std::endl;
        }
        d_single_inv = NodeManager::currentNM()->mkNode( FORALL, pbvl, bd );
        //equality resolution
        for( unsigned j=0; j<tmp.size(); j++ ){
          Node conj = tmp[j];
          std::map< Node, std::vector< Node > > case_vals;
          bool exh = processSingleInvLiteral( conj, false, case_vals );
          Trace("cegqi-analyze-er") << "Conjunct " << conj << " gives equality restrictions, exh = " << exh << " : " << std::endl;
          for( std::map< Node, std::vector< Node > >::iterator it = case_vals.begin(); it != case_vals.end(); ++it ){
            Trace("cegqi-analyze-er") << "  " << it->first << " -> ";
            for( unsigned k=0; k<it->second.size(); k++ ){
              Trace("cegqi-analyze-er") << it->second[k] << " ";
            }
            Trace("cegqi-analyze-er") << std::endl;
          }

        }
      }
      Trace("cegqi-analyze-debug") << "...formula is : " << d_single_inv << std::endl;
    }else{
      Trace("cegqi-analyze") << "Property is not single invocation." << std::endl;
    }
  }
}

bool CegInstantiation::CegConjecture::processSingleInvLiteral( Node lit, bool pol, std::map< Node, std::vector< Node > >& case_vals ) {
  if( lit.getKind()==NOT ){
    return processSingleInvLiteral( lit[0], !pol, case_vals );
  }else if( ( lit.getKind()==OR && pol ) || ( lit.getKind()==AND && !pol ) ){
    bool exh = true;
    for( unsigned k=0; k<lit.getNumChildren(); k++ ){
      bool curr = processSingleInvLiteral( lit[k], pol, case_vals );
      exh = exh && curr;
    }
    return exh;
  }else if( lit.getKind()==IFF || lit.getKind()==EQUAL ){
    if( pol ){
      for( unsigned r=0; r<2; r++ ){
        std::map< Node, Node >::iterator it = d_single_inv_map_to_prog.find( lit[r] );
        if( it!=d_single_inv_map_to_prog.end() ){
          if( r==1 || d_single_inv_map_to_prog.find( lit[1] )==d_single_inv_map_to_prog.end() ){
            case_vals[it->second].push_back( lit[ r==0 ? 1 : 0 ] );
            return true;
          }
        }
      }
    }
  }
  return false;
}

bool CegInstantiation::CegConjecture::analyzeSygusConjunct( Node p, Node n, std::map< Node, std::vector< Node > >& children,
                                                            std::map< Node, std::map< Node, std::vector< Node > > >& prog_invoke,
                                                            std::vector< Node >& progs, std::map< Node, std::map< Node, bool > >& contains, bool pol ) {
  if( ( pol && n.getKind()==OR ) || ( !pol && n.getKind()==AND ) ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( !analyzeSygusConjunct( p, n[i], children, prog_invoke, progs, contains, pol ) ){
        return false;
      }
    }
  }else if( pol && n.getKind()==NOT && n[0].getKind()==FORALL ){
    if( !p.isNull() ){
      //do not allow nested quantifiers
      return false;
    }
    analyzeSygusConjunct( n[0][0], n[0][1], children, prog_invoke, progs, contains, false );
  }else{
    if( pol ){
      n = n.negate();
    }
    Trace("cegqi-analyze") << "Sygus conjunct : " << n << std::endl;
    children[p].push_back( n );
    for( unsigned i=0; i<progs.size(); i++ ){
      prog_invoke[n][progs[i]].clear();
    }
    bool success = analyzeSygusTerm( n, prog_invoke[n], contains[n] );
    for( unsigned i=0; i<progs.size(); i++ ){
      std::map< Node, std::vector< Node > >::iterator it = prog_invoke[n].find( progs[i] );
      Trace("cegqi-analyze") << "  Program " << progs[i] << " is invoked " << it->second.size() << " times " << std::endl;
      for( unsigned j=0; j<it->second.size(); j++ ){
        Trace("cegqi-analyze") << "    " << it->second[j] << std::endl;
      }
    }
    return success;
  }
  return true;
}

bool CegInstantiation::CegConjecture::analyzeSygusTerm( Node n, std::map< Node, std::vector< Node > >& prog_invoke, std::map< Node, bool >& contains ) {
  if( n.getNumChildren()>0 ){
    if( n.getKind()==FORALL ){
      //do not allow nested quantifiers
      return false;
    }
    //look at first argument in evaluator
    Node p = n[0];
    std::map< Node, std::vector< Node > >::iterator it = prog_invoke.find( p );
    if( it!=prog_invoke.end() ){
      if( std::find( it->second.begin(), it->second.end(), n )==it->second.end() ){
        it->second.push_back( n );
      }
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( !analyzeSygusTerm( n[i], prog_invoke, contains ) ){
        return false;
      }
    }
  }else{
    //record this conjunct contains n
    contains[n] = true;
  }
  return true;
}

void CegInstantiation::CegConjecture::initializeGuard( QuantifiersEngine * qe ){
  if( d_guard.isNull() ){
    d_guard = Rewriter::rewrite( NodeManager::currentNM()->mkSkolem( "G", NodeManager::currentNM()->booleanType() ) );
    //specify guard behavior
    d_guard = qe->getValuation().ensureLiteral( d_guard );
    AlwaysAssert( !d_guard.isNull() );
    qe->getOutputChannel().requirePhase( d_guard, true );
    if( !d_syntax_guided ){
      //add immediate lemma
      Node lem = NodeManager::currentNM()->mkNode( OR, d_guard.negate(), d_base_inst.negate() );
      Trace("cegqi") << "Add candidate lemma : " << lem << std::endl;
      qe->getOutputChannel().lemma( lem );
    }else if( !d_single_inv.isNull() ){
      Assert( d_single_inv.getKind()==FORALL );
      std::vector< Node > vars;
      d_single_inv_sk.clear();
      for( unsigned i=0; i<d_single_inv[0].getNumChildren(); i++ ){
        std::stringstream ss;
        ss << "k_" << d_single_inv[0][i];
        Node k = NodeManager::currentNM()->mkSkolem( ss.str(), d_single_inv[0][i].getType(), "single invocation function skolem" );
        vars.push_back( d_single_inv[0][i] );
        d_single_inv_sk.push_back( k );
      }
      Node inst = d_single_inv[1].substitute( vars.begin(), vars.end(), d_single_inv_sk.begin(), d_single_inv_sk.end() );
      Node lem = NodeManager::currentNM()->mkNode( OR, d_guard.negate(), inst.negate() );
      Trace("cegqi") << "Add single invocation lemma : " << lem << std::endl;
      qe->getOutputChannel().lemma( lem );
      if( Trace.isOn("cegqi-debug") ){
        lem = Rewriter::rewrite( lem );
        Trace("cegqi-debug") << "...rewritten : " << lem << std::endl;
      }
    }
  }
}

Node CegInstantiation::CegConjecture::getLiteral( QuantifiersEngine * qe, int i ) {
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
      Trace("cegqi-lemma") << "Fairness split : " << lem << std::endl;
      qe->getOutputChannel().lemma( lem );
      qe->getOutputChannel().requirePhase( lit, true );

      if( options::ceGuidedInstFair()==CEGQI_FAIR_DT_HEIGHT_PRED ){
        //implies height bounds on each candidate variable
        std::vector< Node > lem_c;
        for( unsigned j=0; j<d_candidates.size(); j++ ){
          lem_c.push_back( NodeManager::currentNM()->mkNode( DT_HEIGHT_BOUND, d_candidates[j], c ) );
        }
        Node hlem = NodeManager::currentNM()->mkNode( OR, lit.negate(), lem_c.size()==1 ? lem_c[0] : NodeManager::currentNM()->mkNode( AND, lem_c ) );
        Trace("cegqi-lemma") << "Fairness expansion (dt-height-pred) : " << hlem << std::endl;
        qe->getOutputChannel().lemma( hlem );
      }
      return lit;
    }else{
      return it->second;
    }
  }
}

CegInstantiation::CegInstantiation( QuantifiersEngine * qe, context::Context* c ) : QuantifiersModule( qe ){
  d_conj = new CegConjecture( d_quantEngine->getSatContext() );
}

bool CegInstantiation::needsCheck( Theory::Effort e ) {
  return e>=Theory::EFFORT_LAST_CALL;
}

bool CegInstantiation::needsModel( Theory::Effort e ) {
  return true;
}
bool CegInstantiation::needsFullModel( Theory::Effort e ) {
  return true;
}

void CegInstantiation::check( Theory::Effort e, unsigned quant_e ) {
  if( quant_e==QuantifiersEngine::QEFFORT_MODEL ){
    Trace("cegqi-engine") << "---Counterexample Guided Instantiation Engine---" << std::endl;
    Trace("cegqi-engine-debug") << std::endl;
    Trace("cegqi-engine-debug") << "Current conjecture status : active : " << d_conj->d_active << " feasible : " << !d_conj->d_infeasible << std::endl;
    if( d_conj->d_active && !d_conj->d_infeasible ){
      checkCegConjecture( d_conj );
    }
    Trace("cegqi-engine") << "Finished Counterexample Guided Instantiation engine." << std::endl;
  }
}

void CegInstantiation::registerQuantifier( Node q ) {
  if( d_quantEngine->getOwner( q )==this ){
    if( !d_conj->isAssigned() ){
      Trace("cegqi") << "Register conjecture : " << q << std::endl;
      d_conj->assign( d_quantEngine, q );

      //fairness
      if( options::ceGuidedInstFair()!=CEGQI_FAIR_NONE ){
        std::vector< Node > mc;
        for( unsigned j=0; j<d_conj->d_candidates.size(); j++ ){
          TypeNode tn = d_conj->d_candidates[j].getType();
          if( options::ceGuidedInstFair()==CEGQI_FAIR_DT_SIZE ){
            if( tn.isDatatype() ){
              mc.push_back( NodeManager::currentNM()->mkNode( DT_SIZE, d_conj->d_candidates[j] ) );
            }
          }else if( options::ceGuidedInstFair()==CEGQI_FAIR_UF_DT_SIZE ){
            registerMeasuredType( tn );
            std::map< TypeNode, Node >::iterator it = d_uf_measure.find( tn );
            if( it!=d_uf_measure.end() ){
              mc.push_back( NodeManager::currentNM()->mkNode( APPLY_UF, it->second, d_conj->d_candidates[j] ) );
            }
          }else if( options::ceGuidedInstFair()==CEGQI_FAIR_DT_HEIGHT_PRED ){
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
  }
}

void CegInstantiation::assertNode( Node n ) {
  Trace("cegqi-debug") << "Cegqi : Assert : " << n << std::endl;
  bool pol = n.getKind()!=NOT;
  Node lit = n.getKind()==NOT ? n[0] : n;
  if( lit==d_conj->d_guard ){
    //d_guard_assertions[lit] = pol;
    d_conj->d_infeasible = !pol;
  }
  if( lit==d_conj->d_quant ){
    d_conj->d_active = true;
  }
}

Node CegInstantiation::getNextDecisionRequest() {
  d_conj->initializeGuard( d_quantEngine );
  bool value;
  if( !d_quantEngine->getValuation().hasSatValue( d_conj->d_guard, value ) ) {
    if( d_conj->d_guard_split.isNull() ){
      Node lem = NodeManager::currentNM()->mkNode( OR, d_conj->d_guard.negate(), d_conj->d_guard );
      d_quantEngine->getOutputChannel().lemma( lem );
    }
    Trace("cegqi-debug") << "CEGQI : Decide next on : " << d_conj->d_guard << "..." << std::endl;
    return d_conj->d_guard;
  }
  //enforce fairness
  if( d_conj->isAssigned() && options::ceGuidedInstFair()!=CEGQI_FAIR_NONE ){
    Node lit = d_conj->getLiteral( d_quantEngine, d_conj->d_curr_lit.get() );
    if( d_quantEngine->getValuation().hasSatValue( lit, value ) ) {
      if( !value ){
        d_conj->d_curr_lit.set( d_conj->d_curr_lit.get() + 1 );
        lit = d_conj->getLiteral( d_quantEngine, d_conj->d_curr_lit.get() );
        Trace("cegqi-debug") << "CEGQI : Decide on next lit : " << lit << "..." << std::endl;
        return lit;
      }
    }else{
      Trace("cegqi-debug") << "CEGQI : Decide on current lit : " << lit << "..." << std::endl;
      return lit;
    }
  }

  return Node::null();
}

void CegInstantiation::checkCegConjecture( CegConjecture * conj ) {
  Node q = conj->d_quant;
  Trace("cegqi-engine-debug") << "Synthesis conjecture : " << q << std::endl;
  Trace("cegqi-engine-debug") << "  * Candidate program/output symbol : ";
  for( unsigned i=0; i<conj->d_candidates.size(); i++ ){
    Trace("cegqi-engine-debug") << conj->d_candidates[i] << " ";
  }
  Trace("cegqi-engine-debug") << std::endl;
  if( options::ceGuidedInstFair()!=CEGQI_FAIR_NONE ){
    Trace("cegqi-engine") << "  * Current term size : " << conj->d_curr_lit.get() << std::endl;
  }

  if( conj->d_ce_sk.empty() ){
    Trace("cegqi-engine") << "  *** Check candidate phase..." << std::endl;
    if( getTermDatabase()->isQAttrSygus( q ) ){

      std::vector< Node > model_values;
      if( getModelValues( conj, conj->d_candidates, model_values ) ){
        //check if we must apply fairness lemmas
        std::vector< Node > lems;
        if( options::ceGuidedInstFair()==CEGQI_FAIR_UF_DT_SIZE ){
          for( unsigned j=0; j<conj->d_candidates.size(); j++ ){
            getMeasureLemmas( conj->d_candidates[j], model_values[j], lems );
          }
        }
        if( !lems.empty() ){
          for( unsigned j=0; j<lems.size(); j++ ){
            Trace("cegqi-lemma") << "Measure lemma : " << lems[j] << std::endl;
            d_quantEngine->addLemma( lems[j] );
          }
          Trace("cegqi-engine") << "  ...refine size." << std::endl;
        }else{
          //must get a counterexample to the value of the current candidate
          Node inst = conj->d_base_inst.substitute( conj->d_candidates.begin(), conj->d_candidates.end(), model_values.begin(), model_values.end() );
          //check whether we will run CEGIS on inner skolem variables
          bool sk_refine = ( !conj->isGround() || conj->d_refine_count==0 );
          if( sk_refine ){
            conj->d_ce_sk.push_back( std::vector< Node >() );
          }
          std::vector< Node > ic;
          ic.push_back( q.negate() );
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
          Trace("cegqi-lemma") << "Counterexample lemma : " << lem << std::endl;
          d_quantEngine->addLemma( lem );
          Trace("cegqi-engine") << "  ...find counterexample." << std::endl;
        }
      }

    }else if( getTermDatabase()->isQAttrSynthesis( q ) ){
      std::vector< Node > model_terms;
      if( getModelValues( conj, conj->d_candidates, model_terms ) ){
        d_quantEngine->addInstantiation( q, model_terms, false );
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
        lem = NodeManager::currentNM()->mkNode( OR, conj->d_guard.negate(), lem );
        lem = Rewriter::rewrite( lem );
        Trace("cegqi-lemma") << "Candidate refinement lemma : " << lem << std::endl;
        Trace("cegqi-engine") << "  ...refine candidate." << std::endl;
        d_quantEngine->addLemma( lem );
        conj->d_refine_count++;
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
      printSygusTerm( ss, nv );
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

void CegInstantiation::printSynthSolution( std::ostream& out ) {
  if( d_conj ){
    out << "Solution:" << std::endl;
    for( unsigned i=0; i<d_conj->d_candidates.size(); i++ ){
      std::stringstream ss;
      ss << d_conj->d_quant[0][i];
      std::string f(ss.str());
      f.erase(f.begin());
      out << "(define-fun f ";
      TypeNode tn = d_conj->d_quant[0][i].getType();
      Assert( datatypes::DatatypesRewriter::isTypeDatatype( tn ) );
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      Assert( dt.isSygus() );
      out << dt.getSygusVarList() << " ";
      out << dt.getSygusType() << " ";
      if( d_conj->d_candidate_inst[i].empty() ){
        out << "?";
      }else{
        printSygusTerm( out, d_conj->d_candidate_inst[i].back() );
      }
      out << ")" << std::endl;
    }
  }
}

void CegInstantiation::printSygusTerm( std::ostream& out, Node n ) {
  if( n.getKind()==APPLY_CONSTRUCTOR ){
    TypeNode tn = n.getType();
    const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
    if( dt.isSygus() ){
      int cIndex = Datatype::indexOf( n.getOperator().toExpr() );
      Assert( !dt[cIndex].getSygusOp().isNull() );
      if( n.getNumChildren()>0 ){
        out << "(";
      }
      out << dt[cIndex].getSygusOp();
      if( n.getNumChildren()>0 ){
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          out << " ";
          printSygusTerm( out, n[i] );
        }
        out << ")";
      }
      return;
    }
  }
  out << n;
}

}
