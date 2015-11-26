/*********************                                                        */
/*! \file ce_guided_single_inv.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief utility for processing single invocation synthesis conjectures
 **
 **/

#include "theory/quantifiers/ce_guided_single_inv.h"
#include "theory/quantifiers/ce_guided_instantiation.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "util/datatype.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/trigger.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace std;

namespace CVC4 {

bool CegqiOutputSingleInv::addInstantiation( std::vector< Node >& subs ) {
  return d_out->addInstantiation( subs );
}

bool CegqiOutputSingleInv::isEligibleForInstantiation( Node n ) {
  return d_out->isEligibleForInstantiation( n );
}

bool CegqiOutputSingleInv::addLemma( Node n ) {
  return d_out->addLemma( n );
}


CegConjectureSingleInv::CegConjectureSingleInv( QuantifiersEngine * qe, CegConjecture * p ) : d_qe( qe ), d_parent( p ){
  d_has_ites = true;
  if( options::incrementalSolving() ){
    d_c_inst_match_trie = new inst::CDInstMatchTrie( qe->getUserContext() );
  }else{
    d_c_inst_match_trie = NULL;
  }
  CegqiOutputSingleInv * cosi = new CegqiOutputSingleInv( this );
  //  third and fourth arguments set to (false,false) until we have solution reconstruction for delta and infinity
  d_cinst = new CegInstantiator( qe, cosi, false, false );

  d_sol = new CegConjectureSingleInvSol( qe );
  
  d_sip = new SingleInvocationPartition;
}

void CegConjectureSingleInv::getSingleInvLemma( Node guard, std::vector< Node >& lems ) {
  if( !d_single_inv.isNull() ) {
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
    inst = TermDb::simpleNegate( inst );
    Trace("cegqi-si") << "Single invocation initial lemma : " << inst << std::endl;

    //register with the instantiator
    Node ginst = NodeManager::currentNM()->mkNode( OR, guard.negate(), inst );
    lems.push_back( ginst );
    d_cinst->registerCounterexampleLemma( lems, d_single_inv_sk );
  }
}

void CegConjectureSingleInv::initialize( Node q ) {
  Assert( d_quant.isNull() );
  //initialize data
  d_quant = q;
  //process
  Trace("cegqi-si") << "Initialize cegqi-si for " << q << std::endl;
  // conj -> conj*
  std::map< Node, std::vector< Node > > children;
  // conj X prog -> inv*
  std::map< Node, std::map< Node, std::vector< Node > > > prog_invoke;
  std::vector< Node > progs;
  std::map< Node, std::map< Node, bool > > contains;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    progs.push_back( q[0][i] );
    //check whether all types have ITE
    TypeNode tn = q[0][i].getType();
    d_qe->getTermDatabaseSygus()->registerSygusType( tn );
    if( !d_qe->getTermDatabaseSygus()->sygusToBuiltinType( tn ).isBoolean() ){
      if( !d_qe->getTermDatabaseSygus()->hasKind( tn, ITE ) ){
        d_has_ites = false;
      }
    }
  }
  Node qq = q[1];
  if( q[1].getKind()==NOT && q[1][0].getKind()==FORALL ){
    qq = q[1][0][1];
  }else{
    qq = TermDb::simpleNegate( qq );
  }
  //remove the deep embedding
  std::map< Node, Node > visited;
  std::vector< TypeNode > types;
  std::vector< Node > order_vars;
  int type_valid = 0;
  qq = removeDeepEmbedding( qq, progs, types, type_valid, visited );
  Trace("cegqi-si-debug") << "- Remove deep embedding, got : " << qq << ", type valid = " << type_valid << std::endl;
  bool singleInvocation = true;
  if( type_valid==0 ){
    //process the single invocation-ness of the property
    d_sip->init( types );
    d_sip->process( qq );
    Trace("cegqi-si") << "- Partitioned to single invocation parts : " << std::endl;
    d_sip->debugPrint( "cegqi-si" );
    //map from program to bound variables
    for( unsigned j=0; j<progs.size(); j++ ){
      Node prog = progs[j];
      std::map< Node, Node >::iterator it_nsi = d_nsi_op_map.find( prog );
      if( it_nsi!=d_nsi_op_map.end() ){
        Node op = it_nsi->second;
        std::map< Node, Node >::iterator it_fov = d_sip->d_func_fo_var.find( op );
        if( it_fov!=d_sip->d_func_fo_var.end() ){
          Node pv = it_fov->second;
          d_single_inv_map[prog] = pv;
          d_single_inv_map_to_prog[pv] = prog;
          Assert( d_sip->d_func_inv.find( op )!=d_sip->d_func_inv.end() );
          Node inv = d_sip->d_func_inv[op];
          d_single_inv_app_map[prog] = inv;
          Trace("cegqi-si") << "  " << pv << ", " << inv << " is associated with program " << prog << std::endl;
          d_prog_to_sol_index[prog] = order_vars.size();
          order_vars.push_back( pv );
        }
      }else{
        //does not mention the function
      }
    }
    //check if it is single invocation
    if( !d_sip->d_conjuncts[1].empty() ){
      singleInvocation = false;
      //if we are doing invariant templates, then construct the template
      if( options::sygusInvTemplMode() != SYGUS_INV_TEMPL_MODE_NONE ){
        std::map< Node, bool > has_inv;
        std::map< Node, std::vector< Node > > inv_pre_post[2];
        for( unsigned i=0; i<d_sip->d_conjuncts[2].size(); i++ ){
          std::vector< Node > disjuncts;
          Node func;
          int pol = -1;
          Trace("cegqi-si-inv") << "INV process " << d_sip->d_conjuncts[2][i] << std::endl;
          d_sip->extractInvariant( d_sip->d_conjuncts[2][i], func, pol, disjuncts );
          if( pol>=0 ){
            Assert( d_nsi_op_map_to_prog.find( func )!=d_nsi_op_map_to_prog.end() );
            Node prog = d_nsi_op_map_to_prog[func];
            Trace("cegqi-si-inv") << "..." << ( pol==0 ? "pre" : "post" ) << "-condition for " << prog << "." << std::endl;
            Node c = disjuncts.empty() ? d_qe->getTermDatabase()->d_false : ( disjuncts.size()==1 ? disjuncts[0] : NodeManager::currentNM()->mkNode( OR, disjuncts ) );
            c = pol==0 ? TermDb::simpleNegate( c ) : c;
            Trace("cegqi-si-inv-debug") << "...extracted : " << c << std::endl;
            inv_pre_post[pol][prog].push_back( c );
            has_inv[prog] = true;
          }else{
            Trace("cegqi-si-inv") << "...no status." << std::endl;
          }
        }

        Trace("cegqi-si-inv") << "Constructing invariant templates..." << std::endl;
        //now, contruct the template for the invariant(s)
        std::map< Node, Node > prog_templ;
        for( std::map< Node, bool >::iterator iti = has_inv.begin(); iti != has_inv.end(); ++iti ){
          Node prog = iti->first;
          Trace("cegqi-si-inv") << "...for " << prog << "..." << std::endl;
          Trace("cegqi-si-inv") << "   args : ";
          for( unsigned j=0; j<d_sip->d_si_vars.size(); j++ ){
            Node v = NodeManager::currentNM()->mkBoundVar( d_sip->d_si_vars[j].getType() );
            d_prog_templ_vars[prog].push_back( v );
            Trace("cegqi-si-inv") << v << " ";
          }
          Trace("cegqi-si-inv") << std::endl;
          Node pre = inv_pre_post[0][prog].empty() ? NodeManager::currentNM()->mkConst( false ) :
                      ( inv_pre_post[0][prog].size()==1 ? inv_pre_post[0][prog][0] : NodeManager::currentNM()->mkNode( OR, inv_pre_post[0][prog] ) );
          d_trans_pre[prog] = pre.substitute( d_sip->d_si_vars.begin(), d_sip->d_si_vars.end(), d_prog_templ_vars[prog].begin(), d_prog_templ_vars[prog].end() );
          Node post = inv_pre_post[1][prog].empty() ? NodeManager::currentNM()->mkConst( true ) :
                      ( inv_pre_post[1][prog].size()==1 ? inv_pre_post[1][prog][0] : NodeManager::currentNM()->mkNode( AND, inv_pre_post[1][prog] ) );
          d_trans_post[prog] = post.substitute( d_sip->d_si_vars.begin(), d_sip->d_si_vars.end(), d_prog_templ_vars[prog].begin(), d_prog_templ_vars[prog].end() );
          Trace("cegqi-si-inv") << "   precondition : " << d_trans_pre[prog] << std::endl;
          Trace("cegqi-si-inv") << "  postcondition : " << d_trans_post[prog] << std::endl;
          Node invariant = d_single_inv_app_map[prog];
          invariant = invariant.substitute( d_sip->d_si_vars.begin(), d_sip->d_si_vars.end(), d_prog_templ_vars[prog].begin(), d_prog_templ_vars[prog].end() );
          Trace("cegqi-si-inv") << "      invariant : " << invariant << std::endl;
          //construct template
          Node templ;
          if( options::sygusInvTemplMode() == SYGUS_INV_TEMPL_MODE_PRE ){
            //templ = NodeManager::currentNM()->mkNode( AND, NodeManager::currentNM()->mkNode( OR, d_trans_pre[prog], invariant ), d_trans_post[prog] );
            templ = NodeManager::currentNM()->mkNode( OR, d_trans_pre[prog], invariant );
          }else{
            Assert( options::sygusInvTemplMode() == SYGUS_INV_TEMPL_MODE_POST );
            //templ = NodeManager::currentNM()->mkNode( OR, d_trans_pre[prog], NodeManager::currentNM()->mkNode( AND, d_trans_post[prog], invariant ) );
            templ = NodeManager::currentNM()->mkNode( AND, d_trans_post[prog], invariant );
          }
          visited.clear();
          templ = addDeepEmbedding( templ, visited );
          Trace("cegqi-si-inv") << "       template : " << templ << std::endl;
          prog_templ[prog] = templ;
        }
        Node bd = d_sip->d_conjuncts[2].size()==1 ? d_sip->d_conjuncts[2][0] : NodeManager::currentNM()->mkNode( AND, d_sip->d_conjuncts[2] );
        visited.clear();
        bd = addDeepEmbedding( bd, visited );
        Trace("cegqi-si-inv") << "           body : " << bd << std::endl;
        bd = substituteInvariantTemplates( bd, prog_templ, d_prog_templ_vars );
        Trace("cegqi-si-inv-debug") << "     templ-subs body : " << bd << std::endl;
        //make inner existential
        std::vector< Node > new_var_bv;
        for( unsigned j=0; j<d_sip->d_si_vars.size(); j++ ){
          new_var_bv.push_back( NodeManager::currentNM()->mkBoundVar( d_sip->d_si_vars[j].getType() ) );
        }
        bd = bd.substitute( d_sip->d_si_vars.begin(), d_sip->d_si_vars.end(), new_var_bv.begin(), new_var_bv.end() );
        Assert( q[1].getKind()==NOT && q[1][0].getKind()==FORALL );
        for( unsigned j=0; j<q[1][0][0].getNumChildren(); j++ ){
          new_var_bv.push_back( q[1][0][0][j] );
        }
        if( !new_var_bv.empty() ){
          Node bvl = NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, new_var_bv );
          bd = NodeManager::currentNM()->mkNode( FORALL, bvl, bd ).negate();
        }
        //make outer universal
        bd = NodeManager::currentNM()->mkNode( FORALL, q[0], bd );
        bd = Rewriter::rewrite( bd );
        Trace("cegqi-si-inv") << "  rtempl-subs body : " << bd << std::endl;
        d_quant = bd;
      }
    }else{
      //we are fully single invocation
    }
  }else{
    Trace("cegqi-si") << "...property is not single invocation, involves functions with different argument sorts." << std::endl;
    singleInvocation = false;
  }
  if( options::cegqiSingleInvPartial() ){
    //TODO: set up outer loop
  }
  if( singleInvocation ){
    d_single_inv = d_sip->getSingleInvocation();
    d_single_inv = TermDb::simpleNegate( d_single_inv );
    if( !order_vars.empty() ){
      Node pbvl = NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, order_vars );
      d_single_inv = NodeManager::currentNM()->mkNode( FORALL, pbvl, d_single_inv );
    }
    //now, introduce the skolems
    for( unsigned i=0; i<d_sip->d_si_vars.size(); i++ ){
      Node v = NodeManager::currentNM()->mkSkolem( "a", d_sip->d_si_vars[i].getType(), "single invocation arg" );
      d_single_inv_arg_sk.push_back( v );
    }
    d_single_inv = d_single_inv.substitute( d_sip->d_si_vars.begin(), d_sip->d_si_vars.end(), d_single_inv_arg_sk.begin(), d_single_inv_arg_sk.end() );
    Trace("cegqi-si") << "Single invocation formula is : " << d_single_inv << std::endl;
    if( options::cbqiPreRegInst() && d_single_inv.getKind()==FORALL ){
      //just invoke the presolve now
      d_cinst->presolve( d_single_inv );
    }
  }else{
    Trace("cegqi-si") << "Formula is not single invocation." << std::endl;
    if( options::cegqiSingleInvAbort() ){
      Notice() << "Property is not single invocation." << std::endl;
      exit( 0 );
    }
  }
}

bool CegConjectureSingleInv::doVariableElimination( Node v, std::vector< Node >& conjuncts ) {
  //all conjuncts containing v must contain a literal v != s for some s
  // if so, do DER on all such conjuncts
  TNode s;
  for( unsigned i=0; i<conjuncts.size(); i++ ){
    int status = 0;
    if( getVariableEliminationTerm( true, true, v, conjuncts[i], s, status ) ){
      Trace("cegqi-si-debug") << "Substitute " << s << " for " << v << " in " << conjuncts[i] << std::endl;
      Assert( !s.isNull() );
      conjuncts[i] = conjuncts[i].substitute( v, s );
    }else{
      if( status==1 ){
        Trace("cegqi-si-debug") << "Conjunct " << conjuncts[i] << " contains " << v << " but not in disequality." << std::endl;
        return false;
      }else{
        Trace("cegqi-si-debug") << "Conjunct does not contain " << v << "." << std::endl;
      }
    }
  }
  return true;
}

bool CegConjectureSingleInv::getVariableEliminationTerm( bool pol, bool hasPol, Node v, Node n, TNode& s, int& status ) {
  if( hasPol ){
    if( n.getKind()==NOT ){
      return getVariableEliminationTerm( !pol, true, v, n[0], s, status );
    }else if( pol && ( n.getKind()==EQUAL || n.getKind()==IFF ) ){
      Node ss = QuantArith::solveEqualityFor( n, v );
      if( !ss.isNull() ){
        if( s.isNull() ){
          s = ss;
        }
        return ss==s;
      }
    }else if( ( n.getKind()==OR && !pol ) || ( n.getKind()==AND && pol ) ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( getVariableEliminationTerm( pol, true, v, n[i], s, status ) ){
          return true;
        }
      }
      return false;
    }
  }
  if( n==v ){
    status = 1;
  }else{
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      getVariableEliminationTerm( pol, false, v, n[i], s, status );
    }
  }
  return false;
}

int CegConjectureSingleInv::extractInvariantPolarity( Node n, Node inv, std::vector< Node >& curr_disj, bool pol ) {
  if( n.getKind()==NOT ){
    return extractInvariantPolarity( n[0], inv, curr_disj, !pol );
  }else if( ( n.getKind()==AND && pol ) || ( n.getKind()==OR && !pol ) ){
    int curr_pol = -1;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      int eipc = extractInvariantPolarity( n[i], inv, curr_disj, pol );
      if( eipc!=-1 ){
        if( curr_pol==-1 ){
          curr_pol = eipc;
        }else{
          return -1;
        }
      }else{
        curr_disj.push_back( pol ? n[i] : TermDb::simpleNegate( n[i] ) );
      }
    }
    return curr_pol;
  }else if( n==inv ){
    return pol ? 1 : 0;
  }else{
    return -1;
  }
}

Node CegConjectureSingleInv::substituteInvariantTemplates( Node n, std::map< Node, Node >& prog_templ, std::map< Node, std::vector< Node > >& prog_templ_vars ) {
  if( n.getKind()==APPLY_UF && n.getNumChildren()>0 ){
    std::map< Node, Node >::iterator it = prog_templ.find( n[0] );
    if( it!=prog_templ.end() ){
      std::vector< Node > children;
      for( unsigned i=1; i<n.getNumChildren(); i++ ){
        children.push_back( n[i] );
      }
      std::map< Node, std::vector< Node > >::iterator itv = prog_templ_vars.find( n[0] );
      Assert( itv!=prog_templ_vars.end() );
      Assert( children.size()==itv->second.size() );
      Node newc = it->second.substitute( itv->second.begin(), itv->second.end(), children.begin(), children.end() );
      return newc;
    }
  }
  bool childChanged = false;
  std::vector< Node > children;
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    Node nn = substituteInvariantTemplates( n[i], prog_templ, prog_templ_vars );
    children.push_back( nn );
    childChanged = childChanged || ( nn!=n[i] );
  }
  if( childChanged ){
    if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
      children.insert( children.begin(), n.getOperator() );
    }
    return NodeManager::currentNM()->mkNode( n.getKind(), children );
  }else{
    return n;
  }
}

Node CegConjectureSingleInv::removeDeepEmbedding( Node n, std::vector< Node >& progs, std::vector< TypeNode >& types, int& type_valid,
                                                  std::map< Node, Node >& visited ) {
  std::map< Node, Node >::iterator itv = visited.find( n );
  if( itv!=visited.end() ){
    return itv->second;
  }else{
    std::vector< Node > children;
    bool childChanged = false;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      Node ni = removeDeepEmbedding( n[i], progs, types, type_valid, visited );
      childChanged = childChanged || n[i]!=ni;
      children.push_back( ni );
    }
    Node ret;
    if( n.getKind()==APPLY_UF ){
      Assert( n.getNumChildren()>0 );
      if( std::find( progs.begin(), progs.end(), n[0] )!=progs.end() ){
        std::map< Node, Node >::iterator it = d_nsi_op_map.find( n[0] );
        Node op;
        if( it==d_nsi_op_map.end() ){
          bool checkTypes = !types.empty();
          std::vector< TypeNode > argTypes;
          for( unsigned j=1; j<n.getNumChildren(); j++ ){
            TypeNode tn = n[j].getType();
            argTypes.push_back( tn );
            if( checkTypes ){
              if( j>=types.size()+1 || tn!=types[j-1] ){
                type_valid = -1;
              }
            }else{
              types.push_back( tn );
            }
          }
          TypeNode ft = argTypes.empty() ? n.getType() : NodeManager::currentNM()->mkFunctionType( argTypes, n.getType() );
          std::stringstream ss2;
          ss2 << "O_" << n[0];
          op = NodeManager::currentNM()->mkSkolem( ss2.str(), ft, "was created for non-single invocation reasoning" );
          d_prog_to_eval_op[n[0]] = n.getOperator();
          d_nsi_op_map[n[0]] = op;
          d_nsi_op_map_to_prog[op] = n[0];
          Trace("cegqi-si-debug2") << "Make operator " << op << " for " << n[0] << std::endl;
        }else{
          op = it->second;
        }
        children[0] = d_nsi_op_map[n[0]];
        ret = NodeManager::currentNM()->mkNode( APPLY_UF, children );
      }
    }
    if( ret.isNull() ){
      ret = n;
      if( childChanged ){
        if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
          children.insert( children.begin(), n.getOperator() );
        }
        ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }
    visited[n] = ret;
    return ret;
  }
}

Node CegConjectureSingleInv::addDeepEmbedding( Node n, std::map< Node, Node >& visited ) {
  std::map< Node, Node >::iterator itv = visited.find( n );
  if( itv!=visited.end() ){
    return itv->second;
  }else{
    std::vector< Node > children;
    bool childChanged = false;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      Node ni = addDeepEmbedding( n[i], visited );
      childChanged = childChanged || n[i]!=ni;
      children.push_back( ni );
    }
    Node ret;
    if( n.getKind()==APPLY_UF ){
      Node op = n.getOperator();
      std::map< Node, Node >::iterator it = d_nsi_op_map_to_prog.find( op );
      if( it!=d_nsi_op_map_to_prog.end() ){
        Node prog = it->second;
        children.insert( children.begin(), prog );
        Assert( d_prog_to_eval_op.find( prog )!=d_prog_to_eval_op.end() );
        children.insert( children.begin(), d_prog_to_eval_op[prog] );
        ret = NodeManager::currentNM()->mkNode( APPLY_UF, children );
      }
    }
    if( ret.isNull() ){
      ret = n;
      if( childChanged ){
        if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
          children.insert( children.begin(), n.getOperator() );
        }
        ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }
    visited[n] = ret;
    return ret;
  }
}

bool CegConjectureSingleInv::analyzeSygusConjunct( Node p, Node n, std::map< Node, std::vector< Node > >& children,
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
      n = TermDb::simpleNegate( n );
    }
    Trace("cegqi-si") << "Sygus conjunct : " << n << std::endl;
    children[p].push_back( n );
    for( unsigned i=0; i<progs.size(); i++ ){
      prog_invoke[n][progs[i]].clear();
    }
    bool success = analyzeSygusTerm( n, prog_invoke[n], contains[n] );
    for( unsigned i=0; i<progs.size(); i++ ){
      std::map< Node, std::vector< Node > >::iterator it = prog_invoke[n].find( progs[i] );
      Trace("cegqi-si") << "  Program " << progs[i] << " is invoked " << it->second.size() << " times " << std::endl;
      for( unsigned j=0; j<it->second.size(); j++ ){
        Trace("cegqi-si") << "    " << it->second[j] << std::endl;
      }
    }
    return success;
  }
  return true;
}

bool CegConjectureSingleInv::analyzeSygusTerm( Node n, std::map< Node, std::vector< Node > >& prog_invoke, std::map< Node, bool >& contains ) {
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

bool CegConjectureSingleInv::addInstantiation( std::vector< Node >& subs ){
  std::stringstream siss;
  if( Trace.isOn("cegqi-si-inst-debug") || Trace.isOn("cegqi-engine") ){
    siss << "  * single invocation: " << std::endl;
    for( unsigned j=0; j<d_single_inv_sk.size(); j++ ){
      Node v = d_single_inv_map_to_prog[d_single_inv[0][j]];
      siss << "    * " << v;
      siss << " (" << d_single_inv_sk[j] << ")";
      siss << " -> " << subs[j] << std::endl;
    }
  }
  bool alreadyExists;
  if( options::incrementalSolving() ){
    alreadyExists = !d_c_inst_match_trie->addInstMatch( d_qe, d_single_inv, subs, d_qe->getUserContext() );
  }else{
    alreadyExists = !d_inst_match_trie.addInstMatch( d_qe, d_single_inv, subs );
  }
  Trace("cegqi-si-inst-debug") << siss.str();
  Trace("cegqi-si-inst-debug") << "  * success = " << !alreadyExists << std::endl;
  if( alreadyExists ){
    return false;
  }else{
    Trace("cegqi-engine") << siss.str() << std::endl;
    Node lem = d_single_inv[1].substitute( d_single_inv_var.begin(), d_single_inv_var.end(), subs.begin(), subs.end() );
    if( d_qe->getTermDatabase()->containsVtsTerm( lem ) ){
      Trace("cegqi-engine-debug") << "Rewrite based on vts symbols..." << std::endl;
      lem = d_qe->getTermDatabase()->rewriteVtsSymbols( lem );
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
}

bool CegConjectureSingleInv::isEligibleForInstantiation( Node n ) {
  return n.getKind()!=SKOLEM || std::find( d_single_inv_arg_sk.begin(), d_single_inv_arg_sk.end(), n )!=d_single_inv_arg_sk.end();
}

bool CegConjectureSingleInv::addLemma( Node n ) {
  d_curr_lemmas.push_back( n );
  return true;
}

void CegConjectureSingleInv::check( std::vector< Node >& lems ) {
  if( !d_single_inv.isNull() ) {
    d_curr_lemmas.clear();
    //call check for instantiator
    d_cinst->check();
    //add lemmas
    lems.insert( lems.end(), d_curr_lemmas.begin(), d_curr_lemmas.end() );
  }
}

Node CegConjectureSingleInv::constructSolution( std::vector< unsigned >& indices, unsigned i, unsigned index ) {
  Assert( index<d_inst.size() );
  Assert( i<d_inst[index].size() );
  unsigned uindex = indices[index];
  if( index==d_inst.size()-1 ){
    return d_inst[uindex][i];
  }else{
    Node cond = d_lemmas_produced[uindex];
    cond = TermDb::simpleNegate( cond );
    Node ite1 = d_inst[uindex][i];
    Node ite2 = constructSolution( indices, i, index+1 );
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
  /*
  ////remove boolean ITE (not allowed for sygus comp 2015)
  if( n.getKind()==ITE && n.getType().isBoolean() ){
    Node n1 = postProcessSolution( n[1] );
    Node n2 = postProcessSolution( n[2] );
    return NodeManager::currentNM()->mkNode( OR, NodeManager::currentNM()->mkNode( AND, n[0], n1 ),
                                                 NodeManager::currentNM()->mkNode( AND, n[0].negate(), n2 ) );
  }else{
    */
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
}


Node CegConjectureSingleInv::getSolution( unsigned sol_index, TypeNode stn, int& reconstructed ){
  Assert( d_sol!=NULL );
  Assert( !d_lemmas_produced.empty() );
  const Datatype& dt = ((DatatypeType)(stn).toType()).getDatatype();
  Node varList = Node::fromExpr( dt.getSygusVarList() );
  Node prog = d_quant[0][sol_index];
  std::vector< Node > vars;
  bool success = true;
  Trace("csi-sol") << "Get solution for " << prog << ", with skolems : ";
  if( d_prog_to_sol_index.find( prog )==d_prog_to_sol_index.end() ){
    success = false;
  }else{
    sol_index = d_prog_to_sol_index[prog];
    d_varList.clear();
    d_sol->d_varList.clear();
    Assert( d_single_inv_arg_sk.size()==varList.getNumChildren() );
    for( unsigned i=0; i<d_single_inv_arg_sk.size(); i++ ){
      Trace("csi-sol") << d_single_inv_arg_sk[i] << " ";
      if( varList[i].getType().isBoolean() ){
        //TODO force boolean term conversion mode
        Node c = NodeManager::currentNM()->mkConst(BitVector(1u, 1u));
        vars.push_back( d_single_inv_arg_sk[i].eqNode( c ) );
      }else{
        vars.push_back( d_single_inv_arg_sk[i] );
      }
      d_varList.push_back( varList[i] );
      d_sol->d_varList.push_back( varList[i] );
    }
  }
  Trace("csi-sol") << std::endl;

  //construct the solution
  Node s;
  if( success ){
    Trace("csi-sol") << "Sort solution return values " << sol_index << std::endl;
    Assert( d_lemmas_produced.size()==d_inst.size() );
    std::vector< unsigned > indices;
    for( unsigned i=0; i<d_lemmas_produced.size(); i++ ){
      Assert( sol_index<d_inst[i].size() );
      indices.push_back( i );
    }
    //sort indices based on heuristic : currently, do all constant returns first (leads to simpler conditions)
    // TODO : to minimize solution size, put the largest term last
    sortSiInstanceIndices ssii;
    ssii.d_ccsi = this;
    ssii.d_i = sol_index;
    std::sort( indices.begin(), indices.end(), ssii );
    Trace("csi-sol") << "Construct solution" << std::endl;
    s = constructSolution( indices, sol_index, 0 );
    s = s.substitute( vars.begin(), vars.end(), d_varList.begin(), d_varList.end() );
    d_orig_solution = s;
  }else{
    //function is unconstrained : make ground term of correct sort
    s = d_qe->getTermDatabase()->getEnumerateTerm( TypeNode::fromType( dt.getSygusType() ), 0 );
  }

  //simplify the solution
  Trace("csi-sol") << "Solution (pre-simplification): " << d_orig_solution << std::endl;
  s = d_sol->simplifySolution( s, stn );
  Trace("csi-sol") << "Solution (post-simplification): " << s << std::endl;
  return reconstructToSyntax( s, stn, reconstructed );
}

Node CegConjectureSingleInv::reconstructToSyntax( Node s, TypeNode stn, int& reconstructed ) {
  d_solution = s;
  const Datatype& dt = ((DatatypeType)(stn).toType()).getDatatype();

  //reconstruct the solution into sygus if necessary
  reconstructed = 0;
  if( options::cegqiSingleInvReconstruct() && !dt.getSygusAllowAll() && !stn.isNull() ){
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
  if( reconstructed==1 ){
    return d_sygus_solution;
  }else{
    return d_solution;
  }
}

bool CegConjectureSingleInv::needsCheck() {
  if( options::cegqiSingleInvMultiInstAbort() ){
    if( !hasITEs() ){
      return d_inst.empty();
    }
  }
  return true;
}

void CegConjectureSingleInv::preregisterConjecture( Node q ) {
  d_orig_conjecture = q;
}

void SingleInvocationPartition::init( std::vector< TypeNode >& typs ){
  Assert( d_arg_types.empty() );
  Assert( d_si_vars.empty() );
  d_arg_types.insert( d_arg_types.end(), typs.begin(), typs.end() );
  for( unsigned j=0; j<d_arg_types.size(); j++ ){
    Node si_v = NodeManager::currentNM()->mkBoundVar( d_arg_types[j] );
    d_si_vars.push_back( si_v );
  }
}


void SingleInvocationPartition::process( Node n ) {
  Assert( d_si_vars.size()==d_arg_types.size() );
  Trace("si-prt") << "SingleInvocationPartition::process " << n << std::endl;
  Trace("si-prt") << "Get conjuncts..." << std::endl;
  std::vector< Node > conj;
  if( collectConjuncts( n, true, conj ) ){
    Trace("si-prt") << "...success." << std::endl;
    for( unsigned i=0; i<conj.size(); i++ ){
      std::vector< Node > si_terms;
      std::vector< Node > si_subs;
      Trace("si-prt") << "Process conjunct : " << conj[i] << std::endl;
      //do DER on conjunct
      Node cr = TermDb::getQuantSimplify( conj[i] );
      Trace("si-prt-debug") << "...rewritten to " << cr << std::endl;
      std::map< Node, bool > visited;
      // functions to arguments
      std::vector< Node > args;
      std::vector< Node > terms;
      std::vector< Node > subs;
      bool singleInvocation = true;
      if( processConjunct( cr, visited, args, terms, subs ) ){
        for( unsigned j=0; j<terms.size(); j++ ){
          si_terms.push_back( subs[j] );
          si_subs.push_back( d_func_fo_var[subs[j].getOperator()] );
        }
        std::map< Node, Node > subs_map;
        std::map< Node, Node > subs_map_rev;
        std::vector< Node > funcs;
        //normalize the invocations
        if( !terms.empty() ){
          cr = cr.substitute( terms.begin(), terms.end(), subs.begin(), subs.end() );
        }
        std::vector< Node > children;
        children.push_back( cr );
        terms.clear();
        subs.clear();
        Trace("si-prt") << "...single invocation, with arguments: " << std::endl;
        for( unsigned j=0; j<args.size(); j++ ){
          Trace("si-prt") << args[j] << " ";
          if( args[j].getKind()==BOUND_VARIABLE && std::find( terms.begin(), terms.end(), args[j] )==terms.end() ){
            terms.push_back( args[j] );
            subs.push_back( d_si_vars[j] );
          }else{
            children.push_back( d_si_vars[j].eqNode( args[j] ).negate() );
          }
        }
        Trace("si-prt") << std::endl;
        cr = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( OR, children );
        cr = cr.substitute( terms.begin(), terms.end(), subs.begin(), subs.end() );
        Trace("si-prt-debug") << "...normalized invocations to " << cr << std::endl;
        //now must check if it has other bound variables
        std::vector< Node > bvs;
        TermDb::getBoundVars( cr, bvs );
        if( bvs.size()>d_si_vars.size() ){
          Trace("si-prt") << "...not ground single invocation." << std::endl;
          singleInvocation = false;
        }else{
          Trace("si-prt") << "...ground single invocation : success." << std::endl;
        }
      }else{
        Trace("si-prt") << "...not single invocation." << std::endl;
        singleInvocation = false;
      }
      Trace("si-prt") << "..... got si=" << singleInvocation << ", result : " << cr << std::endl;
      d_conjuncts[2].push_back( cr );
      if( singleInvocation ){
        //replace with single invocation formulation
        cr = cr.substitute( si_terms.begin(), si_terms.end(), si_subs.begin(), si_subs.end() );
        Trace("si-prt") << "..... si version=" << cr << std::endl;
        d_conjuncts[0].push_back( cr );
      }else{
        d_conjuncts[1].push_back( cr );
      }
    }
  }else{
    Trace("si-prt") << "...failed." << std::endl;
  }
}

bool SingleInvocationPartition::collectConjuncts( Node n, bool pol, std::vector< Node >& conj ) {
  if( ( !pol && n.getKind()==OR ) || ( pol && n.getKind()==AND ) ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( !collectConjuncts( n[i], pol, conj ) ){
        return false;
      }
    }
  }else if( n.getKind()==NOT ){
    return collectConjuncts( n[0], !pol, conj );
  }else if( n.getKind()==FORALL ){
    return false;
  }else{
    if( !pol ){
      n = TermDb::simpleNegate( n );
    }
    Trace("si-prt") << "Conjunct : " << n << std::endl;
    conj.push_back( n );
  }
  return true;
}

bool SingleInvocationPartition::processConjunct( Node n, std::map< Node, bool >& visited, std::vector< Node >& args, 
                                                 std::vector< Node >& terms, std::vector< Node >& subs ) {
  std::map< Node, bool >::iterator it = visited.find( n );
  if( it!=visited.end() ){
    return true;
  }else{
    bool ret = true;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( !processConjunct( n[i], visited, args, terms, subs ) ){
        ret = false;
      }
    }
    if( ret ){
      if( n.getKind()==APPLY_UF ){
        if( std::find( terms.begin(), terms.end(), n )==terms.end() ){
          Node f = n.getOperator();
          //check if it matches the type requirement
          if( isAntiSkolemizableType( f ) ){
            if( args.empty() ){
              //record arguments
              for( unsigned i=0; i<n.getNumChildren(); i++ ){
                args.push_back( n[i] );
              }
            }else{
              //arguments must be the same as those already recorded
              for( unsigned i=0; i<n.getNumChildren(); i++ ){
                if( args[i]!=n[i] ){
                  Trace("si-prt-debug") << "... bad invocation : " << n << " at arg " << i << "." << std::endl;
                  ret = false;
                  break;
                }
              }
            }
            if( ret ){
              terms.push_back( n );
              subs.push_back( d_func_inv[f] );
            }
          }else{
            Trace("si-prt-debug") << "... " << f << " is a bad operator." << std::endl;
            ret = false;
          }
        }
      }
    }
    visited[n] = ret;
    return ret;
  }
}

bool SingleInvocationPartition::isAntiSkolemizableType( Node f ) {
  std::map< Node, bool >::iterator it = d_funcs.find( f );
  if( it!=d_funcs.end() ){
    return it->second;
  }else{
    TypeNode tn = f.getType();
    bool ret = false;
    if( tn.getNumChildren()==d_arg_types.size()+1 ){
      ret = true;
      std::vector< Node > children;
      children.push_back( f );
      for( unsigned i=0; i<d_arg_types.size(); i++ ){
        children.push_back( d_si_vars[i] );
        if( tn[i]!=d_arg_types[i] ){
          ret = false;
          break;
        }
      }
      if( ret ){
        Node t = NodeManager::currentNM()->mkNode( APPLY_UF, children );
        d_func_inv[f] = t;
        d_inv_to_func[t] = f;
        std::stringstream ss;
        ss << "F_" << f;
        Node v = NodeManager::currentNM()->mkBoundVar( ss.str(), tn.getRangeType() );
        d_func_fo_var[f] = v;
        d_fo_var_to_func[v] = f;
        d_func_vars.push_back( v );
      }
    }
    d_funcs[f] = ret;
    return ret;
  }
}

Node SingleInvocationPartition::getConjunct( int index ) {
  return d_conjuncts[index].empty() ? NodeManager::currentNM()->mkConst( true ) : 
          ( d_conjuncts[index].size()==1 ? d_conjuncts[index][0] : NodeManager::currentNM()->mkNode( AND, d_conjuncts[index] ) );
}

void SingleInvocationPartition::extractInvariant( Node n, Node& func, int& pol, std::vector< Node >& disjuncts ) {
  if( n.getKind()==OR ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      extractInvariant( n[i], func, pol, disjuncts );
    }
  }else{
    bool lit_pol = n.getKind()!=NOT;
    Node lit = n.getKind()==NOT ? n[0] : n;
    std::map< Node, Node >::iterator it = d_inv_to_func.find( lit );
    if( it!=d_inv_to_func.end() ){
      if( pol==-1 ){
        pol = lit_pol ? 0 : 1;
        func = it->second;
      }else{
        //mixing multiple invariants
        pol = -2;
      }
    }else{
      disjuncts.push_back( n );
    }
  }
}

void SingleInvocationPartition::debugPrint( const char * c ) {
  Trace(c) << "Single invocation variables : ";
  for( unsigned i=0; i<d_si_vars.size(); i++ ){
    Trace(c) << d_si_vars[i] << " ";
  }
  Trace(c) << std::endl;
  Trace(c) << "Functions : " << std::endl;
  for( std::map< Node, bool >::iterator it = d_funcs.begin(); it != d_funcs.end(); ++it ){
    Trace(c) << "  " << it->first << " : ";
    if( it->second ){
      Trace(c) << d_func_inv[it->first] << " " << d_func_fo_var[it->first] << std::endl;
    }else{
      Trace(c) << "not incorporated." << std::endl;
    }
  }
  for( unsigned i=0; i<3; i++ ){
    Trace(c) << ( i==0 ? "Single invocation" : ( i==1 ? "Non-single invocation" : "All" ) );
    Trace(c) << " conjuncts: " << std::endl;
    for( unsigned j=0; j<d_conjuncts[i].size(); j++ ){
      Trace(c) << "  " << (j+1) << " : " << d_conjuncts[i][j] << std::endl;
    }
  }
  Trace(c) << std::endl;
}

}