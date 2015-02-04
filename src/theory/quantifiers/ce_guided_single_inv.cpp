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

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace std;

namespace CVC4 {

Node simpleNegate( Node n ){
  if( n.getKind()==OR || n.getKind()==AND ){
    std::vector< Node > children;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      children.push_back( simpleNegate( n[i] ) );
    }
    return NodeManager::currentNM()->mkNode( n.getKind()==OR ? AND : OR, children );
  }else{
    return n.negate();
  }
}


CegConjectureSingleInv::CegConjectureSingleInv( Node q, CegConjecture * p ) : d_parent( p ), d_quant( q ){

}

Node CegConjectureSingleInv::getSingleInvLemma( Node guard ) {
  if( !d_single_inv.isNull() ) {
    Assert( d_single_inv.getKind()==FORALL );
    d_single_inv_var.clear();
    d_single_inv_sk.clear();
    for( unsigned i=0; i<d_single_inv[0].getNumChildren(); i++ ){
      std::stringstream ss;
      ss << "k_" << d_single_inv[0][i];
      Node k = NodeManager::currentNM()->mkSkolem( ss.str(), d_single_inv[0][i].getType(), "single invocation function skolem" );
      d_single_inv_var.push_back( d_single_inv[0][i] );
      d_single_inv_sk.push_back( k );
      d_single_inv_sk_index[k] = i;
    }
    Node inst = d_single_inv[1].substitute( d_single_inv_var.begin(), d_single_inv_var.end(), d_single_inv_sk.begin(), d_single_inv_sk.end() );
    inst = simpleNegate( inst );
    Trace("cegqi-si") << "Single invocation initial lemma : " << inst << std::endl;
    return NodeManager::currentNM()->mkNode( OR, guard.negate(), inst );
  }else{
    return Node::null();
  }
}

void CegConjectureSingleInv::initialize() {
  Node q = d_quant;
  Trace("cegqi-si") << "Initialize cegqi-si for " << q << std::endl;
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
  bool singleInvocation = false;
  if( analyzeSygusConjunct( Node::null(), q[1], children, prog_invoke, progs, contains, true ) ){
    singleInvocation = true;
    //try to phrase as single invocation property
    Trace("cegqi-si") << "...success." << std::endl;
    std::map< Node, std::vector< Node > > invocations;
    std::map< Node, std::map< int, std::vector< Node > > > single_invoke_args;
    std::map< Node, std::map< int, std::map< Node, std::vector< Node > > > > single_invoke_args_from;
    for( std::map< Node, std::vector< Node > >::iterator it = children.begin(); it != children.end(); ++it ){
      for( unsigned j=0; j<it->second.size(); j++ ){
        Node conj = it->second[j];
        Trace("cegqi-si-debug") << "Process child " << conj << " from " << it->first << std::endl;
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
                Trace("cegqi-si-debug") << "process : " << arg << " occurs in position " << k-1 << " in invocation " << inv << " of " << prog << " in " << conj << std::endl;
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
      Trace("cegqi-si") << "Property is single invocation with : " << std::endl;
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
        std::stringstream ss;
        ss << "F_" << prog;
        Node pv = NodeManager::currentNM()->mkBoundVar( ss.str(), inv.getType() );
        d_single_inv_map[prog] = pv;
        d_single_inv_map_to_prog[pv] = prog;
        pbvs.push_back( pv );
        Trace("cegqi-si-debug2") << "Make variable " << pv << " for " << prog << std::endl;
        for( unsigned k=1; k<inv.getNumChildren(); k++ ){
          Assert( !single_invoke_args[prog][k-1].empty() );
          if( single_invoke_args[prog][k-1].size()==1 && single_invoke_args[prog][k-1][0].getKind()==BOUND_VARIABLE ){
            invc.push_back( single_invoke_args[prog][k-1][0] );
          }else{
            //introduce fresh variable, assign all
            Node v = NodeManager::currentNM()->mkSkolem( "a", single_invoke_args[prog][k-1][0].getType(), "single invocation arg" );
            new_vars.push_back( v );
            invc.push_back( v );
            d_single_inv_arg_sk.push_back( v );

            for( unsigned i=0; i<single_invoke_args[prog][k-1].size(); i++ ){
              Node arg = single_invoke_args[prog][k-1][i];
              Node asum = NodeManager::currentNM()->mkNode( arg.getType().isBoolean() ? IFF : EQUAL, v, arg ).negate();
              Trace("cegqi-si-debug") << "  ..." << arg << " occurs in ";
              Trace("cegqi-si-debug") << single_invoke_args_from[prog][k-1][arg].size() << " invocations at position " << (k-1) << " of " << prog << "." << std::endl;
              for( unsigned j=0; j<single_invoke_args_from[prog][k-1][arg].size(); j++ ){
                Node conj = single_invoke_args_from[prog][k-1][arg][j];
                Trace("cegqi-si-debug") << "  ..." << arg << " occurs in invocation " << inv << " of " << prog << " in " << conj << std::endl;
                Trace("cegqi-si-debug") << "  ...add assumption " << asum << " to " << conj << std::endl;
                if( std::find( new_assumptions[conj].begin(), new_assumptions[conj].end(), asum )==new_assumptions[conj].end() ){
                  new_assumptions[conj].push_back( asum );
                }
              }
            }
          }
        }
        Node sinv = NodeManager::currentNM()->mkNode( APPLY_UF, invc );
        Trace("cegqi-si") << "  " << prog << " -> " << sinv << std::endl;
        d_single_inv_app_map[prog] = sinv;
      }
      //construct the single invocation version of the property
      Trace("cegqi-si") << "Single invocation formula conjuncts are : " << std::endl;
      //std::vector< Node > si_conj;
      Assert( !pbvs.empty() );
      Node pbvl = NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, pbvs );
      for( std::map< Node, std::vector< Node > >::iterator it = children.begin(); it != children.end(); ++it ){
        //should hold since we prevent miniscoping
        Assert( d_single_inv.isNull() );
        std::vector< Node > conjuncts;
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
                Trace("cegqi-si-debug2") << "subs : " << inv << " -> var for " << prog << " : " << d_single_inv_map[prog] << std::endl;
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
          curr = simpleNegate( curr );
          Trace("cegqi-si") << "    " << curr;
          conjuncts.push_back( curr );
          if( !it->first.isNull() ){
            Trace("cegqi-si-debug") << " under " << it->first;
          }
          Trace("cegqi-si") << std::endl;
        }
        Assert( !conjuncts.empty() );
        //make the skolems for the existential
        if( !it->first.isNull() ){
          std::vector< Node > vars;
          std::vector< Node > sks;
          for( unsigned j=0; j<it->first.getNumChildren(); j++ ){
            std::stringstream ss;
            ss << "a_" << it->first[j];
            Node v = NodeManager::currentNM()->mkSkolem( ss.str(), it->first[j].getType(), "single invocation skolem" );
            vars.push_back( it->first[j] );
            sks.push_back( v );
          }
          //substitute conjunctions
          for( unsigned i=0; i<conjuncts.size(); i++ ){
            conjuncts[i] = conjuncts[i].substitute( vars.begin(), vars.end(), sks.begin(), sks.end() );
          }
          d_single_inv_arg_sk.insert( d_single_inv_arg_sk.end(), sks.begin(), sks.end() );
          //substitute single invocation applications
          for( std::map< Node, Node >::iterator itam = d_single_inv_app_map.begin(); itam != d_single_inv_app_map.end(); ++itam ){
            Node n = itam->second;
            d_single_inv_app_map[itam->first] = n.substitute( vars.begin(), vars.end(), sks.begin(), sks.end() );
          }
        }
        //ensure that this is a ground property
        for( std::map< Node, Node >::iterator itam = d_single_inv_app_map.begin(); itam != d_single_inv_app_map.end(); ++itam ){
          Node n = itam->second;
          //check if all variables are arguments of this
          std::vector< Node > n_args;
          for( unsigned i=1; i<n.getNumChildren(); i++ ){
            n_args.push_back( n[i] );
          }
          for( int i=0; i<(int)d_single_inv_arg_sk.size(); i++ ){
            if( std::find( n_args.begin(), n_args.end(), d_single_inv_arg_sk[i] )==n_args.end() ){
              Trace("cegqi-si") << "...property is not ground: program invocation " << n << " does not contain variable " << d_single_inv_arg_sk[i] << "." << std::endl;
              //try to do variable elimination on d_single_inv_arg_sk[i]
              if( doVariableElimination( d_single_inv_arg_sk[i], conjuncts ) ){
                Trace("cegqi-si") << "...did variable elimination on " << d_single_inv_arg_sk[i] << std::endl;
                d_single_inv_arg_sk.erase( d_single_inv_arg_sk.begin() + i, d_single_inv_arg_sk.begin() + i + 1 );
                i--;
              }else{
                singleInvocation = false;
                //exit( 57 );
              }
              break;
            }
          }
        }

        if( singleInvocation ){
          Node bd = conjuncts.size()==1 ? conjuncts[0] : NodeManager::currentNM()->mkNode( OR, conjuncts );
          d_single_inv = NodeManager::currentNM()->mkNode( FORALL, pbvl, bd );
          Trace("cegqi-si-debug") << "...formula is : " << d_single_inv << std::endl;
          /*
          //equality resolution
          for( unsigned j=0; j<conjuncts.size(); j++ ){
            Node conj = conjuncts[j];
            std::map< Node, std::vector< Node > > case_vals;
            bool exh = processSingleInvLiteral( conj, false, case_vals );
            Trace("cegqi-si-er") << "Conjunct " << conj << " gives equality restrictions, exh = " << exh << " : " << std::endl;
            for( std::map< Node, std::vector< Node > >::iterator it = case_vals.begin(); it != case_vals.end(); ++it ){
              Trace("cegqi-si-er") << "  " << it->first << " -> ";
              for( unsigned k=0; k<it->second.size(); k++ ){
                Trace("cegqi-si-er") << it->second[k] << " ";
              }
              Trace("cegqi-si-er") << std::endl;
            }
          }
          */
        }
      }
    }
  }
  if( !singleInvocation ){
    Trace("cegqi-si") << "Property is not single invocation." << std::endl;
    if( options::cegqiSingleInvAbort() ){
      Message() << "Property is not single invocation." << std::endl;
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
    }else if( pol && n.getKind()==EQUAL ){
      for( unsigned r=0; r<2; r++ ){
        if( n[r]==v ){
          status = 1;
          Node ss = n[r==0 ? 1 : 0];
          if( s.isNull() ){
            s = ss;
          }
          return ss==s;
        }
      }
      //did not match, now see if it contains v
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

bool CegConjectureSingleInv::processSingleInvLiteral( Node lit, bool pol, std::map< Node, std::vector< Node > >& case_vals ) {
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
      n = simpleNegate( n );
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


void CegConjectureSingleInv::check( QuantifiersEngine * qe, std::vector< Node >& lems ) {
  if( !d_single_inv.isNull() ) {
    eq::EqualityEngine* ee = qe->getMasterEqualityEngine();
    Trace("cegqi-engine") << "  * single invocation: " << std::endl;
    std::vector< Node > subs;
    std::map< Node, int > subs_from_model;
    std::vector< Node > waiting_to_slv;
    for( unsigned i=0; i<d_single_inv_sk.size(); i++ ){
      Node v = d_single_inv_map_to_prog[d_single_inv[0][i]];
      Node pv = d_single_inv_sk[i];
      Trace("cegqi-engine") << "    * " << v;
      Trace("cegqi-engine") << " (" << pv << ")";
      Trace("cegqi-engine") << " -> ";
      Node slv;
      if( ee->hasTerm( pv ) ){
        Node r = ee->getRepresentative( pv );
        eq::EqClassIterator eqc_i = eq::EqClassIterator( r, ee );
        bool isWaitingSlv = false;
        while( !eqc_i.isFinished() ){
          Node n = *eqc_i;
          if( n!=pv ){
            if( slv.isNull() || isWaitingSlv ){
              std::vector< Node > vars;
              collectProgVars( n, vars );
              if( slv.isNull() || vars.empty() ){
                // n cannot contain pv
                bool isLoop = std::find( vars.begin(), vars.end(), pv )!=vars.end();
                if( !isLoop ){
                  for( unsigned j=0; j<vars.size(); j++ ){
                    if( std::find( waiting_to_slv.begin(), waiting_to_slv.end(), vars[j] )!=waiting_to_slv.end() ){
                      isLoop = true;
                      break;
                    }
                  }
                  if( !isLoop ){
                    slv = n;
                    isWaitingSlv = !vars.empty();
                  }
                }
              }
            }
          }
          ++eqc_i;
        }
        if( isWaitingSlv ){
          Trace("cegqi-engine-debug") << "waiting:";
          waiting_to_slv.push_back( pv );
        }
      }else{
        Trace("cegqi-engine-debug") << "N/A:";
      }
      if( slv.isNull() ){
        //get model value
        Node mv = qe->getModel()->getValue( pv );
        subs.push_back( mv );
        subs_from_model[pv] = i;
        if( Trace.isOn("cegqi-engine") || Trace.isOn("cegqi-engine-debug") ){
          Trace("cegqi-engine") << "M:" << mv;
        }
      }else{
        subs.push_back( slv );
        Trace("cegqi-engine") << slv;
      }
      Trace("cegqi-engine") << std::endl;
    }
    for( int i=(int)(waiting_to_slv.size()-1); i>=0; --i ){
      int index = d_single_inv_sk_index[waiting_to_slv[i]];
      Trace("cegqi-engine-debug") << "Go back and solve " << d_single_inv_sk[index] << std::endl;
      Trace("cegqi-engine-debug") << "Substitute " << subs[index] << " to ";
      subs[index] = applyProgVarSubstitution( subs[index], subs_from_model, subs );
      Trace("cegqi-engine-debug") << subs[index] << std::endl;
    }
    //try to improve substitutions : look for terms that contain terms in question
    if( !subs_from_model.empty() ){
      eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
      while( !eqcs_i.isFinished() ){
        Node r = *eqcs_i;
        int res = -1;
        Node slv_n;
        Node const_n;
        eq::EqClassIterator eqc_i = eq::EqClassIterator( r, ee );
        while( !eqc_i.isFinished() ){
          Node n = *eqc_i;
          if( slv_n.isNull() || const_n.isNull() ){
            std::vector< Node > vars;
            int curr_res = classifyTerm( n, subs_from_model );
            Trace("cegqi-si-debug2") << "Term : " << n << " classify : " << curr_res << std::endl;
            if( curr_res!=-2 ){
              if( curr_res!=-1 && slv_n.isNull() ){
                res = curr_res;
                slv_n = n;
              }else if( const_n.isNull() ){
                const_n = n;
              }
            }
          }
          ++eqc_i;
        }
        if( !slv_n.isNull() && !const_n.isNull() ){
          if( slv_n.getType().isInteger() || slv_n.getType().isReal() ){
            Trace("cegqi-si-debug") << "Can possibly set " << d_single_inv_sk[res] << " based on " << slv_n << " = " << const_n << std::endl;
            subs_from_model.erase( d_single_inv_sk[res] );
            Node prev_subs_res = subs[res];
            subs[res] = d_single_inv_sk[res];
            Node eq = slv_n.eqNode( const_n );
            bool success = false;
            std::map< Node, Node > msum;
            if( QuantArith::getMonomialSumLit( eq, msum ) ){
              Trace("cegqi-si-debug") << "As monomial sum : " << std::endl;
              QuantArith::debugPrintMonomialSum( msum, "cegqi-si");
              Node veq;
              if( QuantArith::isolate( d_single_inv_sk[res], msum, veq, EQUAL ) ){
                Trace("cegqi-si-debug") << "Isolated for " << d_single_inv_sk[res] << " : " << veq << std::endl;
                Node sol;
                for( unsigned r=0; r<2; r++ ){
                  if( veq[r]==d_single_inv_sk[res] ){
                    sol = veq[ r==0 ? 1 : 0 ];
                  }
                }
                if( !sol.isNull() ){
                  sol = applyProgVarSubstitution( sol, subs_from_model, subs );
                  Trace("cegqi-si-debug") << "Substituted solution is : " << sol << std::endl;
                  subs[res] = sol;
                  Trace("cegqi-engine") << "  ...by arithmetic, " << d_single_inv_sk[res] << " -> " << sol << std::endl;
                  success = true;
                }
              }
            }
            if( !success ){
              subs[res] = prev_subs_res;
            }
          }
        }
        ++eqcs_i;
      }
    }
    Node lem = d_single_inv[1].substitute( d_single_inv_var.begin(), d_single_inv_var.end(), subs.begin(), subs.end() );
    lem = Rewriter::rewrite( lem );
    Trace("cegqi-si") << "Single invocation lemma : " << lem << std::endl;
    if( std::find( d_lemmas_produced.begin(), d_lemmas_produced.end(), lem )==d_lemmas_produced.end() ){
      lems.push_back( lem );
      d_lemmas_produced.push_back( lem );
      d_inst.push_back( std::vector< Node >() );
      d_inst.back().insert( d_inst.back().end(), subs.begin(), subs.end() );
    }
  }
}

Node CegConjectureSingleInv::applyProgVarSubstitution( Node n, std::map< Node, int >& subs_from_model, std::vector< Node >& subs ) {
  std::vector< Node > vars;
  collectProgVars( n, vars );
  if( !vars.empty() ){
    std::vector< Node > ssubs;
    //get substitution
    for( unsigned i=0; i<vars.size(); i++ ){
      Assert( d_single_inv_sk_index.find( vars[i] )!=d_single_inv_sk_index.end() );
      int index = d_single_inv_sk_index[vars[i]];
      ssubs.push_back( subs[index] );
      //it is now constrained
      if( subs_from_model.find( vars[i] )!=subs_from_model.end() ){
        subs_from_model.erase( vars[i] );
      }
    }
    n = n.substitute( vars.begin(), vars.end(), ssubs.begin(), ssubs.end() );
    n = Rewriter::rewrite( n );
    return n;
  }else{
    return n;
  }
}

int CegConjectureSingleInv::classifyTerm( Node n, std::map< Node, int >& subs_from_model ) {
  if( n.getKind()==SKOLEM ){
    std::map< Node, int >::iterator it = subs_from_model.find( n );
    if( it!=subs_from_model.end() ){
      return it->second;
    }else{
      // if it is symbolic argument, we are also fine
      if( std::find( d_single_inv_arg_sk.begin(), d_single_inv_arg_sk.end(), n )!=d_single_inv_arg_sk.end() ){
        return -1;
      }else{
        //if it is another program, we are also fine
        if( std::find( d_single_inv_sk.begin(), d_single_inv_sk.end(), n )!=d_single_inv_sk.end() ){
          return -1;
        }else{
          return -2;
        }
      }
    }
  }else{
    int curr_res = -1;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      int res = classifyTerm( n[i], subs_from_model );
      if( res==-2 ){
        return res;
      }else if( res!=-1 ){
        curr_res = res;
      }
    }
    return curr_res;
  }
}

void CegConjectureSingleInv::collectProgVars( Node n, std::vector< Node >& vars ) {
  if( n.getKind()==SKOLEM ){
    if( std::find( d_single_inv_sk.begin(), d_single_inv_sk.end(), n )!=d_single_inv_sk.end() ){
      if( std::find( vars.begin(), vars.end(), n )==vars.end() ){
        vars.push_back( n );
      }
    }
  }else{
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      collectProgVars( n[i], vars );
    }
  }
}


Node CegConjectureSingleInv::constructSolution( unsigned i, unsigned index ) {
  Assert( index<d_inst.size() );
  Assert( i<d_inst[index].size() );
  if( index==d_inst.size()-1 ){
    return d_inst[index][i];
  }else{
    Node cond = d_lemmas_produced[index];
    cond = simpleNegate( cond );
    Node ite1 = d_inst[index][i];
    Node ite2 = constructSolution( i, index+1 );
    return NodeManager::currentNM()->mkNode( ITE, cond, ite1, ite2 );
  }
}

Node CegConjectureSingleInv::getSolution( QuantifiersEngine * qe, unsigned i, TypeNode stn, int& reconstructed ){
  Assert( !d_lemmas_produced.empty() );
  Node s = constructSolution( i, 0 );
  const Datatype& dt = ((DatatypeType)(stn).toType()).getDatatype();
  Node varList = Node::fromExpr( dt.getSygusVarList() );
  //TODO : not in grammar
  Node prog = d_quant[0][i];
  Node prog_app = d_single_inv_app_map[prog];
  std::vector< Node > vars;
  std::vector< Node > subs;
  Trace("cegqi-si-debug-sol") << "Get solution for " << prog << ", which is applied as " << prog_app << std::endl;
  Assert( prog_app.getNumChildren()==varList.getNumChildren()+1 );
  for( unsigned i=1; i<prog_app.getNumChildren(); i++ ){
    vars.push_back( prog_app[i] );
    subs.push_back( varList[i-1] );
  }
  s = s.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
  d_orig_solution = s;
  Trace("cegqi-si-debug-sol") << "Solution (pre-rewrite): " << d_orig_solution << std::endl;
  s = pullITEs( s );
  //s = flattenITEs( s );
  //do standard rewriting
  s = Rewriter::rewrite( s );

  std::map< Node, bool > sassign;
  std::vector< Node > svars;
  std::vector< Node > ssubs;
  Trace("cegqi-si-debug-sol") << "Solution (pre-simplification): " << s << std::endl;
  s = simplifySolution( qe, s, sassign, svars, ssubs, subs, 0 );
  Trace("cegqi-si-debug-sol") << "Solution (post-simplification): " << s << std::endl;
  s = Rewriter::rewrite( s );
  Trace("cegqi-si-debug-sol") << "Solution (post-rewrite): " << s << std::endl;
  d_solution = s;
  if( options::cegqiSingleInvReconstruct() && !stn.isNull() ){
    collectReconstructNodes( qe->getTermDatabaseSygus(), d_solution, stn, Node::null(), TypeNode::null(), false );
    std::vector< TypeNode > rcons_tn;
    for( std::map< TypeNode, std::map< Node, bool > >::iterator it = d_rcons_to_process.begin(); it != d_rcons_to_process.end(); ++it ){
      TypeNode tn = it->first;
      Assert( datatypes::DatatypesRewriter::isTypeDatatype(tn) );
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      Trace("cegqi-si-rcons") << it->second.size() << " terms to reconstruct of type " << dt.getName() << " : " << std::endl;
      for( std::map< Node, bool >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
        Trace("cegqi-si-rcons") << "  " << it2->first << std::endl;
      }
      Assert( !it->second.empty() );
      rcons_tn.push_back( it->first );
    }
    bool success;
    unsigned index = 0;
    do {
      success = true;
      std::vector< TypeNode > to_erase;
      for( std::map< TypeNode, std::map< Node, bool > >::iterator it = d_rcons_to_process.begin(); it != d_rcons_to_process.end(); ++it ){
        if( it->second.empty() ){
          to_erase.push_back( it->first );
        }else{
          Node ns = qe->getTermDatabase()->getEnumerateTerm( it->first, index );
          Node nb = qe->getTermDatabaseSygus()->sygusToBuiltin( ns, it->first );
          Node nr = Rewriter::rewrite( nb );//qe->getTermDatabaseSygus()->getNormalized( it->first, nb, false, false );
          if( it->second.find( nr )!=it->second.end() ){
            Trace("cegqi-si-rcons") << "...reconstructed " << ns << " for term " << nr << std::endl;
            d_reconstructed[nr][it->first] = ns;
            d_reconstructed_op[nr][it->first] = false;
            setReconstructed( nr, it->first );
          }
          success = false;
        }
      }
      for( unsigned i=0; i<to_erase.size(); i++ ){
        Trace("cegqi-si-rcons") << "......reconstructed all terms for type " << to_erase[i] << std::endl;
        d_rcons_to_process.erase( to_erase[i] );
      }
      index++;
      if( index%100==0 ){
        Trace("cegqi-si-rcons-debug") << "Tried " << index << " for each type."  << std::endl;
      }
      if( success ){
        reconstructed = 1;
      }
    }while( !success );
  }else{
    reconstructed = 0;
  }
  if( Trace.isOn("cegqi-si-debug-sol") ){
    //debug solution
    if( !debugSolution( d_solution ) ){
      Trace("cegqi-si-debug-sol") << "WARNING : solution " << d_solution << " contains free constants." << std::endl;
      //exit( 47 );
    }else{
      //exit( 49 );
    }
  }
  if( Trace.isOn("cegqi-stats") ){
    int t_size = 0;
    int num_ite = 0;
    debugTermSize( d_orig_solution, t_size, num_ite );
    //Trace("cegqi-stats") << "size " << t_size << " #ite " << num_ite << std::endl;
    Trace("cegqi-stats") << t_size << " " << num_ite << " ";
    t_size = 0;
    num_ite = 0;
    debugTermSize( d_solution, t_size, num_ite );
    //Trace("cegqi-stats") << "simplified size " << t_size << " #ite " << num_ite << std::endl;
    Trace("cegqi-stats") << t_size << " " << num_ite << std::endl;
  }
  return d_solution;
}

bool CegConjectureSingleInv::debugSolution( Node sol ) {
  if( sol.getKind()==SKOLEM ){
    return false;
  }else{
    for( unsigned i=0; i<sol.getNumChildren(); i++ ){
      if( !debugSolution( sol[i] ) ){
        return false;
      }
    }
    return true;
  }

}

void CegConjectureSingleInv::debugTermSize( Node sol, int& t_size, int& num_ite ) {
  t_size++;
  if( sol.getKind()==ITE ){
    num_ite++;
  }
  for( unsigned i=0; i<sol.getNumChildren(); i++ ){
    debugTermSize( sol[i], t_size, num_ite );
  }
}

Node CegConjectureSingleInv::pullITEs( Node s ) {
  if( s.getKind()==ITE ){
    bool success;
    do {
      success = false;
      std::vector< Node > conj;
      Node t;
      Node rem;
      if( pullITECondition( s, s, conj, t, rem, 0 ) ){
        Assert( !conj.empty() );
        Node cond = conj.size()==1 ? conj[0] : NodeManager::currentNM()->mkNode( AND, conj );
        Trace("cegqi-si-debug-sol") << "For " << s << ", can pull " << cond << " -> " << t << " with remainder " << rem << std::endl;
        t = pullITEs( t );
        rem = pullITEs( rem );
        s = NodeManager::currentNM()->mkNode( ITE, simpleNegate( cond ), t, rem );
        //Trace("cegqi-si-debug-sol") << "Now : " << s << std::endl;
        success = true;
      }
    }while( success );
  }
  return s;
}

// pull condition common to all ITE conditions in path of size > 1
bool CegConjectureSingleInv::pullITECondition( Node root, Node n_ite, std::vector< Node >& conj, Node& t, Node& rem, int depth ) {
  Assert( n_ite.getKind()==ITE );
  std::vector< Node > curr_conj;
  bool isAnd;
  if( n_ite[0].getKind()==AND || n_ite[0].getKind()==OR ){
    isAnd = n_ite[0].getKind()==AND;
    for( unsigned i=0; i<n_ite[0].getNumChildren(); i++ ){
      Node cond = n_ite[0][i];
      if( n_ite[0].getKind()==OR ){
        cond = simpleNegate( cond );
      }
      curr_conj.push_back( cond );
    }
  }else{
    Node neg = n_ite[0].negate();
    if( std::find( conj.begin(), conj.end(), neg )!=conj.end() ){
      isAnd = false;
      curr_conj.push_back( neg );
    }else{
      isAnd = true;
      curr_conj.push_back( n_ite[0] );
    }
  }
  // take intersection with current conditions
  std::vector< Node > new_conj;
  std::vector< Node > prev_conj;
  if( n_ite==root ){
    new_conj.insert( new_conj.end(), curr_conj.begin(), curr_conj.end() );
    Trace("cegqi-pull-ite") << "Pull ITE root " << n_ite << ", #conj = " << new_conj.size() << std::endl;
  }else{
    for( unsigned i=0; i<curr_conj.size(); i++ ){
      if( std::find( conj.begin(), conj.end(), curr_conj[i] )!=conj.end() ){
        new_conj.push_back( curr_conj[i] );
      }
    }
    Trace("cegqi-pull-ite") << "Pull ITE " << n_ite << ", #conj = " << conj.size() << " intersect " << curr_conj.size() << " = " << new_conj.size() << std::endl;
  }
  //cannot go further
  if( new_conj.empty() ){
    return false;
  }
  //it is an intersection with current
  conj.clear();
  conj.insert( conj.end(), new_conj.begin(), new_conj.end() );
  //recurse if possible
  Node trec = n_ite[ isAnd ? 2 : 1 ];
  Node tval = n_ite[ isAnd ? 1 : 2 ];
  bool success = false;
  if( trec.getKind()==ITE ){
    prev_conj.insert( prev_conj.end(), conj.begin(), conj.end() );
    success = pullITECondition( root, trec, conj, t, rem, depth+1 );
  }
  if( !success && depth>0 ){
    t = trec;
    rem = trec;
    success = true;
    if( trec.getKind()==ITE ){
      //restore previous state
      conj.clear();
      conj.insert( conj.end(), prev_conj.begin(), prev_conj.end() );
    }
  }
  if( success ){
    //make remainder : strip out conditions in conj
    Assert( !conj.empty() );
    std::vector< Node > cond_c;
    for( unsigned i=0; i<curr_conj.size(); i++ ){
      if( std::find( conj.begin(), conj.end(), curr_conj[i] )==conj.end() ){
        cond_c.push_back( curr_conj[i] );
      }
    }
    if( cond_c.empty() ){
      rem = isAnd ? tval : rem;
    }else{
      Node new_cond = cond_c.size()==1 ? cond_c[0] : NodeManager::currentNM()->mkNode( n_ite[0].getKind(), cond_c );
      rem = NodeManager::currentNM()->mkNode( ITE, new_cond, isAnd ? tval : rem, isAnd ? rem : tval );
    }
    return true;
  }else{
    return false;
  }
}

Node CegConjectureSingleInv::flattenITEs( Node n, bool rec ) {
  if( n.getKind()==ITE ){
    Trace("csi-simp-debug") << "Flatten ITE : " << n << std::endl;
    Node ret;
    Node n0 = rec ? flattenITEs( n[0] ) : n[0];
    Node n1 = rec ? flattenITEs( n[1] ) : n[1];
    Node n2 = rec ? flattenITEs( n[2] ) : n[2];
    if( n0.getKind()==NOT ){
      ret = NodeManager::currentNM()->mkNode( ITE, n0[0], n2, n1 );
    }else if( n0.getKind()==AND || n0.getKind()==OR ){
      std::vector< Node > children;
      for( unsigned i=1; i<n0.getNumChildren(); i++ ){
        children.push_back( n0[i] );
      }
      Node rem = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( n0.getKind(), children );
      Node ret;
      if( n0.getKind()==AND ){
        ret = NodeManager::currentNM()->mkNode( ITE, rem, NodeManager::currentNM()->mkNode( n0[0], n1, n2 ), n2 );
      }else{
        ret = NodeManager::currentNM()->mkNode( ITE, rem, n1, NodeManager::currentNM()->mkNode( n0[0], n1, n2 ) );
      }
    }else{
      if( n0.getKind()==ITE ){
        n0 = NodeManager::currentNM()->mkNode( OR, NodeManager::currentNM()->mkNode( AND, n0, n1 ),
                                                   NodeManager::currentNM()->mkNode( AND, n0.negate(), n2 ) );
      }else if( n0.getKind()==IFF ){
        n0 = NodeManager::currentNM()->mkNode( OR, NodeManager::currentNM()->mkNode( AND, n0, n1 ),
                                                   NodeManager::currentNM()->mkNode( AND, n0.negate(), n1.negate() ) );
      }else{
        return NodeManager::currentNM()->mkNode( ITE, n0, n1, n2 );
      }
      ret = NodeManager::currentNM()->mkNode( ITE, n0, n1, n2 );
    }
    return flattenITEs( ret, false );
  }else{
    if( n.getNumChildren()>0 ){
      std::vector< Node > children;
      bool childChanged = false;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node nc = flattenITEs( n[i] );
        children.push_back( nc );
        childChanged = childChanged || nc!=n[i];
      }
      if( !childChanged ){
        return n;
      }else{
        return NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }else{
      return n;
    }
  }
}

// assign is from literals to booleans
// union_find is from args to values

bool CegConjectureSingleInv::getAssign( QuantifiersEngine * qe, bool pol, Node n, std::map< Node, bool >& assign, std::vector< Node >& new_assign, std::vector< Node >& vars,
                                        std::vector< Node >& new_vars, std::vector< Node >& new_subs, std::vector< Node >& args ) {
  std::map< Node, bool >::iterator ita = assign.find( n );
  if( ita!=assign.end() ){
    Trace("csi-simp-debug") << "---already assigned, lookup " << pol << " " << ita->second << std::endl;
    return pol==ita->second;
  }else{
    Trace("csi-simp-debug") << "---assign " << n << " " << pol << std::endl;
    assign[n] = pol;
    new_assign.push_back( n );
    if( ( pol && n.getKind()==AND ) || ( !pol && n.getKind()==OR ) ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( !getAssign( qe, pol, n[i], assign, new_assign, vars, new_vars, new_subs, args ) ){
          return false;
        }
      }
    }else if( n.getKind()==NOT ){
      return getAssign( qe, !pol, n[0], assign, new_assign, vars, new_vars, new_subs, args );
    }else if( pol && ( n.getKind()==IFF || n.getKind()==EQUAL ) ){
      getAssignEquality( qe, n, vars, new_vars, new_subs, args );
    }
  }
  return true;
}

bool CegConjectureSingleInv::getAssignEquality( QuantifiersEngine * qe, Node eq,
                                                std::vector< Node >& vars, std::vector< Node >& new_vars, std::vector< Node >& new_subs, std::vector< Node >& args ) {
  Assert( eq.getKind()==IFF || eq.getKind()==EQUAL );
  //try to find valid argument
  for( unsigned r=0; r<2; r++ ){
    if( std::find( args.begin(), args.end(), eq[r] )!=args.end() ){
      Assert( std::find( vars.begin(), vars.end(), eq[r] )==vars.end() );
      if( std::find( new_vars.begin(), new_vars.end(), eq[r] )==new_vars.end() ){
        Node eqro = eq[r==0 ? 1 : 0 ];
        if( !qe->getTermDatabase()->containsTerm( eqro, eq[r] ) ){
          Trace("csi-simp-debug") << "---equality " << eq[r] << " = " << eqro << std::endl;
          new_vars.push_back( eq[r] );
          new_subs.push_back( eqro );
          return true;
        }
      }
    }
  }
  /*
  TypeNode tn = eq[0].getType();
  if( tn.isInteger() || tn.isReal() ){
    std::map< Node, Node > msum;
    if( QuantArith::getMonomialSumLit( eq, msum ) ){

    }
  }
  */
  return false;
}

Node CegConjectureSingleInv::simplifySolution( QuantifiersEngine * qe, Node sol, std::map< Node, bool >& assign,
                                               std::vector< Node >& vars, std::vector< Node >& subs, std::vector< Node >& args, int status ) {
  Assert( vars.size()==subs.size() );
  std::map< Node, bool >::iterator ita = assign.find( sol );
  if( ita!=assign.end() ){
    return NodeManager::currentNM()->mkConst( ita->second );
  }else{
    if( sol.getKind()==ITE ){
      Trace("csi-simp") << "Simplify ITE " << std::endl;
      std::vector< Node > children;
      for( unsigned r=1; r<=2; r++ ){
        std::vector< Node > new_assign;
        std::vector< Node > new_vars;
        std::vector< Node > new_subs;
        if( getAssign( qe, r==1, sol[0], assign, new_assign, vars, new_vars, new_subs, args ) ){
          Trace("csi-simp") << "- branch " << r << " led to " << new_assign.size() << " assignments, " << new_vars.size() << " equalities." << std::endl;
          unsigned prev_size = vars.size();
          Node nc = sol[r];
          if( !new_vars.empty() ){
            nc = nc.substitute( new_vars.begin(), new_vars.end(), new_subs.begin(), new_subs.end() );
            vars.insert( vars.end(), new_vars.begin(), new_vars.end() );
            subs.insert( subs.end(), new_subs.begin(), new_subs.end() );
          }
          nc = simplifySolution( qe, nc, assign, vars, subs, args, 0 );
          children.push_back( nc );
          //clean up substitution
          if( !new_vars.empty() ){
            vars.resize( prev_size );
            subs.resize( prev_size );
          }
        }else{
          Trace("csi-simp") << "- branch " << r << " of " << sol[0] << " is infeasible." << std::endl;
        }
        //clean up assignment
        for( unsigned i=0; i<new_assign.size(); i++ ){
          assign.erase( new_assign[i] );
        }
      }
      if( children.size()==1 || ( children.size()==2 && children[0]==children[1] ) ){
        return children[0];
      }else{
        Assert( children.size()==2 );
        Node ncond = simplifySolution( qe, sol[0], assign, vars, subs, args, 0 );
        return NodeManager::currentNM()->mkNode( ITE, ncond, children[0], children[1] );
      }
    }else if( sol.getKind()==OR || sol.getKind()==AND ){
      Trace("csi-simp") << "Simplify " << sol.getKind() << std::endl;
      //collect new equalities
      std::map< Node, bool > atoms;
      std::vector< Node > inc;
      std::vector< Node > children;
      std::vector< Node > new_vars;
      std::vector< Node > new_subs;
      Node bc = sol.getKind()==OR ? qe->getTermDatabase()->d_true : qe->getTermDatabase()->d_false;
      for( unsigned i=0; i<sol.getNumChildren(); i++ ){
        bool do_exc = false;
        Node c = sol[i];
        Trace("csi-simp") << "  - child " << i << " : " << c << std::endl;
        if( c.isConst() ){
          if( c==bc ){
            Trace("csi-simp") << "  ...singularity." << std::endl;
            return bc;
          }else{
            do_exc = true;
          }
        }else{
          Node atom = c.getKind()==NOT ? c[0] : c;
          bool pol = c.getKind()!=NOT;
          std::map< Node, bool >::iterator it = atoms.find( atom );
          if( it==atoms.end() ){
            atoms[atom] = pol;
            if( status==0 && ( atom.getKind()==IFF || atom.getKind()==EQUAL ) && ( pol==( sol.getKind()==AND ) ) ){
              Trace("csi-simp") << "  ...equality." << std::endl;
              if( getAssignEquality( qe, atom, vars, new_vars, new_subs, args ) ){
                children.push_back( sol[i] );
                do_exc = true;
              }
            }
          }else{
            //repeated atom
            if( it->second!=pol ){
              return NodeManager::currentNM()->mkConst( sol.getKind()==OR );
            }else{
              do_exc = true;
            }
          }
        }
        if( !do_exc ){
          inc.push_back( sol[i] );
        }else{
          Trace("csi-simp") << "  ...exclude." << std::endl;
        }
      }
      if( !new_vars.empty() ){
        if( !inc.empty() ){
          Node ret = inc.size()==1 ? sol[0] : NodeManager::currentNM()->mkNode( sol.getKind(), inc );
          Trace("csi-simp") << "Base return is : " << ret << std::endl;
          // apply substitution
          ret = ret.substitute( new_vars.begin(), new_vars.end(), new_subs.begin(), new_subs.end() );
          ret = Rewriter::rewrite( ret );
          Trace("csi-simp") << "After substitution : " << ret << std::endl;
          unsigned prev_size = vars.size();
          vars.insert( vars.end(), new_vars.begin(), new_vars.end() );
          subs.insert( subs.end(), new_subs.begin(), new_subs.end() );
          ret = simplifySolution( qe, ret, assign, vars, subs, args, 1 );
          //clean up substitution
          if( !vars.empty() ){
            vars.resize( prev_size );
            subs.resize( prev_size );
          }
          //Trace("csi-simp") << "After simplification : " << ret << std::endl;
          if( ret.getKind()==sol.getKind() ){
            for( unsigned i=0; i<ret.getNumChildren(); i++ ){
              children.push_back( ret[i] );
            }
          }else{
            children.push_back( ret );
          }
        }
      }else{
        //recurse on children
        for( unsigned i=0; i<inc.size(); i++ ){
          Node retc = simplifySolution( qe, inc[i], assign, vars, subs, args, 0 );
          if( retc.isConst() ){
            if( retc==bc ){
              return bc;
            }
          }else{
            children.push_back( retc );
          }
        }
      }
      return children.size()==0 ? NodeManager::currentNM()->mkConst( sol.getKind()==AND ) : ( children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( sol.getKind(), children ) );
    }else{
      //generic simplification
      std::vector< Node > children;
      if( sol.getMetaKind() == kind::metakind::PARAMETERIZED ){
        children.push_back( sol.getOperator() );
      }
      bool childChanged = false;
      for( unsigned i=0; i<sol.getNumChildren(); i++ ){
        Node nc = simplifySolution( qe, sol[i], assign, vars, subs, args, 0 );
        childChanged = childChanged || nc!=sol[i];
        children.push_back( nc );
      }
      if( childChanged ){
        return NodeManager::currentNM()->mkNode( sol.getKind(), children );
      }
    }
    return sol;
  }
}


void CegConjectureSingleInv::collectReconstructNodes( TermDbSygus * tds, Node t, TypeNode stn, Node parent, TypeNode pstn, bool ignoreBoolean ) {
  if( ignoreBoolean && t.getType().isBoolean() ){
    if( t.getKind()==OR || t.getKind()==AND || t.getKind()==IFF || t.getKind()==ITE || t.getKind()==NOT ){ //FIXME
      for( unsigned i=0; i<t.getNumChildren(); i++ ){
        collectReconstructNodes( tds, t[i], stn, parent, pstn, ignoreBoolean );
      }
      return;
    }
  }
  if( std::find( d_rcons_processed[t].begin(), d_rcons_processed[t].end(), stn )==d_rcons_processed[t].end() ){
    TypeNode tn = t.getType();
    d_rcons_processed[t].push_back( stn );
    Assert( datatypes::DatatypesRewriter::isTypeDatatype( stn ) );
    const Datatype& dt = ((DatatypeType)(stn).toType()).getDatatype();
    Assert( dt.isSygus() );
    Trace("cegqi-si-rcons-debug") << "Check reconstruct " << t << " type " << tn << ", sygus type " << dt.getName() << std::endl;
    tds->registerSygusType( stn );
    int arg = tds->getKindArg( stn, t.getKind() );
    bool processed = false;
    if( arg!=-1 ){
      if( t.getNumChildren()==dt[arg].getNumArgs() ){
        Trace("cegqi-si-rcons-debug") << "  Type has kind " << t.getKind() << ", recurse." << std::endl;
        for( unsigned i=0; i<t.getNumChildren(); i++ ){
          bool ignB = ( i==0 && t.getKind()==ITE );
          TypeNode stnc = tds->getArgType( dt[arg], i );
          collectReconstructNodes( tds, t[i], stnc, t, stn, ignB );
        }
        d_reconstructed[t][stn] = Node::fromExpr( dt[arg].getSygusOp() );
        d_reconstructed_op[t][stn] = true;
        processed = true;
      }else{
        Trace("cegqi-si-rcons-debug") << "  Type has kind " << t.getKind() << ", but argument mismatch, with parent " << parent << std::endl;
      }
    }
    int carg = tds->getConstArg( stn, t );
    if( carg==-1 ){
      Trace("cegqi-si-rcons") << "...Reconstruction needed for " << t << " sygus type " << dt.getName() << " with parent " << parent << std::endl;
    }else{
      d_reconstructed[t][stn] = Node::fromExpr( dt[carg].getSygusOp() );
      d_reconstructed_op[t][stn] = false;
      processed = true;
      Trace("cegqi-si-rcons-debug") << "  Type has constant." << std::endl;
    }
    //add to parent if necessary
    if( !parent.isNull() && ( !processed || !d_rcons_graph[0][t][stn].empty() ) ){
      Assert( !pstn.isNull() );
      d_rcons_graph[0][parent][pstn][t][stn] = true;
      d_rcons_to_process[pstn][parent] = true;
      d_rcons_graph[1][t][stn][parent][pstn] = true;
      d_rcons_to_process[stn][t] = true;
    }
  }
}

void CegConjectureSingleInv::setReconstructed( Node t, TypeNode stn ) {
  if( Trace.isOn("cegqi-si-rcons-debug") ){
    const Datatype& dt = ((DatatypeType)(stn).toType()).getDatatype();
    Trace("cegqi-si-rcons-debug") << "set rcons : " << t << " in syntax " << dt.getName() << std::endl;
  }
  // clear all children, d_rcons_parents
  std::vector< Node > to_set;
  std::vector< TypeNode > to_set_tn;
  for( unsigned r=0; r<2; r++){
    unsigned ro = r==0 ? 1 : 0;
    for( std::map< Node, std::map< TypeNode, bool > >::iterator it = d_rcons_graph[r][t][stn].begin(); it != d_rcons_graph[r][t][stn].end(); ++it ){
      TypeNode stnc;
      for( std::map< TypeNode, bool >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
        stnc = it2->first;
        d_rcons_graph[ro][it->first][stnc][t].erase( stn );
        if( d_rcons_graph[ro][it->first][stnc][t].empty() ){
          d_rcons_graph[ro][it->first][stnc].erase( t );
        }else{
          Trace("cegqi-si-rcons-debug") << "  " << ( r==0 ? "child" : "parent" ) << " " << it->first << " now has " << d_rcons_graph[ro][it->first][stnc][t].size() << std::endl;
        }
      }
      if( d_rcons_graph[ro][it->first][stnc].empty() ){
        to_set.push_back( it->first );
        to_set_tn.push_back( stnc );
      }
    }
  }
  for( unsigned r=0; r<2; r++){
    d_rcons_graph[r].erase( t );
  }
  d_rcons_to_process[stn].erase( t );
  for( unsigned i=0; i<to_set.size(); i++ ){
    setReconstructed( to_set[i], to_set_tn[i] );
  }
}

Node CegConjectureSingleInv::getReconstructedSolution( TypeNode stn, Node t ) {
  std::map< TypeNode, Node >::iterator it = d_reconstructed[t].find( stn );
  if( it!=d_reconstructed[t].end() ){
    if( d_reconstructed_op[t][stn] ){
      std::vector< Node > children;
      children.push_back( it->second );
      for( unsigned i=0; i<t.getNumChildren(); i++ ){
        Node nc = getReconstructedSolution( stn, t[i] );
        children.push_back( nc );
      }
      return NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, children );
    }else{
      return it->second;
    }
  }else{
    Trace("cegqi-si-rcons-debug") << "*** error : missing reconstruction for " << t << std::endl;
    Assert( false );
    return Node::null();
  }
}



}