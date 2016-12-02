/*********************                                                        */
/*! \file ce_guided_single_inv_sol.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing single invocation synthesis conjectures
 **
 **/
#include "theory/quantifiers/ce_guided_single_inv_sol.h"

#include "expr/datatype.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/ce_guided_instantiation.h"
#include "theory/quantifiers/ce_guided_single_inv.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/trigger.h"
#include "theory/theory_engine.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace std;

namespace CVC4 {

CegConjectureSingleInvSol::CegConjectureSingleInvSol( QuantifiersEngine * qe ) : d_qe( qe ){
  d_id_count = 0;
}

bool CegConjectureSingleInvSol::debugSolution( Node sol ) {
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

void CegConjectureSingleInvSol::debugTermSize( Node sol, int& t_size, int& num_ite ) {
  std::map< Node, int >::iterator it = d_dterm_size.find( sol );
  if( it==d_dterm_size.end() ){
    int prev = t_size;
    int prev_ite = num_ite;
    t_size++;
    if( sol.getKind()==ITE ){
      num_ite++;
    }
    for( unsigned i=0; i<sol.getNumChildren(); i++ ){
      debugTermSize( sol[i], t_size, num_ite );
    }
    d_dterm_size[sol] = t_size-prev;
    d_dterm_ite_size[sol] = num_ite-prev_ite;
  }else{
    t_size += it->second;
    num_ite += d_dterm_ite_size[sol];
  }
}


Node CegConjectureSingleInvSol::pullITEs( Node s ) {
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
        Trace("csi-sol-debug") << "For " << s << ", can pull " << cond << " -> " << t << " with remainder " << rem << std::endl;
        t = pullITEs( t );
        rem = pullITEs( rem );
        Trace("csi-pull-ite") << "PI: Rewrite : " << s << std::endl;
        Node prev = s;
        s = NodeManager::currentNM()->mkNode( ITE, TermDb::simpleNegate( cond ), t, rem );
        Trace("csi-pull-ite") << "PI: Rewrite Now : " << s << std::endl;
        Trace("csi-pull-ite") << "(= " << prev << " " << s << ")" << std::endl;
        success = true;
      }
    }while( success );
  }
  return s;
}

// pull condition common to all ITE conditions in path of size > 1
bool CegConjectureSingleInvSol::pullITECondition( Node root, Node n_ite, std::vector< Node >& conj, Node& t, Node& rem, int depth ) {
  Assert( n_ite.getKind()==ITE );
  std::vector< Node > curr_conj;
  std::vector< Node > orig_conj;
  bool isAnd;
  if( n_ite[0].getKind()==AND || n_ite[0].getKind()==OR ){
    isAnd = n_ite[0].getKind()==AND;
    for( unsigned i=0; i<n_ite[0].getNumChildren(); i++ ){
      Node cond = n_ite[0][i];
      orig_conj.push_back( cond );
      if( n_ite[0].getKind()==OR ){
        cond = TermDb::simpleNegate( cond );
      }
      curr_conj.push_back( cond );
    }
  }else{
    Node neg = n_ite[0].negate();
    if( std::find( conj.begin(), conj.end(), neg )!=conj.end() ){
      //if negation of condition exists, use it
      isAnd = false;
      curr_conj.push_back( neg );
    }else{
      //otherwise, use condition
      isAnd = true;
      curr_conj.push_back( n_ite[0] );
    }
    orig_conj.push_back( n_ite[0] );
  }
  // take intersection with current conditions
  std::vector< Node > new_conj;
  std::vector< Node > prev_conj;
  if( n_ite==root ){
    new_conj.insert( new_conj.end(), curr_conj.begin(), curr_conj.end() );
    Trace("csi-sol-debug") << "Pull ITE root " << n_ite << ", #conj = " << new_conj.size() << std::endl;
  }else{
    for( unsigned i=0; i<curr_conj.size(); i++ ){
      if( std::find( conj.begin(), conj.end(), curr_conj[i] )!=conj.end() ){
        new_conj.push_back( curr_conj[i] );
      }
    }
    Trace("csi-sol-debug") << "Pull ITE " << n_ite << ", #conj = " << conj.size() << " intersect " << curr_conj.size() << " = " << new_conj.size() << std::endl;
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
    Assert( orig_conj.size()==curr_conj.size() );
    for( unsigned i=0; i<curr_conj.size(); i++ ){
      if( std::find( conj.begin(), conj.end(), curr_conj[i] )==conj.end() ){
        cond_c.push_back( orig_conj[i] );
      }
    }
    if( cond_c.empty() ){
      rem = tval;
    }else{
      Node new_cond = cond_c.size()==1 ? cond_c[0] : NodeManager::currentNM()->mkNode( n_ite[0].getKind(), cond_c );
      rem = NodeManager::currentNM()->mkNode( ITE, new_cond, isAnd ? tval : rem, isAnd ? rem : tval );
    }
    return true;
  }else{
    return false;
  }
}

Node CegConjectureSingleInvSol::flattenITEs( Node n, bool rec ) {
  Assert( !n.isNull() );
  if( n.getKind()==ITE ){
    Trace("csi-sol-debug") << "Flatten ITE." << std::endl;
    Node ret;
    Node n0 = rec ? flattenITEs( n[0] ) : n[0];
    Node n1 = rec ? flattenITEs( n[1] ) : n[1];
    Node n2 = rec ? flattenITEs( n[2] ) : n[2];
    Assert( !n0.isNull() );
    Assert( !n1.isNull() );
    Assert( !n2.isNull() );
    if( n0.getKind()==NOT ){
      ret = NodeManager::currentNM()->mkNode( ITE, n0[0], n2, n1 );
    }else if( n0.getKind()==AND || n0.getKind()==OR ){
      std::vector< Node > children;
      for( unsigned i=1; i<n0.getNumChildren(); i++ ){
        children.push_back( n0[i] );
      }
      Node rem = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( n0.getKind(), children );
      if( n0.getKind()==AND ){
        ret = NodeManager::currentNM()->mkNode( ITE, rem, NodeManager::currentNM()->mkNode( ITE, n0[0], n1, n2 ), n2 );
      }else{
        ret = NodeManager::currentNM()->mkNode( ITE, rem, n1, NodeManager::currentNM()->mkNode( ITE, n0[0], n1, n2 ) );
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
    Assert( !ret.isNull() );
    return flattenITEs( ret, false );
  }else{
    if( n.getNumChildren()>0 ){
      std::vector< Node > children;
      if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
        children.push_back( n.getOperator() );
      }
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

bool CegConjectureSingleInvSol::getAssign( bool pol, Node n, std::map< Node, bool >& assign, std::vector< Node >& new_assign, std::vector< Node >& vars,
                                        std::vector< Node >& new_vars, std::vector< Node >& new_subs ) {
  std::map< Node, bool >::iterator ita = assign.find( n );
  if( ita!=assign.end() ){
    Trace("csi-simp-debug") << "---already assigned, lookup " << pol << " " << ita->second << std::endl;
    return pol==ita->second;
  }else if( n.isConst() ){
    return pol==(n==d_qe->getTermDatabase()->d_true);
  }else{
    Trace("csi-simp-debug") << "---assign " << n << " " << pol << std::endl;
    assign[n] = pol;
    new_assign.push_back( n );
    if( ( pol && n.getKind()==AND ) || ( !pol && n.getKind()==OR ) ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( !getAssign( pol, n[i], assign, new_assign, vars, new_vars, new_subs ) ){
          return false;
        }
      }
    }else if( n.getKind()==NOT ){
      return getAssign( !pol, n[0], assign, new_assign, vars, new_vars, new_subs );
    }else if( pol && ( n.getKind()==IFF || n.getKind()==EQUAL ) ){
      getAssignEquality( n, vars, new_vars, new_subs );
    }
  }
  return true;
}

bool CegConjectureSingleInvSol::getAssignEquality( Node eq, std::vector< Node >& vars, std::vector< Node >& new_vars, std::vector< Node >& new_subs ) {
  Assert( eq.getKind()==IFF || eq.getKind()==EQUAL );
  //try to find valid argument
  for( unsigned r=0; r<2; r++ ){
    if( std::find( d_varList.begin(), d_varList.end(), eq[r] )!=d_varList.end() ){
      Assert( std::find( vars.begin(), vars.end(), eq[r] )==vars.end() );
      if( std::find( new_vars.begin(), new_vars.end(), eq[r] )==new_vars.end() ){
        Node eqro = eq[r==0 ? 1 : 0 ];
        if( !d_qe->getTermDatabase()->containsTerm( eqro, eq[r] ) ){
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

Node CegConjectureSingleInvSol::simplifySolution( Node sol, TypeNode stn ){
  int tsize, itesize;
  if( Trace.isOn("csi-sol") ){
    tsize = 0;itesize = 0;
    debugTermSize( sol, tsize, itesize );
    Trace("csi-sol") << tsize << " " << itesize << " rewrite..." << std::endl;
    Trace("csi-sol-debug") << "sol : " << sol << "..." << std::endl;
  }
  Node sol0 = Rewriter::rewrite( sol );
  Trace("csi-sol") << "now : " << sol0 << std::endl;

  Node curr_sol = sol0;
  Node prev_sol;
  do{
    prev_sol = curr_sol;
    //first, pull ITE conditions
    if( Trace.isOn("csi-sol") ){
      tsize = 0;itesize = 0;
      debugTermSize( curr_sol, tsize, itesize );
      Trace("csi-sol") << tsize << " " << itesize << " pull ITE..." << std::endl;
      Trace("csi-sol-debug") << "sol : " << curr_sol << "..." << std::endl;
    }
    Node sol1 = pullITEs( curr_sol );
    Trace("csi-sol") << "now : " << sol1 << std::endl;
    //do standard rewriting
    if( sol1!=curr_sol ){
      if( Trace.isOn("csi-sol") ){
        tsize = 0;itesize = 0;
        debugTermSize( sol1, tsize, itesize );
        Trace("csi-sol") << tsize << " " << itesize << " rewrite..." << std::endl;
        Trace("csi-sol-debug") << "sol : " << sol1 << "..." << std::endl;
      }
      Node sol2 = Rewriter::rewrite( sol1 );
      Trace("csi-sol") << "now : " << sol2 << std::endl;
      curr_sol = sol2;
    }
    //now do branch analysis
    if( Trace.isOn("csi-sol") ){
      tsize = 0;itesize = 0;
      debugTermSize( curr_sol, tsize, itesize );
      Trace("csi-sol") << tsize << " " << itesize << " simplify solution..." << std::endl;
      Trace("csi-sol-debug") << "sol : " << curr_sol << "..." << std::endl;
    }
    std::map< Node, bool > sassign;
    std::vector< Node > svars;
    std::vector< Node > ssubs;
    Node sol3 = simplifySolutionNode( curr_sol, stn, sassign, svars, ssubs, 0 );
    Trace("csi-sol") << "now : " << sol3 << std::endl;
    if( sol3!=curr_sol ){
      //do standard rewriting again
      if( Trace.isOn("csi-sol" ) ){
        tsize = 0;itesize = 0;
        debugTermSize( sol3, tsize, itesize );
        Trace("csi-sol") << tsize << " " << itesize << " rewrite..." << std::endl;
      }
      Node sol4 = Rewriter::rewrite( sol3 );
      Trace("csi-sol") << "now : " << sol4 << std::endl;
      curr_sol = sol4;
    }
  }while( curr_sol!=prev_sol );

  return curr_sol;
}

Node CegConjectureSingleInvSol::simplifySolutionNode( Node sol, TypeNode stn, std::map< Node, bool >& assign,
                                                      std::vector< Node >& vars, std::vector< Node >& subs, int status ) {

  Assert( vars.size()==subs.size() );
  std::map< Node, bool >::iterator ita = assign.find( sol );
  if( ita!=assign.end() ){
    //it is currently assigned a boolean value
    return NodeManager::currentNM()->mkConst( ita->second );
  }else{
    d_qe->getTermDatabaseSygus()->registerSygusType( stn );
    std::map< int, TypeNode > stnc;
    if( !stn.isNull() ){
      int karg = d_qe->getTermDatabaseSygus()->getKindArg( stn, sol.getKind() );
      if( karg!=-1 ){
        const Datatype& dt = ((DatatypeType)(stn).toType()).getDatatype();
        if( dt[karg].getNumArgs()==sol.getNumChildren() ){
          for( unsigned i=0; i<dt[karg].getNumArgs(); i++ ){
            stnc[i] = d_qe->getTermDatabaseSygus()->getArgType( dt[karg], i );
          }
        }
      }
    }

    if( sol.getKind()==ITE ){
      Trace("csi-simp") << "Simplify ITE " << std::endl;
      std::vector< Node > children;
      for( unsigned r=1; r<=2; r++ ){
        std::vector< Node > new_assign;
        std::vector< Node > new_vars;
        std::vector< Node > new_subs;
        if( getAssign( r==1, sol[0], assign, new_assign, vars, new_vars, new_subs ) ){
          Trace("csi-simp") << "- branch " << r << " led to " << new_assign.size() << " assignments, " << new_vars.size() << " equalities." << std::endl;
          unsigned prev_size = vars.size();
          Node nc = sol[r];
          if( !new_vars.empty() ){
            nc = nc.substitute( new_vars.begin(), new_vars.end(), new_subs.begin(), new_subs.end() );
            vars.insert( vars.end(), new_vars.begin(), new_vars.end() );
            subs.insert( subs.end(), new_subs.begin(), new_subs.end() );
          }
          nc = simplifySolutionNode( nc, stnc[r], assign, vars, subs, 0 );
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
        Node ncond = simplifySolutionNode( sol[0], stnc[0], assign, vars, subs, 0 );
        Node ret = NodeManager::currentNM()->mkNode( ITE, ncond, children[0], children[1] );

        //expand/flatten if necessary
        Node orig_ret = ret;
        if( !stnc[0].isNull() ){
          d_qe->getTermDatabaseSygus()->registerSygusType( stnc[0] );
          Node prev_ret;
          while( !d_qe->getTermDatabaseSygus()->hasKind( stnc[0], ret[0].getKind() ) && ret!=prev_ret ){
            prev_ret = ret;
            Node exp_c = d_qe->getTermDatabaseSygus()->expandBuiltinTerm( ret[0] );
            if( !exp_c.isNull() ){
              Trace("csi-simp-debug") << "Pre expand to " << ret[0] << " to " << exp_c << std::endl;
              ret = NodeManager::currentNM()->mkNode( ITE, exp_c, ret[1], ret[2] );
            }
            if( !d_qe->getTermDatabaseSygus()->hasKind( stnc[0], ret[0].getKind() ) ){
              Trace("csi-simp-debug") << "Flatten based on " << ret[0] << "." << std::endl;
              ret = flattenITEs( ret, false );
            }
          }
        }
        return ret;
        /*
        if( orig_ret!=ret ){
          Trace("csi-simp") << "Try expanded ITE" << std::endl;
          return ret;//simplifySolutionNode( ret, stn, assign, vars, subs, status );
        }else{
          return ret;
        }
        */
      }
    }else if( sol.getKind()==OR || sol.getKind()==AND ){
      Trace("csi-simp") << "Simplify " << sol.getKind() << std::endl;
      //collect new equalities
      std::map< Node, bool > atoms;
      std::vector< Node > inc;
      std::vector< Node > children;
      std::vector< Node > new_vars;
      std::vector< Node > new_subs;
      Node bc = sol.getKind()==OR ? d_qe->getTermDatabase()->d_true : d_qe->getTermDatabase()->d_false;
      for( unsigned i=0; i<sol.getNumChildren(); i++ ){
        bool do_exc = false;
        Node c;
        std::map< Node, bool >::iterator ita = assign.find( sol[i] );
        if( ita==assign.end() ){
          c = sol[i];
        }else{
          c = NodeManager::currentNM()->mkConst( ita->second );
        }
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
            if( status==0 && ( atom.getKind()==IFF || atom.getKind()==EQUAL ) ){
              if( pol==( sol.getKind()==AND ) ){
                Trace("csi-simp") << "  ...equality." << std::endl;
                if( getAssignEquality( atom, vars, new_vars, new_subs ) ){
                  children.push_back( sol[i] );
                  do_exc = true;
                }
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
          Node ret = inc.size()==1 ? inc[0] : NodeManager::currentNM()->mkNode( sol.getKind(), inc );
          Trace("csi-simp") << "Base return is : " << ret << std::endl;
          // apply substitution
          ret = ret.substitute( new_vars.begin(), new_vars.end(), new_subs.begin(), new_subs.end() );
          ret = Rewriter::rewrite( ret );
          Trace("csi-simp") << "After substitution : " << ret << std::endl;
          unsigned prev_size = vars.size();
          vars.insert( vars.end(), new_vars.begin(), new_vars.end() );
          subs.insert( subs.end(), new_subs.begin(), new_subs.end() );
          ret = simplifySolutionNode( ret, TypeNode::null(), assign, vars, subs, 1 );
          //clean up substitution
          if( !vars.empty() ){
            vars.resize( prev_size );
            subs.resize( prev_size );
          }
          //Trace("csi-simp") << "After simplification : " << ret << std::endl;
          if( ret.isConst() ){
            if( ret==bc ){
              return bc;
            }
          }else{
            if( ret.getKind()==sol.getKind() ){
              for( unsigned i=0; i<ret.getNumChildren(); i++ ){
                children.push_back( ret[i] );
              }
            }else{
              children.push_back( ret );
            }
          }
        }
      }else{
        //recurse on children
        for( unsigned i=0; i<inc.size(); i++ ){
          Node retc = simplifySolutionNode( inc[i], TypeNode::null(), assign, vars, subs, 0 );
          if( retc.isConst() ){
            if( retc==bc ){
              return bc;
            }
          }else{
            children.push_back( retc );
          }
        }
      }
      // now, remove all equalities that are implied
      std::vector< Node > final_children;
      for( unsigned i=0; i<children.size(); i++ ){
        bool red = false;
        Node atom = children[i].getKind()==NOT ? children[i][0] : children[i];
        bool pol = children[i].getKind()!=NOT;
        if( status==0 && ( atom.getKind()==IFF || atom.getKind()==EQUAL ) ){
          if( pol!=( sol.getKind()==AND ) ){
            std::vector< Node > tmp_vars;
            std::vector< Node > tmp_subs;
            if( getAssignEquality( atom, vars, tmp_vars, tmp_subs ) ){
              Trace("csi-simp-debug") << "Check if " << children[i] << " is redundant in " << sol << std::endl;
              for( unsigned j=0; j<children.size(); j++ ){
                if( j!=i && ( j>i || std::find( final_children.begin(), final_children.end(), children[j] )!=final_children.end() ) ){
                  Node sj = children[j].substitute( tmp_vars.begin(), tmp_vars.end(), tmp_subs.begin(), tmp_subs.end() );
                  sj = Rewriter::rewrite( sj );
                  if( sj==( sol.getKind()==AND ? d_qe->getTermDatabase()->d_false : d_qe->getTermDatabase()->d_true ) ){
                    Trace("csi-simp") << "--- " << children[i].negate() << " is implied by " << children[j].negate() << std::endl;
                    red = true;
                    break;
                  }
                }
              }
              if( !red ){
                Trace("csi-simp-debug") << "...is not." << std::endl;
              }
            }
          }
        }
        if( !red ){
          final_children.push_back( children[i] );
        }
      }
      return final_children.size()==0 ? NodeManager::currentNM()->mkConst( sol.getKind()==AND ) :
             ( final_children.size()==1 ? final_children[0] : NodeManager::currentNM()->mkNode( sol.getKind(), final_children ) );
    }else{
      //generic simplification
      std::vector< Node > children;
      if( sol.getMetaKind() == kind::metakind::PARAMETERIZED ){
        children.push_back( sol.getOperator() );
      }
      bool childChanged = false;
      for( unsigned i=0; i<sol.getNumChildren(); i++ ){
        Node nc = simplifySolutionNode( sol[i], stnc[i], assign, vars, subs, 0 );
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


void CegConjectureSingleInvSol::preregisterConjecture( Node q ) {
  Trace("csi-sol") << "Preregister conjecture : " << q << std::endl;
  Node n = q;
  if( n.getKind()==FORALL ){
    n = n[1];
  }
  if( n.getKind()==EXISTS ){
    if( n[0].getNumChildren()==d_varList.size() ){
      std::vector< Node > evars;
      for( unsigned i=0; i<n[0].getNumChildren(); i++ ){
        evars.push_back( n[0][i] );
      }
      n = n[1].substitute( evars.begin(), evars.end(), d_varList.begin(), d_varList.end() );
    }else{
      Trace("csi-sol") << "Not the same number of variables, return." << std::endl;
      return;
    }
  }
  Trace("csi-sol") << "Preregister node for solution reconstruction : " << n << std::endl;
  registerEquivalentTerms( n );
}

Node CegConjectureSingleInvSol::reconstructSolution( Node sol, TypeNode stn, int& reconstructed ) {
  Trace("csi-rcons") << "Solution (pre-reconstruction) is : " << sol << std::endl;
  int status;
  d_root_id = collectReconstructNodes( sol, stn, status );
  if( status==0 ){
    Node ret = getReconstructedSolution( d_root_id );
    Trace("csi-rcons") << "Sygus solution is : " << ret << std::endl;
    Assert( !ret.isNull() );
    reconstructed = 1;
    return ret;
  }else{
    //Trace("csi-debug-sol") << "Induced solution template is : " << d_templ_solution << std::endl;
    if( Trace.isOn("csi-rcons") ){
      for( std::map< TypeNode, std::map< Node, int > >::iterator it = d_rcons_to_id.begin(); it != d_rcons_to_id.end(); ++it ){
        TypeNode tn = it->first;
        Assert( tn.isDatatype() );
        const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
        Trace("csi-rcons") << "Terms to reconstruct of type " << dt.getName() << " : " << std::endl;
        for( std::map< Node, int >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
          if( d_reconstruct.find( it2->second )==d_reconstruct.end() ){
            Trace("csi-rcons") << "  " << it2->first << std::endl;
          }
        }
        Assert( !it->second.empty() );
      }
    }
    unsigned index = 0;
    std::map< TypeNode, bool > active;
    for( std::map< TypeNode, std::map< Node, int > >::iterator it = d_rcons_to_id.begin(); it != d_rcons_to_id.end(); ++it ){
      active[it->first] = true;
    }
    //enumerate for all types
    do {
      std::vector< TypeNode > to_erase;
      for( std::map< TypeNode, bool >::iterator it = active.begin(); it != active.end(); ++it ){
        TypeNode stn = it->first;
        Node ns = d_qe->getTermDatabase()->getEnumerateTerm( stn, index );
        if( ns.isNull() ){
          to_erase.push_back( stn );
        }else{
          Node nb = d_qe->getTermDatabaseSygus()->sygusToBuiltin( ns, stn );
          Node nr = Rewriter::rewrite( nb );//d_qe->getTermDatabaseSygus()->getNormalized( stn, nb, false, false );
          Trace("csi-rcons-debug2") << "  - try " << ns << " -> " << nr << " for " << stn << " " << nr.getKind() << std::endl;
          std::map< Node, int >::iterator itt = d_rcons_to_id[stn].find( nr );
          if( itt!= d_rcons_to_id[stn].end() ){
            // if it is not already reconstructed
            if( d_reconstruct.find( itt->second )==d_reconstruct.end() ){
              Trace("csi-rcons") << "...reconstructed " << ns << " for term " << nr << std::endl;
              bool do_check = true;//getPathToRoot( itt->second );
              setReconstructed( itt->second, ns );
              if( do_check ){
                Trace("csi-rcons-debug") << "...path to root, try reconstruction." << std::endl;
                d_tmp_fail.clear();
                Node ret = getReconstructedSolution( d_root_id );
                if( !ret.isNull() ){
                  Trace("csi-rcons") << "Sygus solution (after enumeration) is : " << ret << std::endl;
                  reconstructed = 1;
                  return ret;
                }
              }else{
                Trace("csi-rcons-debug") << "...no path to root." << std::endl;
              }
            }
          }
        }
      }
      for( unsigned i=0; i<to_erase.size(); i++ ){
        active.erase( to_erase[i] );
      }
      index++;
      if( index%100==0 ){
        Trace("csi-rcons-stats") << "Tried " << index << " for each type."  << std::endl;
      }
    }while( !active.empty() );

    //if solution is null, we ran out of elements, return the original solution
    return sol;
  }
}

int CegConjectureSingleInvSol::collectReconstructNodes( Node t, TypeNode stn, int& status ) {
  std::map< Node, int >::iterator itri = d_rcons_to_status[stn].find( t );
  if( itri!=d_rcons_to_status[stn].end() ){
    status = itri->second;
    //Trace("csi-rcons-debug") << "-> (cached) " << status << " for " << d_rcons_to_id[stn][t] << std::endl;
    return d_rcons_to_id[stn][t];
  }else{
    status = 1;
    d_qe->getTermDatabaseSygus()->registerSygusType( stn );
    int id = allocate( t, stn );
    d_rcons_to_status[stn][t] = -1;
    TypeNode tn = t.getType();
    Assert( stn.isDatatype() );
    const Datatype& dt = ((DatatypeType)(stn).toType()).getDatatype();
    Assert( dt.isSygus() );
    Trace("csi-rcons-debug") << "Check reconstruct " << t << ", sygus type " << dt.getName() << ", kind " << t.getKind() << ", id : " << id << std::endl;
    int carg = -1;
    int karg = -1;
    // first, do standard minimizations
    Node min_t = d_qe->getTermDatabaseSygus()->minimizeBuiltinTerm( t );
    Trace("csi-rcons-debug") << "Minimized term is : " << min_t << std::endl;
    //check if op is in syntax sort
    carg = d_qe->getTermDatabaseSygus()->getOpArg( stn, min_t );
    if( carg!=-1 ){
      Trace("csi-rcons-debug") << "  Type has operator." << std::endl;
      d_reconstruct[id] = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, Node::fromExpr( dt[carg].getConstructor() ) );
      status = 0;
    }else{
      //check if kind is in syntax sort
      karg = d_qe->getTermDatabaseSygus()->getKindArg( stn, min_t.getKind() );
      if( karg!=-1 ){
        //collect the children of min_t
        std::vector< Node > tchildren;
        if( min_t.getNumChildren()>dt[karg].getNumArgs() && quantifiers::TermDb::isAssoc( min_t.getKind() ) && dt[karg].getNumArgs()==2 ){
          tchildren.push_back( min_t[0] );
          std::vector< Node > rem_children;
          for( unsigned i=1; i<min_t.getNumChildren(); i++ ){
            rem_children.push_back( min_t[i] );
          }
          Node t2 = NodeManager::currentNM()->mkNode( min_t.getKind(), rem_children );
          tchildren.push_back( t2 );
          Trace("csi-rcons-debug") << "...split n-ary to binary " << min_t[0] << " " << t2 << "." << std::endl;
        }else{
          for( unsigned i=0; i<min_t.getNumChildren(); i++ ){
            tchildren.push_back( min_t[i] );
          }
        }
        //recurse on the children
        if( tchildren.size()==dt[karg].getNumArgs() ){
          Trace("csi-rcons-debug") << "Type for " << id << " has kind " << min_t.getKind() << ", recurse." << std::endl;
          status = 0;
          Node cons = Node::fromExpr( dt[karg].getConstructor() );
          if( !collectReconstructNodes( id, tchildren, dt[karg], d_reconstruct_op[id][cons], status ) ){
            Trace("csi-rcons-debug") << "...failure for " << id << " " << dt[karg].getName() << std::endl;
            d_reconstruct_op[id].erase( cons );
            status = 1;
          }
        }else{
          Trace("csi-rcons-debug") << "Type for " << id << " has kind " << min_t.getKind() << ", but argument # mismatch." << std::endl;
        }
      }
      if( status!=0 ){
        //try constant reconstruction
        if( min_t.isConst() ){
          Trace("csi-rcons-debug") << "...try constant reconstruction." << std::endl;
          Node min_t_c = d_qe->getTermDatabaseSygus()->builtinToSygusConst( min_t, stn );
          if( !min_t_c.isNull() ){
            Trace("csi-rcons-debug") << "   constant reconstruction success for " << id << ", result = " << min_t_c << std::endl;
            d_reconstruct[id] = min_t_c;
            status = 0;
          }
        }
        if( status!=0 ){
          //try identity functions
          for( unsigned i=0; i<d_qe->getTermDatabaseSygus()->getNumIdFuncs( stn ); i++ ){
            unsigned ii = d_qe->getTermDatabaseSygus()->getIdFuncIndex( stn, i );
            Assert( dt[ii].getNumArgs()==1 );
            //try to directly reconstruct from single argument
            std::vector< Node > tchildren;
            tchildren.push_back( min_t );
            TypeNode stnc = TypeNode::fromType( ((SelectorType)dt[ii][0].getType()).getRangeType() );
            Trace("csi-rcons-debug") << "...try identity function " << dt[ii].getSygusOp() << ", child type is " << stnc << std::endl;
            status = 0;
            Node cons = Node::fromExpr( dt[ii].getConstructor() );
            if( !collectReconstructNodes( id, tchildren, dt[ii], d_reconstruct_op[id][cons], status ) ){
              d_reconstruct_op[id].erase( cons );
              status = 1;
            }else{
              Trace("csi-rcons-debug") << "   identity function success for " << id << std::endl;
              break;
            }
          }
          if( status!=0 ){
            //try other options, such as matching against other constructors
            Trace("csi-rcons-debug") << "Try matching for " << id << "." << std::endl;
            bool success;
            int c_index = 0;
            do{
              success = false;
              int index_found;
              std::vector< Node > args;
              if( d_qe->getTermDatabaseSygus()->getMatch( min_t, stn, index_found, args, karg, c_index ) ){
                success = true;
                status = 0;
                Node cons = Node::fromExpr( dt[index_found].getConstructor() );
                Trace("csi-rcons-debug") << "Try alternative for " << id << ", matching " << dt[index_found].getName() << " with children : " << std::endl;
                for( unsigned i=0; i<args.size(); i++ ){
                  Trace("csi-rcons-debug") << "  " << args[i] << std::endl;
                }
                if( !collectReconstructNodes( id, args, dt[index_found], d_reconstruct_op[id][cons], status ) ){
                  d_reconstruct_op[id].erase( cons );
                  status = 1;
                }else{
                  c_index = index_found+1;
                }
              }
            }while( success && status!=0 );

            if( status!=0 ){
              // construct an equivalence class of terms that are equivalent to t
              if( d_rep[id]==id ){
                Trace("csi-rcons-debug") << "Try rewriting for " << id << "." << std::endl;
                //get equivalence class of term
                std::vector< Node > equiv;
                if( tn.isBoolean() ){
                  Node curr = min_t;
                  Node new_t;
                  do{
                    new_t = Node::null();
                    if( curr.getKind()==EQUAL && ( curr[0].getType().isInteger() || curr[0].getType().isReal() ) ){
                      new_t = NodeManager::currentNM()->mkNode( AND, NodeManager::currentNM()->mkNode( LEQ, curr[0], curr[1] ),
                                                                    NodeManager::currentNM()->mkNode( LEQ, curr[1], curr[0] ) );
                    }else if( curr.getKind()==ITE ){
                      new_t = NodeManager::currentNM()->mkNode( OR, NodeManager::currentNM()->mkNode( AND, curr[0], curr[1] ),
                                                                    NodeManager::currentNM()->mkNode( AND, curr[0].negate(), curr[2] ) );
                    }else if( curr.getKind()==IFF ){
                      new_t = NodeManager::currentNM()->mkNode( OR, NodeManager::currentNM()->mkNode( AND, curr[0], curr[1] ),
                                                                    NodeManager::currentNM()->mkNode( AND, curr[0].negate(), curr[1].negate() ) );
                    }else if( curr.getKind()==OR || curr.getKind()==AND ){
                      new_t = TermDb::simpleNegate( curr ).negate();
                    }else if( curr.getKind()==NOT ){
                      new_t = TermDb::simpleNegate( curr[0] );
                    }else{
                      new_t = NodeManager::currentNM()->mkNode( NOT, NodeManager::currentNM()->mkNode( NOT, curr ) );
                    }
                    if( !new_t.isNull() ){
                      if( new_t!=min_t && std::find( equiv.begin(), equiv.end(), new_t )==equiv.end() ){
                        curr = new_t;
                        equiv.push_back( new_t );
                      }else{
                        new_t = Node::null();
                      }
                    }
                  }while( !new_t.isNull() );
                }
                //get decompositions
                for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
                  Kind k = d_qe->getTermDatabaseSygus()->getArgKind( stn, i );
                  getEquivalentTerms( k, min_t, equiv );
                }
                //assign ids to terms
                Trace("csi-rcons-debug") << "Term " << id << " is equivalent to " << equiv.size() << " terms : " << std::endl;
                std::vector< int > equiv_ids;
                for( unsigned i=0; i<equiv.size(); i++ ){
                  Trace("csi-rcons-debug") << "  " << equiv[i] << std::endl;
                  if( d_rcons_to_id[stn].find( equiv[i] )==d_rcons_to_id[stn].end() ){
                    int eq_id = allocate( equiv[i], stn );
                    d_eqc.erase( eq_id );
                    d_rep[eq_id] = id;
                    d_eqc[id].push_back( eq_id );
                    equiv_ids.push_back( eq_id );
                  }else{
                    equiv_ids.push_back( -1 );
                  }
                }
                // now, try each of them
                for( unsigned i=0; i<equiv.size(); i++ ){
                  if( equiv_ids[i]!=-1 ){
                    collectReconstructNodes( equiv[i], stn, status );
                    //if one succeeds
                    if( status==0 ){
                      Node rsol = getReconstructedSolution( equiv_ids[i] );
                      Assert( !rsol.isNull() );
                      //set all members of the equivalence class that this is the reconstructed solution
                      setReconstructed( id, rsol );
                      break;
                    }
                  }
                }
              }else{
                Trace("csi-rcons-debug") << "Do not try rewriting for " << id << ", rep = " << d_rep[id] << std::endl;
              }
            }
          }
        }
      }
    }
    if( status!=0 ){
      Trace("csi-rcons-debug") << "-> *** reconstruction required for id " << id << std::endl;
    }else{
      Trace("csi-rcons-debug") << "-> success for " << id << std::endl;
    }
    d_rcons_to_status[stn][t] = status;
    return id;
  }
}

bool CegConjectureSingleInvSol::collectReconstructNodes( int pid, std::vector< Node >& ts, const DatatypeConstructor& dtc, std::vector< int >& ids, int& status ) {
  Assert( dtc.getNumArgs()==ts.size() );
  for( unsigned i=0; i<ts.size(); i++ ){
    TypeNode cstn = d_qe->getTermDatabaseSygus()->getArgType( dtc, i );
    int cstatus;
    int c_id = collectReconstructNodes( ts[i], cstn, cstatus );
    if( cstatus==-1 ){
      return false;
    }else if( cstatus!=0 ){
      status = 1;
    }
    ids.push_back( c_id );
  }
  for( unsigned i=0; i<ids.size(); i++ ){
    d_parents[ids[i]].push_back( pid );
  }
  return true;
}

  /*
  //flatten ITEs if necessary  TODO : carry assignment or move this elsewhere
  if( t.getKind()==ITE ){
    TypeNode cstn = tds->getArgType( dt[karg], 0 );
    tds->registerSygusType( cstn );
    Node prev_t;
    while( !tds->hasKind( cstn, t[0].getKind() ) && t!=prev_t ){
      prev_t = t;
      Node exp_c = tds->expandBuiltinTerm( t[0] );
      if( !exp_c.isNull() ){
        t = NodeManager::currentNM()->mkNode( ITE, exp_c, t[1], t[2] );
        Trace("csi-rcons-debug") << "Pre expand to " << t << std::endl;
      }
      t = flattenITEs( t, false );
      if( t!=prev_t ){
        Trace("csi-rcons-debug") << "Flatten ITE to " << t << std::endl;
        std::map< Node, bool > sassign;
        std::vector< Node > svars;
        std::vector< Node > ssubs;
        t = simplifySolutionNode( t, sassign, svars, ssubs, 0 );
      }
      Assert( t.getKind()==ITE );
    }
  }
  */


Node CegConjectureSingleInvSol::CegConjectureSingleInvSol::getReconstructedSolution( int id, bool mod_eq ) {
  std::map< int, Node >::iterator it = d_reconstruct.find( id );
  if( it!=d_reconstruct.end() ){
    return it->second;
  }else{
    if( std::find( d_tmp_fail.begin(), d_tmp_fail.end(), id )!=d_tmp_fail.end() ){
      return Node::null();
    }else{
      // try each child option
      std::map< int, std::map< Node, std::vector< int > > >::iterator ito = d_reconstruct_op.find( id );
      if( ito!=d_reconstruct_op.end() ){
        for( std::map< Node, std::vector< int > >::iterator itt = ito->second.begin(); itt != ito->second.end(); ++itt ){
          std::vector< Node > children;
          children.push_back( itt->first );
          bool success = true;
          for( unsigned i=0; i<itt->second.size(); i++ ){
            Node nc = getReconstructedSolution( itt->second[i] );
            if( nc.isNull() ){
              success = false;
              break;
            }else{
              children.push_back( nc );
            }
          }
          if( success ){
            Node ret = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, children );
            setReconstructed( id, ret );
            return ret;
          }
        }
      }
      // try terms in the equivalence class of this
      if( mod_eq ){
        int rid = d_rep[id];
        for( unsigned i=0; i<d_eqc[rid].size(); i++ ){
          int tid = d_eqc[rid][i];
          if( tid!=id ){
            Node eret = getReconstructedSolution( tid, false );
            if( !eret.isNull() ){
              setReconstructed( id, eret );
              return eret;
            }
          }
        }
      }
      d_tmp_fail.push_back( id );
      return Node::null();
    }
  }
}

int CegConjectureSingleInvSol::allocate( Node n, TypeNode stn ) {
  std::map< Node, int >::iterator it = d_rcons_to_id[stn].find( n );
  if( it==d_rcons_to_id[stn].end() ){
    int ret = d_id_count;
    if( Trace.isOn("csi-rcons-debug") ){
      const Datatype& dt = ((DatatypeType)(stn).toType()).getDatatype();
      Trace("csi-rcons-debug") << "id " << ret << " : " << n << " " <<  dt.getName() << std::endl;
    }
    d_id_node[d_id_count] = n;
    d_id_type[d_id_count] = stn;
    d_rep[d_id_count] = d_id_count;
    d_eqc[d_id_count].push_back( d_id_count );
    d_rcons_to_id[stn][n] = d_id_count;
    d_id_count++;
    return ret;
  }else{
    return it->second;
  }
}

bool CegConjectureSingleInvSol::getPathToRoot( int id ) {
  if( id==d_root_id ){
    return true;
  }else{
    std::map< int, Node >::iterator it = d_reconstruct.find( id );
    if( it!=d_reconstruct.end() ){
      return false;
    }else{
      int rid = d_rep[id];
      for( unsigned j=0; j<d_parents[rid].size(); j++ ){
        if( getPathToRoot( d_parents[rid][j] ) ){
          return true;
        }
      }
      return false;
    }
  }
}

void CegConjectureSingleInvSol::setReconstructed( int id, Node n ) {
  //set all equivalent to this as reconstructed
  int rid = d_rep[id];
  for( unsigned i=0; i<d_eqc[rid].size(); i++ ){
    d_reconstruct[d_eqc[rid][i]] = n;
  }
}

void CegConjectureSingleInvSol::getEquivalentTerms( Kind k, Node n, std::vector< Node >& equiv ) {
  Assert( n.getKind()!=k ); //?
  if( k==AND || k==OR ){
    equiv.push_back( NodeManager::currentNM()->mkNode( k, n, n ) );
    equiv.push_back( NodeManager::currentNM()->mkNode( k, n, NodeManager::currentNM()->mkConst( k==AND ) ) );
  }
  //multiplication for integers
  //TODO for bitvectors
  Kind mk = ( k==PLUS || k==MINUS ) ? MULT : UNDEFINED_KIND;
  if( mk!=UNDEFINED_KIND ){
    if( n.getKind()==mk && n[0].isConst() && n[0].getType().isInteger() ){
      bool success = true;
      for( unsigned i=0; i<2; i++ ){
        Node eq;
        if( k==PLUS || k==MINUS ){
          Node oth = NodeManager::currentNM()->mkConst( Rational(i==0 ? 1000 : -1000) );
          eq = i==0 ? NodeManager::currentNM()->mkNode( LEQ, n[0], oth ) : NodeManager::currentNM()->mkNode( GEQ, n[0], oth );
        }
        if( !eq.isNull() ){
          eq = Rewriter::rewrite( eq );
          if( eq!=d_qe->getTermDatabase()->d_true ){
            success = false;
            break;
          }
        }
      }
      if( success ){
        Node var = n[1];
        Node rem;
        if( k==PLUS || k==MINUS ){
          int rem_coeff = (int)n[0].getConst<Rational>().getNumerator().getSignedInt();
          if( rem_coeff>0 && k==PLUS ){
            rem_coeff--;
          }else if( rem_coeff<0 && k==MINUS ){
            rem_coeff++;
          }else{
            success = false;
          }
          if( success ){
            rem = NodeManager::currentNM()->mkNode( MULT, NodeManager::currentNM()->mkConst( Rational(rem_coeff) ), var );
            rem = Rewriter::rewrite( rem );
          }
        }
        if( !rem.isNull() ){
          equiv.push_back( NodeManager::currentNM()->mkNode( k, rem, var ) );
        }
      }
    }
  }
  //negative constants
  if( k==MINUS ){
    if( n.isConst() && n.getType().isInteger() && n.getConst<Rational>().getNumerator().strictlyNegative() ){
      Node nn = NodeManager::currentNM()->mkNode( UMINUS, n );
      nn = Rewriter::rewrite( nn );
      equiv.push_back( NodeManager::currentNM()->mkNode( MINUS, NodeManager::currentNM()->mkConst( Rational(0) ), nn ) );
    }
  }
  //inequalities
  if( k==GEQ || k==LEQ || k==LT || k==GT || k==NOT ){
    Node atom = n.getKind()==NOT ? n[0] : n;
    bool pol = n.getKind()!=NOT;
    Kind ak = atom.getKind();
    if( ( ak==GEQ || ak==LEQ || ak==LT || ak==GT ) && ( pol || k!=NOT ) ){
      Node t1 = atom[0];
      Node t2 = atom[1];
      if( !pol ){
        ak = ak==GEQ ? LT : ( ak==LEQ ? GT : ( ak==LT ? GEQ : LEQ ) );
      }
      if( k==NOT ){
        equiv.push_back( NodeManager::currentNM()->mkNode( ak==GEQ ? LT : ( ak==LEQ ? GT : ( ak==LT ? GEQ : LEQ ) ), t1, t2 ).negate() );
      }else if( k==ak ){
        equiv.push_back( NodeManager::currentNM()->mkNode( k, t1, t2 ) );
      }else if( (k==GEQ || k==LEQ)==(ak==GEQ || ak==LEQ) ){
        equiv.push_back( NodeManager::currentNM()->mkNode( k, t2, t1 ) );
      }else if( t1.getType().isInteger() && t2.getType().isInteger() ){
        if( (k==GEQ || k==GT)!=(ak==GEQ || ak==GT) ){
          Node ts = t1;
          t1 = t2;
          t2 = ts;
          ak = ak==GEQ ? LEQ : ( ak==LEQ ? GEQ : ( ak==LT ? GT : LT ) );
        }
        t2 = NodeManager::currentNM()->mkNode( PLUS, t2, NodeManager::currentNM()->mkConst( Rational( (ak==GT || ak==LEQ) ? 1 : -1 ) ) );
        t2 = Rewriter::rewrite( t2 );
        equiv.push_back( NodeManager::currentNM()->mkNode( k, t1, t2 ) );
      }
    }
  }

  //based on eqt cache
  std::map< Node, Node >::iterator itet = d_eqt_rep.find( n );
  if( itet!=d_eqt_rep.end() ){
    Node rn = itet->second;
    for( unsigned i=0; i<d_eqt_eqc[rn].size(); i++ ){
      if( d_eqt_eqc[rn][i]!=n && d_eqt_eqc[rn][i].getKind()==k ){
        if( std::find( equiv.begin(), equiv.end(), d_eqt_eqc[rn][i] )==equiv.end() ){
          equiv.push_back( d_eqt_eqc[rn][i] );
        }
      }
    }
  }
}

void CegConjectureSingleInvSol::registerEquivalentTerms( Node n ) {
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    registerEquivalentTerms( n[i] );
  }
  Node rn = Rewriter::rewrite( n );
  if( rn!=n ){
    Trace("csi-equiv") << "  eq terms : " << n << " " << rn << std::endl;
    d_eqt_rep[n] = rn;
    d_eqt_rep[rn] = rn;
    if( std::find( d_eqt_eqc[rn].begin(), d_eqt_eqc[rn].end(), rn )==d_eqt_eqc[rn].end() ){
      d_eqt_eqc[rn].push_back( rn );
    }
    if( std::find( d_eqt_eqc[rn].begin(), d_eqt_eqc[rn].end(), n )==d_eqt_eqc[rn].end() ){
      d_eqt_eqc[rn].push_back( n );
    }
  }
}

}
