/*********************                                                        */
/*! \file ce_guided_single_inv_sol.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing single invocation synthesis conjectures
 **
 **/
#include "theory/quantifiers/sygus/ce_guided_single_inv_sol.h"

#include "expr/datatype.h"
#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/ce_guided_single_inv.h"
#include "theory/quantifiers/sygus/synth_engine.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

bool doCompare(Node a, Node b, Kind k)
{
  Node com = NodeManager::currentNM()->mkNode(k, a, b);
  com = Rewriter::rewrite(com);
  Assert(com.getType().isBoolean());
  return com.isConst() && com.getConst<bool>();
}

CegSingleInvSol::CegSingleInvSol(QuantifiersEngine* qe)
    : d_qe(qe), d_id_count(0), d_root_id()
{
}

bool CegSingleInvSol::debugSolution(Node sol)
{
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

void CegSingleInvSol::debugTermSize(Node sol, int& t_size, int& num_ite)
{
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

void CegSingleInvSol::preregisterConjecture(Node q)
{
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

Node CegSingleInvSol::reconstructSolution(Node sol,
                                          TypeNode stn,
                                          int& reconstructed,
                                          int enumLimit)
{
  Trace("csi-rcons") << "Solution (pre-reconstruction) is : " << sol << std::endl;
  int status;
  d_root_id = collectReconstructNodes( sol, stn, status );
  if( status==0 ){
    Node ret = getReconstructedSolution( d_root_id );
    Trace("csi-rcons") << "Sygus solution is : " << ret << std::endl;
    Assert(!ret.isNull());
    reconstructed = 1;
    return ret;
  }
  if (Trace.isOn("csi-rcons"))
  {
    for (std::map<TypeNode, std::map<Node, int> >::iterator it =
             d_rcons_to_id.begin();
         it != d_rcons_to_id.end();
         ++it)
    {
      TypeNode tn = it->first;
      Assert(tn.isDatatype());
      const DType& dt = tn.getDType();
      Trace("csi-rcons") << "Terms to reconstruct of type " << dt.getName()
                         << " : " << std::endl;
      for (std::map<Node, int>::iterator it2 = it->second.begin();
           it2 != it->second.end();
           ++it2)
      {
        if (d_reconstruct.find(it2->second) == d_reconstruct.end())
        {
          Trace("csi-rcons") << "  " << it2->first << std::endl;
        }
      }
      Assert(!it->second.empty());
    }
  }
  if (enumLimit != 0)
  {
    int index = 0;
    std::map< TypeNode, bool > active;
    for( std::map< TypeNode, std::map< Node, int > >::iterator it = d_rcons_to_id.begin(); it != d_rcons_to_id.end(); ++it ){
      active[it->first] = true;
    }
    //enumerate for all types
    do {
      std::vector< TypeNode > to_erase;
      for( std::map< TypeNode, bool >::iterator it = active.begin(); it != active.end(); ++it ){
        TypeNode tn = it->first;
        Node ns = d_qe->getTermEnumeration()->getEnumerateTerm(tn, index);
        if( ns.isNull() ){
          to_erase.push_back(tn);
        }else{
          Node nb = d_qe->getTermDatabaseSygus()->sygusToBuiltin(ns, tn);
          Node nr = Rewriter::rewrite(nb);  // d_qe->getTermDatabaseSygus()->getNormalized(
                                            // tn, nb, false, false );
          Trace("csi-rcons-debug2")
              << "  - try " << ns << " -> " << nr << " for " << tn << " "
              << nr.getKind() << std::endl;
          std::map<Node, int>::iterator itt = d_rcons_to_id[tn].find(nr);
          if (itt != d_rcons_to_id[tn].end())
          {
            // if it is not already reconstructed
            if (d_reconstruct.find(itt->second) == d_reconstruct.end())
            {
              Trace("csi-rcons") << "...reconstructed " << ns << " for term "
                                 << nr << std::endl;
              setReconstructed(itt->second, ns);
              Trace("csi-rcons-debug")
                  << "...path to root, try reconstruction." << std::endl;
              d_tmp_fail.clear();
              Node ret = getReconstructedSolution(d_root_id);
              if (!ret.isNull())
              {
                Trace("csi-rcons")
                    << "Sygus solution (after enumeration) is : " << ret
                    << std::endl;
                reconstructed = 1;
                return ret;
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
    } while (!active.empty() && (enumLimit < 0 || index < enumLimit));
  }

  // we ran out of elements, return null
  reconstructed = -1;
  Warning() << CommandFailure(
      "Cannot get synth function: reconstruction to syntax failed.");
  // could return sol here, however, we choose to fail by returning null, since
  // it indicates a failure.
  return Node::null();
}

int CegSingleInvSol::collectReconstructNodes(Node t, TypeNode stn, int& status)
{
  std::map< Node, int >::iterator itri = d_rcons_to_status[stn].find( t );
  if( itri!=d_rcons_to_status[stn].end() ){
    status = itri->second;
    //Trace("csi-rcons-debug") << "-> (cached) " << status << " for " << d_rcons_to_id[stn][t] << std::endl;
    return d_rcons_to_id[stn][t];
  }else{
    status = 1;
    // register the type
    registerType(stn);
    int id = allocate( t, stn );
    d_rcons_to_status[stn][t] = -1;
    TypeNode tn = t.getType();
    Assert(stn.isDatatype());
    const DType& dt = stn.getDType();
    TermDbSygus* tds = d_qe->getTermDatabaseSygus();
    SygusTypeInfo& sti = tds->getTypeInfo(stn);
    Assert(dt.isSygus());
    Trace("csi-rcons-debug") << "Check reconstruct " << t << ", sygus type " << dt.getName() << ", kind " << t.getKind() << ", id : " << id << std::endl;
    int carg = -1;
    int karg = -1;
    // first, do standard minimizations
    Node min_t = minimizeBuiltinTerm(t);
    Trace("csi-rcons-debug") << "Minimized term is : " << min_t << std::endl;
    //check if op is in syntax sort

    carg = sti.getOpConsNum(min_t);
    if( carg!=-1 ){
      Trace("csi-rcons-debug") << "  Type has operator." << std::endl;
      d_reconstruct[id] = NodeManager::currentNM()->mkNode(
          APPLY_CONSTRUCTOR, dt[carg].getConstructor());
      status = 0;
    }else{
      //check if kind is in syntax sort
      karg = sti.getKindConsNum(min_t.getKind());
      if( karg!=-1 ){
        //collect the children of min_t
        std::vector< Node > tchildren;
        if( min_t.getNumChildren()>dt[karg].getNumArgs() && quantifiers::TermUtil::isAssoc( min_t.getKind() ) && dt[karg].getNumArgs()==2 ){
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
          Node cons = dt[karg].getConstructor();
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
          Node min_t_c = builtinToSygusConst(min_t, stn);
          if( !min_t_c.isNull() ){
            Trace("csi-rcons-debug") << "   constant reconstruction success for " << id << ", result = " << min_t_c << std::endl;
            d_reconstruct[id] = min_t_c;
            status = 0;
          }
        }
        if( status!=0 ){
          //try identity functions
          for (unsigned ii : d_id_funcs[stn])
          {
            Assert(dt[ii].getNumArgs() == 1);
            //try to directly reconstruct from single argument
            std::vector< Node > tchildren;
            tchildren.push_back( min_t );
            TypeNode stnc = dt[ii][0].getRangeType();
            Trace("csi-rcons-debug") << "...try identity function " << dt[ii].getSygusOp() << ", child type is " << stnc << std::endl;
            status = 0;
            Node cons = dt[ii].getConstructor();
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
              if (getMatch(min_t, stn, index_found, args, karg, c_index))
              {
                success = true;
                status = 0;
                Node cons = dt[index_found].getConstructor();
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
                    if( curr.getKind()==EQUAL ){
                      if( curr[0].getType().isInteger() || curr[0].getType().isReal() ){
                        new_t = NodeManager::currentNM()->mkNode( AND, NodeManager::currentNM()->mkNode( LEQ, curr[0], curr[1] ),
                                                                      NodeManager::currentNM()->mkNode( LEQ, curr[1], curr[0] ) );
                      }else if( curr[0].getType().isBoolean() ){
                        new_t = NodeManager::currentNM()->mkNode( OR, NodeManager::currentNM()->mkNode( AND, curr[0], curr[1] ),
                                                                      NodeManager::currentNM()->mkNode( AND, curr[0].negate(), curr[1].negate() ) );
                      }else{
                        new_t = NodeManager::currentNM()->mkNode( NOT, NodeManager::currentNM()->mkNode( NOT, curr ) );
                      }
                    }else if( curr.getKind()==ITE ){
                      new_t = NodeManager::currentNM()->mkNode( OR, NodeManager::currentNM()->mkNode( AND, curr[0], curr[1] ),
                                                                    NodeManager::currentNM()->mkNode( AND, curr[0].negate(), curr[2] ) );
                    }else if( curr.getKind()==OR || curr.getKind()==AND ){
                      new_t = TermUtil::simpleNegate( curr ).negate();
                    }else if( curr.getKind()==NOT ){
                      new_t = TermUtil::simpleNegate( curr[0] );
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
                  Kind k = sti.getConsNumKind(i);
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
                      Assert(!rsol.isNull());
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

bool CegSingleInvSol::collectReconstructNodes(int pid,
                                              std::vector<Node>& ts,
                                              const DTypeConstructor& dtc,
                                              std::vector<int>& ids,
                                              int& status)
{
  Assert(dtc.getNumArgs() == ts.size());
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

Node CegSingleInvSol::CegSingleInvSol::getReconstructedSolution(int id,
                                                                bool mod_eq)
{
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

int CegSingleInvSol::allocate(Node n, TypeNode stn)
{
  std::map< Node, int >::iterator it = d_rcons_to_id[stn].find( n );
  if( it==d_rcons_to_id[stn].end() ){
    int ret = d_id_count;
    if( Trace.isOn("csi-rcons-debug") ){
      const DType& dt = stn.getDType();
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

bool CegSingleInvSol::getPathToRoot(int id)
{
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

void CegSingleInvSol::setReconstructed(int id, Node n)
{
  //set all equivalent to this as reconstructed
  int rid = d_rep[id];
  for( unsigned i=0; i<d_eqc[rid].size(); i++ ){
    d_reconstruct[d_eqc[rid][i]] = n;
  }
}

void CegSingleInvSol::getEquivalentTerms(Kind k,
                                         Node n,
                                         std::vector<Node>& equiv)
{
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
          if( eq!=d_qe->getTermUtil()->d_true ){
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

void CegSingleInvSol::registerEquivalentTerms(Node n)
{
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

Node CegSingleInvSol::builtinToSygusConst(Node c, TypeNode tn, int rcons_depth)
{
  std::map<Node, Node>::iterator it = d_builtin_const_to_sygus[tn].find(c);
  if (it != d_builtin_const_to_sygus[tn].end())
  {
    return it->second;
  }
  TermDbSygus* tds = d_qe->getTermDatabaseSygus();
  NodeManager* nm = NodeManager::currentNM();
  SygusTypeInfo& ti = tds->getTypeInfo(tn);
  Node sc;
  d_builtin_const_to_sygus[tn][c] = sc;
  Assert(c.isConst());
  if (!tn.isDatatype())
  {
    // if we've traversed to a builtin type, simply return c
    d_builtin_const_to_sygus[tn][c] = c;
    return c;
  }
  const DType& dt = tn.getDType();
  Trace("csi-rcons-debug") << "Try to reconstruct " << c << " in "
                           << dt.getName() << std::endl;
  if (!dt.isSygus())
  {
    // if we've traversed to a builtin datatype type, simply return c
    d_builtin_const_to_sygus[tn][c] = c;
    return c;
  }
  // if we are not interested in reconstructing constants, or the grammar allows
  // them, return a proxy
  if (!options::cegqiSingleInvReconstructConst() || dt.getSygusAllowConst())
  {
    sc = tds->getProxyVariable(tn, c);
  }
  else
  {
    int carg = ti.getOpConsNum(c);
    if (carg != -1)
    {
      sc = nm->mkNode(APPLY_CONSTRUCTOR, dt[carg].getConstructor());
    }
    else
    {
      // identity functions
      for (unsigned ii : d_id_funcs[tn])
      {
        Assert(dt[ii].getNumArgs() == 1);
        // try to directly reconstruct from single argument
        TypeNode tnc = tds->getArgType(dt[ii], 0);
        Trace("csi-rcons-debug")
            << "Based on id function " << dt[ii].getSygusOp()
            << ", try reconstructing " << c << " instead in " << tnc
            << std::endl;
        Node n = builtinToSygusConst(c, tnc, rcons_depth);
        if (!n.isNull())
        {
          sc = nm->mkNode(APPLY_CONSTRUCTOR, dt[ii].getConstructor(), n);
          break;
        }
      }
      if (sc.isNull())
      {
        if (rcons_depth < 1000)
        {
          // accelerated, recursive reconstruction of constants
          Kind pk = getPlusKind(dt.getSygusType());
          if (pk != UNDEFINED_KIND)
          {
            int arg = ti.getKindConsNum(pk);
            if (arg != -1)
            {
              Kind ck = getComparisonKind(dt.getSygusType());
              Kind pkm = getPlusKind(dt.getSygusType(), true);
              // get types
              Assert(dt[arg].getNumArgs() == 2);
              TypeNode tn1 = tds->getArgType(dt[arg], 0);
              TypeNode tn2 = tds->getArgType(dt[arg], 1);
              // initialize d_const_list for tn1
              registerType(tn1);
              // iterate over all positive constants, largest to smallest
              int start = d_const_list[tn1].size() - 1;
              int end = d_const_list[tn1].size() - d_const_list_pos[tn1];
              for (int i = start; i >= end; --i)
              {
                Node c1 = d_const_list[tn1][i];
                // only consider if smaller than c, and
                if (doCompare(c1, c, ck))
                {
                  Node c2 = nm->mkNode(pkm, c, c1);
                  c2 = Rewriter::rewrite(c2);
                  if (c2.isConst())
                  {
                    // reconstruct constant on the other side
                    Node sc2 = builtinToSygusConst(c2, tn2, rcons_depth + 1);
                    if (!sc2.isNull())
                    {
                      Node sc1 = builtinToSygusConst(c1, tn1, rcons_depth);
                      Assert(!sc1.isNull());
                      sc = nm->mkNode(APPLY_CONSTRUCTOR,
                                      dt[arg].getConstructor(),
                                      sc1,
                                      sc2);
                      break;
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  d_builtin_const_to_sygus[tn][c] = sc;
  return sc;
}

struct sortConstants
{
  Kind d_comp_kind;
  bool operator()(Node i, Node j)
  {
    return i != j && doCompare(i, j, d_comp_kind);
  }
};

void CegSingleInvSol::registerType(TypeNode tn)
{
  if (d_const_list_pos.find(tn) != d_const_list_pos.end())
  {
    return;
  }
  d_const_list_pos[tn] = 0;
  Assert(tn.isDatatype());

  TermDbSygus* tds = d_qe->getTermDatabaseSygus();
  // ensure it is registered
  tds->registerSygusType(tn);
  const DType& dt = tn.getDType();
  Assert(dt.isSygus());
  TypeNode btn = dt.getSygusType();
  // for constant reconstruction
  Kind ck = getComparisonKind(btn);
  Node z = d_qe->getTermUtil()->getTypeValue(btn, 0);

  // iterate over constructors
  for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    Node n = dt[i].getSygusOp();
    if (n.getKind() != kind::BUILTIN && n.isConst())
    {
      d_const_list[tn].push_back(n);
      if (ck != UNDEFINED_KIND && doCompare(z, n, ck))
      {
        d_const_list_pos[tn]++;
      }
    }
    if (dt[i].isSygusIdFunc())
    {
      d_id_funcs[tn].push_back(i);
    }
  }
  // sort the constant list
  if (!d_const_list[tn].empty())
  {
    if (ck != UNDEFINED_KIND)
    {
      sortConstants sc;
      sc.d_comp_kind = ck;
      std::sort(d_const_list[tn].begin(), d_const_list[tn].end(), sc);
    }
    Trace("csi-rcons") << "Type has " << d_const_list[tn].size()
                       << " constants..." << std::endl
                       << "  ";
    for (unsigned i = 0; i < d_const_list[tn].size(); i++)
    {
      Trace("csi-rcons") << d_const_list[tn][i] << " ";
    }
    Trace("csi-rcons") << std::endl;
    Trace("csi-rcons") << "Of these, " << d_const_list_pos[tn]
                       << " are marked as positive." << std::endl;
  }
}

bool CegSingleInvSol::getMatch(Node p,
                               Node n,
                               std::map<int, Node>& s,
                               std::vector<int>& new_s)
{
  TermDbSygus* tds = d_qe->getTermDatabaseSygus();
  if (tds->isFreeVar(p))
  {
    size_t vnum = tds->getFreeVarId(p);
    Node prev = s[vnum];
    s[vnum] = n;
    if (prev.isNull())
    {
      new_s.push_back(vnum);
    }
    return prev.isNull() || prev == n;
  }
  if (n.getNumChildren() == 0)
  {
    return p == n;
  }
  if (n.getKind() == p.getKind() && n.getNumChildren() == p.getNumChildren())
  {
    // try both ways?
    unsigned rmax =
        TermUtil::isComm(n.getKind()) && n.getNumChildren() == 2 ? 2 : 1;
    std::vector<int> new_tmp;
    for (unsigned r = 0; r < rmax; r++)
    {
      bool success = true;
      for (unsigned i = 0, size = n.getNumChildren(); i < size; i++)
      {
        int io = r == 0 ? i : (i == 0 ? 1 : 0);
        if (!getMatch(p[i], n[io], s, new_tmp))
        {
          success = false;
          for (unsigned j = 0; j < new_tmp.size(); j++)
          {
            s.erase(new_tmp[j]);
          }
          new_tmp.clear();
          break;
        }
      }
      if (success)
      {
        new_s.insert(new_s.end(), new_tmp.begin(), new_tmp.end());
        return true;
      }
    }
  }
  return false;
}

bool CegSingleInvSol::getMatch(Node t,
                               TypeNode st,
                               int& index_found,
                               std::vector<Node>& args,
                               int index_exc,
                               int index_start)
{
  Assert(st.isDatatype());
  const DType& dt = st.getDType();
  Assert(dt.isSygus());
  std::map<Kind, std::vector<Node> > kgens;
  std::vector<Node> gens;
  for (unsigned i = index_start, ncons = dt.getNumConstructors(); i < ncons;
       i++)
  {
    if ((int)i != index_exc)
    {
      Node g = getGenericBase(st, dt, i);
      gens.push_back(g);
      kgens[g.getKind()].push_back(g);
      Trace("csi-sol-debug") << "Check generic base : " << g << " from "
                             << dt[i].getName() << std::endl;
      if (g.getKind() == t.getKind())
      {
        Trace("csi-sol-debug") << "Possible match ? " << g << " " << t
                               << " for " << dt[i].getName() << std::endl;
        std::map<int, Node> sigma;
        std::vector<int> new_s;
        if (getMatch(g, t, sigma, new_s))
        {
          // we found an exact match
          bool msuccess = true;
          for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
          {
            if (sigma[j].isNull())
            {
              msuccess = false;
              break;
            }
            else
            {
              args.push_back(sigma[j]);
            }
          }
          if (msuccess)
          {
            index_found = i;
            return true;
          }
        }
      }
    }
  }
  return false;
}

Node CegSingleInvSol::getGenericBase(TypeNode tn, const DType& dt, int c)
{
  std::map<int, Node>::iterator it = d_generic_base[tn].find(c);
  if (it != d_generic_base[tn].end())
  {
    return it->second;
  }
  TermDbSygus* tds = d_qe->getTermDatabaseSygus();
  Assert(tds->isRegistered(tn));
  Node g = tds->mkGeneric(dt, c);
  Trace("csi-sol-debug") << "Generic is " << g << std::endl;
  Node gr = Rewriter::rewrite(g);
  Trace("csi-sol-debug") << "Generic rewritten is " << gr << std::endl;
  d_generic_base[tn][c] = gr;
  return gr;
}

Node CegSingleInvSol::minimizeBuiltinTerm(Node n)
{
  Kind nk = n.getKind();
  if ((nk != EQUAL && nk != LEQ && nk != LT && nk != GEQ && nk != GT)
      || !n[0].getType().isReal())
  {
    return n;
  }
  NodeManager* nm = NodeManager::currentNM();
  bool changed = false;
  std::vector<Node> mon[2];
  for (unsigned r = 0; r < 2; r++)
  {
    unsigned ro = r == 0 ? 1 : 0;
    Node c;
    Node nc;
    if (n[r].getKind() == PLUS)
    {
      for (unsigned i = 0; i < n[r].getNumChildren(); i++)
      {
        if (ArithMSum::getMonomial(n[r][i], c, nc)
            && c.getConst<Rational>().isNegativeOne())
        {
          mon[ro].push_back(nc);
          changed = true;
        }
        else
        {
          if (!n[r][i].isConst() || !n[r][i].getConst<Rational>().isZero())
          {
            mon[r].push_back(n[r][i]);
          }
        }
      }
    }
    else
    {
      if (ArithMSum::getMonomial(n[r], c, nc)
          && c.getConst<Rational>().isNegativeOne())
      {
        mon[ro].push_back(nc);
        changed = true;
      }
      else
      {
        if (!n[r].isConst() || !n[r].getConst<Rational>().isZero())
        {
          mon[r].push_back(n[r]);
        }
      }
    }
  }
  if (changed)
  {
    Node nn[2];
    for (unsigned r = 0; r < 2; r++)
    {
      nn[r] = mon[r].size() == 0
                  ? nm->mkConst(Rational(0))
                  : (mon[r].size() == 1 ? mon[r][0] : nm->mkNode(PLUS, mon[r]));
    }
    return nm->mkNode(n.getKind(), nn[0], nn[1]);
  }
  return n;
}

Kind CegSingleInvSol::getComparisonKind(TypeNode tn)
{
  if (tn.isInteger() || tn.isReal())
  {
    return LT;
  }
  else if (tn.isBitVector())
  {
    return BITVECTOR_ULT;
  }
  return UNDEFINED_KIND;
}

Kind CegSingleInvSol::getPlusKind(TypeNode tn, bool is_neg)
{
  if (tn.isInteger() || tn.isReal())
  {
    return is_neg ? MINUS : PLUS;
  }
  else if (tn.isBitVector())
  {
    return is_neg ? BITVECTOR_SUB : BITVECTOR_PLUS;
  }
  return UNDEFINED_KIND;
}
}
}
}
