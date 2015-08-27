/*********************                                                        */
/*! \file inst_strategy_cbqi.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of counterexample-guided quantifier instantiation strategies
 **/

#include "theory/quantifiers/inst_strategy_cbqi.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/theory_arith_private.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/first_order_model.h"
#include "util/ite_removal.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::theory::arith;

#define ARITH_INSTANTIATOR_USE_MINUS_DELTA
//#define MBP_STRICT_ASSERTIONS


CegInstantiator::CegInstantiator( QuantifiersEngine * qe, CegqiOutput * out, bool use_vts_delta, bool use_vts_inf ) :
d_qe( qe ), d_out( out ), d_use_vts_delta( use_vts_delta ), d_use_vts_inf( use_vts_inf ){
  d_zero = NodeManager::currentNM()->mkConst( Rational( 0 ) );
  d_one = NodeManager::currentNM()->mkConst( Rational( 1 ) );
  d_true = NodeManager::currentNM()->mkConst( true );
}

void CegInstantiator::computeProgVars( Node n ){
  if( d_prog_var.find( n )==d_prog_var.end() ){
    d_prog_var[n].clear();
    if( std::find( d_vars.begin(), d_vars.end(), n )!=d_vars.end() ){
      d_prog_var[n][n] = true;
    }else if( !d_out->isEligibleForInstantiation( n ) ){
      d_inelig[n] = true;
      return;
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      computeProgVars( n[i] );
      if( d_inelig.find( n[i] )!=d_inelig.end() ){
        d_inelig[n] = true;
        return;
      }
      for( std::map< Node, bool >::iterator it = d_prog_var[n[i]].begin(); it != d_prog_var[n[i]].end(); ++it ){
        d_prog_var[n][it->first] = true;
      }
    }
  }
}

bool CegInstantiator::addInstantiation( std::vector< Node >& subs, std::vector< Node >& vars,
                                        std::vector< Node >& coeff, std::vector< int >& btyp,
                                        std::vector< Node >& has_coeff, Node theta, unsigned i, unsigned effort ){
  if( i==d_vars.size() ){
    return addInstantiationCoeff( subs, vars, coeff, btyp, has_coeff, 0 );
  }else{
    std::map< Node, std::map< Node, bool > > subs_proc;
    //Node v = d_single_inv_map_to_prog[d_single_inv[0][i]];
    Node pv = d_vars[i];
    TypeNode pvtn = pv.getType();
    Trace("cbqi-inst-debug") << "[Find instantiation for " << pv << "]" << std::endl;
    Node pv_value;
    if( options::cbqiModel() ){
      pv_value = d_qe->getModel()->getValue( pv );
      Trace("cbqi-bound2") << "...M( " << pv << " ) = " << pv_value << std::endl;
    }

    //if in effort=2, we must choose at least one model value
    if( (i+1)<d_vars.size() || effort!=2 ){

      //[1] easy case : pv is in the equivalence class as another term not containing pv
      Trace("cbqi-inst-debug") << "[1] try based on equivalence class." << std::endl;
      std::map< Node, Node >::iterator itr = d_curr_rep.find( pv );
      if( itr!=d_curr_rep.end() ){
        std::map< Node, std::vector< Node > >::iterator it_eqc = d_curr_eqc.find( itr->second );
        Assert( it_eqc!=d_curr_eqc.end() );
        for( unsigned k=0; k<it_eqc->second.size(); k++ ){
          Node n = it_eqc->second[k];
          if( n!=pv ){
            Trace("cbqi-inst-debug") << "..[1] " << i << "...try based on equal term " << n << std::endl;
            //compute d_subs_fv, which program variables are contained in n
            computeProgVars( n );
            //must be an eligible term
            if( d_inelig.find( n )==d_inelig.end() ){
              Node ns;
              Node pv_coeff;  //coefficient of pv in the equality we solve (null is 1)
              bool proc = false;
              if( !d_prog_var[n].empty() ){
                ns = applySubstitution( n, subs, vars, coeff, has_coeff, pv_coeff, false );
                if( !ns.isNull() ){
                  computeProgVars( ns );
                  //substituted version must be new and cannot contain pv
                  proc = subs_proc[pv_coeff].find( ns )==subs_proc[pv_coeff].end() && d_prog_var[ns].find( pv )==d_prog_var[ns].end();
                }
              }else{
                ns = n;
                proc = true;
              }
              if( proc ){
                //try the substitution
                subs_proc[ns][pv_coeff] = true;
                if( addInstantiationInc( ns, pv, pv_coeff, 0, subs, vars, coeff, btyp, has_coeff, theta, i, effort ) ){
                  return true;
                }
              }
            }
          }
        }
      }

      //[2] : we can solve an equality for pv
      ///iterate over equivalence classes to find cases where we can solve for the variable
      if( pvtn.isInteger() || pvtn.isReal() ){
        Trace("cbqi-inst-debug") << "[2] try based on solving in arithmetic equivalence class." << std::endl;
        for( unsigned k=0; k<d_curr_arith_eqc.size(); k++ ){
          Node r = d_curr_arith_eqc[k];
          std::vector< Node > lhs;
          std::vector< bool > lhs_v;
          std::vector< Node > lhs_coeff;
          std::map< Node, std::vector< Node > >::iterator it_eqc = d_curr_eqc.find( r );
          Assert( it_eqc!=d_curr_eqc.end() );
          for( unsigned kk=0; kk<it_eqc->second.size(); kk++ ){
            Node n = it_eqc->second[kk];
            Trace("cbqi-inst-debug2") << "...look at term " << n << std::endl;
            //compute the variables in n
            computeProgVars( n );
            //must be an eligible term
            if( d_inelig.find( n )==d_inelig.end() ){
              Node ns;
              Node pv_coeff;
              if( !d_prog_var[n].empty() ){
                ns = applySubstitution( n, subs, vars, coeff, has_coeff, pv_coeff );
                if( !ns.isNull() ){
                  computeProgVars( ns );
                }
              }else{
                ns = n;
              }
              if( !ns.isNull() ){
                bool hasVar = d_prog_var[ns].find( pv )!=d_prog_var[ns].end();
                for( unsigned j=0; j<lhs.size(); j++ ){
                  //if this term or the another has pv in it, try to solve for it
                  if( hasVar || lhs_v[j] ){
                    Trace("cbqi-inst-debug") << "..[2] " << i << "...try based on equality " << lhs[j] << " = " << ns << std::endl;
                    Node eq_lhs = lhs[j];
                    Node eq_rhs = ns;
                    //make the same coefficient
                    if( pv_coeff!=lhs_coeff[j] ){
                      if( !pv_coeff.isNull() ){
                        Trace("cbqi-inst-debug") << "...mult lhs by " << pv_coeff << std::endl;
                        eq_lhs = NodeManager::currentNM()->mkNode( MULT, pv_coeff, eq_lhs );
                        eq_lhs = Rewriter::rewrite( eq_lhs );
                      }
                      if( !lhs_coeff[j].isNull() ){
                        Trace("cbqi-inst-debug") << "...mult rhs by " << lhs_coeff[j] << std::endl;
                        eq_rhs = NodeManager::currentNM()->mkNode( MULT, lhs_coeff[j], eq_rhs );
                        eq_rhs = Rewriter::rewrite( eq_rhs );
                      }
                    }
                    Node eq = eq_lhs.eqNode( eq_rhs );
                    eq = Rewriter::rewrite( eq );
                    //cannot contain infinity?
                    //if( !d_qe->getTermDatabase()->containsVtsInfinity( eq ) ){
                    Trace("cbqi-inst-debug") << "...equality is " << eq << std::endl;
                    std::map< Node, Node > msum;
                    if( QuantArith::getMonomialSumLit( eq, msum ) ){
                      if( Trace.isOn("cbqi-inst-debug") ){
                        Trace("cbqi-inst-debug") << "...got monomial sum: " << std::endl;
                        QuantArith::debugPrintMonomialSum( msum, "cbqi-inst-debug" );
                        Trace("cbqi-inst-debug") << "isolate for " << pv << "..." << std::endl;
                      }
                      Node veq;
                      if( QuantArith::isolate( pv, msum, veq, EQUAL, true )!=0 ){
                        Trace("cbqi-inst-debug") << "...isolated equality " << veq << "." << std::endl;
                        Node veq_c;
                        if( veq[0]!=pv ){
                          Node veq_v;
                          if( QuantArith::getMonomial( veq[0], veq_c, veq_v ) ){
                            Assert( veq_v==pv );
                          }
                        }
                        Node val = veq[1];
                        if( subs_proc[val].find( veq_c )==subs_proc[val].end() ){
                          subs_proc[val][veq_c] = true;
                          if( addInstantiationInc( val, pv, veq_c, 0, subs, vars, coeff, btyp, has_coeff, theta, i, effort ) ){
                            return true;
                          }
                        }
                      }
                    }
                  }
                }
                lhs.push_back( ns );
                lhs_v.push_back( hasVar );
                lhs_coeff.push_back( pv_coeff );
              }
            }
          }
        }
      }

      //[3] directly look at assertions
      Trace("cbqi-inst-debug") << "[3] try based on assertions." << std::endl;
      Node vts_sym[2];
      vts_sym[0] = d_qe->getTermDatabase()->getVtsInfinity( pvtn, false, false );
      vts_sym[1] = d_qe->getTermDatabase()->getVtsDelta( false, false );
      std::vector< Node > mbp_bounds[2];
      std::vector< Node > mbp_coeff[2];
      std::vector< Node > mbp_vts_coeff[2][2];
      std::vector< Node > mbp_lit[2];
      unsigned rmax = Theory::theoryOf( pv )==Theory::theoryOf( pv.getType() ) ? 1 : 2;
      for( unsigned r=0; r<rmax; r++ ){
        TheoryId tid = r==0 ? Theory::theoryOf( pv ) : Theory::theoryOf( pv.getType() );
        Trace("cbqi-inst-debug2") << "  look at assertions of " << tid << std::endl;
        std::map< TheoryId, std::vector< Node > >::iterator ita = d_curr_asserts.find( tid );
        if( ita!=d_curr_asserts.end() ){
          for (unsigned j = 0; j<ita->second.size(); j++) {
            Node lit = ita->second[j];
            Trace("cbqi-inst-debug2") << "  look at " << lit << std::endl;
            Node atom = lit.getKind()==NOT ? lit[0] : lit;
            bool pol = lit.getKind()!=NOT;
            //arithmetic inequalities and disequalities
            if( atom.getKind()==GEQ || ( atom.getKind()==EQUAL && !pol && ( atom[0].getType().isInteger() || atom[0].getType().isReal() ) ) ){
              Assert( atom.getKind()!=GEQ || atom[1].isConst() );
              Node atom_lhs;
              Node atom_rhs;
              if( atom.getKind()==GEQ ){
                atom_lhs = atom[0];
                atom_rhs = atom[1];
              }else{
                atom_lhs = NodeManager::currentNM()->mkNode( MINUS, atom[0], atom[1] );
                atom_lhs = Rewriter::rewrite( atom_lhs );
                atom_rhs = d_zero;
              }

              computeProgVars( atom_lhs );
              //must be an eligible term
              if( d_inelig.find( atom_lhs )==d_inelig.end() ){
                //apply substitution to LHS of atom
                if( !d_prog_var[atom_lhs].empty() ){
                  Node atom_lhs_coeff;
                  atom_lhs = applySubstitution( atom_lhs, subs, vars, coeff, has_coeff, atom_lhs_coeff );
                  if( !atom_lhs.isNull() ){
                    computeProgVars( atom_lhs );
                    if( !atom_lhs_coeff.isNull() ){
                      atom_rhs = Rewriter::rewrite( NodeManager::currentNM()->mkNode( MULT, atom_lhs_coeff, atom_rhs ) );
                    }
                  }
                }
                //if it contains pv, not infinity
                if( !atom_lhs.isNull() && d_prog_var[atom_lhs].find( pv )!=d_prog_var[atom_lhs].end() ){
                  Node satom = NodeManager::currentNM()->mkNode( atom.getKind(), atom_lhs, atom_rhs );
                  //cannot contain infinity?
                  //if( !d_qe->getTermDatabase()->containsVtsInfinity( atom_lhs ) ){
                  Trace("cbqi-inst-debug") << "..[3] From assertion : " << atom << ", pol = " << pol << std::endl;
                  Trace("cbqi-inst-debug") << "         substituted : " << satom << ", pol = " << pol << std::endl;
                  std::map< Node, Node > msum;
                  if( QuantArith::getMonomialSumLit( satom, msum ) ){
                    if( Trace.isOn("cbqi-inst-debug") ){
                      Trace("cbqi-inst-debug") << "...got monomial sum: " << std::endl;
                      QuantArith::debugPrintMonomialSum( msum, "cbqi-inst-debug" );
                    }
                    //get the coefficient of infinity and remove it from msum
                    Node vts_coeff[2];
                    for( unsigned t=0; t<2; t++ ){
                      if( !vts_sym[t].isNull() ){
                        std::map< Node, Node >::iterator itminf = msum.find( vts_sym[t] );
                        if( itminf!=msum.end() ){
                          vts_coeff[t] = itminf->second;
                          if( vts_coeff[t].isNull() ){
                            vts_coeff[t] = NodeManager::currentNM()->mkConst( Rational( 1 ) );
                          }
                          //negate if coefficient on variable is positive
                          std::map< Node, Node >::iterator itv = msum.find( pv );
                          if( itv!=msum.end() ){
                            //multiply by the coefficient we will isolate for
                            if( itv->second.isNull() ){
                              vts_coeff[t] = QuantArith::negate(vts_coeff[t]);
                            }else{
                              if( !pvtn.isInteger() ){
                                vts_coeff[t] = NodeManager::currentNM()->mkNode( MULT, NodeManager::currentNM()->mkConst( Rational(-1) / itv->second.getConst<Rational>() ), vts_coeff[t] );
                                vts_coeff[t] = Rewriter::rewrite( vts_coeff[t] );
                              }else if( itv->second.getConst<Rational>().sgn()==1 ){
                                vts_coeff[t] = QuantArith::negate(vts_coeff[t]);
                              }
                            }
                          }
                          Trace("cbqi-inst-debug") << "vts[" << t << "] coefficient is " << vts_coeff[t] << std::endl;
                          msum.erase( vts_sym[t] );
                        }
                      }
                    }

                    Trace("cbqi-inst-debug") << "isolate for " << pv << "..." << std::endl;
                    Node vatom;
                    //isolate pv in the inequality
                    int ires = QuantArith::isolate( pv, msum, vatom, atom.getKind(), true );
                    if( ires!=0 ){
                      Trace("cbqi-inst-debug") << "...isolated atom " << vatom << "." << std::endl;
                      Node val = vatom[ ires==1 ? 1 : 0 ];
                      Node pvm = vatom[ ires==1 ? 0 : 1 ];
                      //get monomial
                      Node veq_c;
                      if( pvm!=pv ){
                        Node veq_v;
                        if( QuantArith::getMonomial( pvm, veq_c, veq_v ) ){
                          Assert( veq_v==pv );
                        }
                      }

                      //disequalities are either strict upper or lower bounds
                      unsigned rmax = ( atom.getKind()==GEQ && options::cbqiModel() ) ? 1 : 2;
                      for( unsigned r=0; r<rmax; r++ ){
                        int uires = ires;
                        Node uval = val;
                        if( atom.getKind()==GEQ ){
                          //push negation downwards
                          if( !pol ){
                            uires = -ires;
                            if( pvtn.isInteger() ){
                              uval = NodeManager::currentNM()->mkNode( PLUS, val, NodeManager::currentNM()->mkConst( Rational( uires ) ) );
                              uval = Rewriter::rewrite( uval );
                            }else{
                              Assert( pvtn.isReal() );
                              //now is strict inequality
                              uires = uires*2;
                            }
                          }
                        }else{
                          bool is_upper = ( r==0 );
                          if( options::cbqiModel() ){
                            // disequality is a disjunction : only consider the bound in the direction of the model
                            //first check if there is an infinity...
                            if( !vts_coeff[0].isNull() ){
                              //coefficient or val won't make a difference, just compare with zero
                              Trace("cbqi-inst-debug") << "Disequality : check infinity polarity " << vts_coeff[0] << std::endl;
                              Assert( vts_coeff[0].isConst() );
                              is_upper = ( vts_coeff[0].getConst<Rational>().sgn()==1 );
                            }else{
                              Node rhs_value = d_qe->getModel()->getValue( val );
                              Node lhs_value = pv_value;
                              if( !veq_c.isNull() ){
                                lhs_value = NodeManager::currentNM()->mkNode( MULT, lhs_value, veq_c );
                                lhs_value = Rewriter::rewrite( lhs_value );
                              }
                              Trace("cbqi-inst-debug") << "Disequality : check model values " << lhs_value << " " << rhs_value << std::endl;
                              Assert( lhs_value!=rhs_value );
                              Node cmp = NodeManager::currentNM()->mkNode( GEQ, lhs_value, rhs_value );
                              cmp = Rewriter::rewrite( cmp );
                              Assert( cmp.isConst() );
                              is_upper = ( cmp!=d_true );
                            }
                          }
                          Assert( atom.getKind()==EQUAL && !pol );
                          if( pvtn.isInteger() ){
                            uires = is_upper ? -1 : 1;
                            uval = NodeManager::currentNM()->mkNode( PLUS, val, NodeManager::currentNM()->mkConst( Rational( uires ) ) );
                            uval = Rewriter::rewrite( uval );
                          }else{
                            Assert( pvtn.isReal() );
                            uires = is_upper ? -2 : 2;
                          }
                        }
                        Trace("cbqi-bound-inf") << "From " << lit << ", got : ";
                        if( !veq_c.isNull() ){
                          Trace("cbqi-bound-inf") << veq_c << " * ";
                        }
                        Trace("cbqi-bound-inf") << pv << " -> " << uval << ", styp = " << uires << std::endl;
                        //take into account delta
                        if( d_use_vts_delta && ( uires==2 || uires==-2 ) ){
                          if( options::cbqiModel() ){
                            Node delta_coeff = NodeManager::currentNM()->mkConst( Rational( uires > 0 ? 1 : -1 ) );
                            if( vts_coeff[1].isNull() ){
                              vts_coeff[1] = delta_coeff;
                            }else{
                              vts_coeff[1] = NodeManager::currentNM()->mkNode( PLUS, vts_coeff[1], delta_coeff );
                              vts_coeff[1] = Rewriter::rewrite( vts_coeff[1] );
                            }
                          }else{
                            Node delta = d_qe->getTermDatabase()->getVtsDelta();
                            uval = NodeManager::currentNM()->mkNode( uires==2 ? PLUS : MINUS, uval, delta );
                            uval = Rewriter::rewrite( uval );
                          }
                        }
                        if( options::cbqiModel() ){
                          //just store bounds, will choose based on tighest bound
                          unsigned index = uires>0 ? 0 : 1;
                          mbp_bounds[index].push_back( uval );
                          mbp_coeff[index].push_back( veq_c );
                          for( unsigned t=0; t<2; t++ ){
                            mbp_vts_coeff[index][t].push_back( vts_coeff[t] );
                          }
                          mbp_lit[index].push_back( lit );
                        }else{
                          //try this bound
                          if( subs_proc[uval].find( veq_c )==subs_proc[uval].end() ){
                            subs_proc[uval][veq_c] = true;
                            if( addInstantiationInc( uval, pv, veq_c, uires>0 ? 1 : -1, subs, vars, coeff, btyp, has_coeff, theta, i, effort ) ){
                              return true;
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
        }
      }
      if( options::cbqiModel() ){
        if( pvtn.isInteger() || pvtn.isReal() ){
          bool use_inf = d_use_vts_inf && ( pvtn.isInteger() ? options::cbqiUseInfInt() : options::cbqiUseInfReal() );
          bool upper_first = false;
          if( options::cbqiMinBounds() ){
            upper_first = mbp_bounds[1].size()<mbp_bounds[0].size();
          }
          unsigned best_used[2];
          std::vector< Node > t_values[3];
          //try optimal bounds
          for( unsigned r=0; r<2; r++ ){
            int rr = upper_first ? (1-r) : r;
            if( mbp_bounds[rr].empty() ){
              if( use_inf ){
                Trace("cbqi-bound") << "No " << ( rr==0 ? "lower" : "upper" ) << " bounds for " << pv << " (type=" << pvtn << ")" << std::endl;
                //no bounds, we do +- infinity
                Node val = d_qe->getTermDatabase()->getVtsInfinity( pvtn );
                //TODO : rho value for infinity?
                if( rr==0 ){
                  val = NodeManager::currentNM()->mkNode( UMINUS, val );
                  val = Rewriter::rewrite( val );
                }
                if( addInstantiationInc( val, pv, Node::null(), 0, subs, vars, coeff, btyp, has_coeff, theta, i, effort ) ){
                  return true;
                }
              }
            }else{
              Trace("cbqi-bound") << ( rr==0 ? "Lower" : "Upper" ) << " bounds for " << pv << " (type=" << pvtn << ") : " << std::endl;
              int best = -1;
              Node best_bound_value[3];
              for( unsigned j=0; j<mbp_bounds[rr].size(); j++ ){
                Node value[3];
                if( Trace.isOn("cbqi-bound") ){
                  Assert( !mbp_bounds[rr][j].isNull() );
                  Trace("cbqi-bound") << "  " << j << ": " << mbp_bounds[rr][j];
                  if( !mbp_vts_coeff[rr][0][j].isNull() ){
                    Trace("cbqi-bound") << " (+ " << mbp_vts_coeff[rr][0][j] << " * INF)";
                  }
                  if( !mbp_vts_coeff[rr][1][j].isNull() ){
                    Trace("cbqi-bound") << " (+ " << mbp_vts_coeff[rr][1][j] << " * DELTA)";
                  }
                  if( !mbp_coeff[rr][j].isNull() ){
                    Trace("cbqi-bound") << " (div " << mbp_coeff[rr][j] << ")";
                  }
                  Trace("cbqi-bound") << ", value = ";
                }
                t_values[rr].push_back( Node::null() );
                //check if it is better than the current best bound : lexicographic order infinite/finite/infinitesimal parts
                bool new_best = true;
                for( unsigned t=0; t<3; t++ ){
                  //get the value
                  if( t==0 ){
                    value[0] = mbp_vts_coeff[rr][0][j];
                    if( !value[0].isNull() ){
                      Trace("cbqi-bound") << "( " << value[0] << " * INF ) + ";
                    }else{
                      value[0] = d_zero;
                    }
                  }else if( t==1 ){
                    Node t_value = d_qe->getModel()->getValue( mbp_bounds[rr][j] );
                    t_values[rr][j] = t_value;
                    value[1] = t_value;
                    Trace("cbqi-bound") << value[1];
                  }else{
                    value[2] = mbp_vts_coeff[rr][1][j];
                    if( !value[2].isNull() ){
                      Trace("cbqi-bound") << " + ( " << value[2] << " * DELTA )";
                    }else{
                      value[2] = d_zero;
                    }
                  }
                  //multiply by coefficient
                  if( value[t]!=d_zero && !mbp_coeff[rr][j].isNull() ){
                    Assert( mbp_coeff[rr][j].isConst() );
                    value[t] = NodeManager::currentNM()->mkNode( MULT, NodeManager::currentNM()->mkConst( Rational(1) / mbp_coeff[rr][j].getConst<Rational>() ), value[t] );
                    value[t] = Rewriter::rewrite( value[t] );
                  }
                  //check if new best
                  if( best!=-1 ){
                    Assert( !value[t].isNull() && !best_bound_value[t].isNull() );
                    if( value[t]!=best_bound_value[t] ){
                      Kind k = rr==0 ? GEQ : LEQ;
                      Node cmp_bound = NodeManager::currentNM()->mkNode( k, value[t], best_bound_value[t] );
                      cmp_bound = Rewriter::rewrite( cmp_bound );
                      if( cmp_bound!=d_true ){
                        new_best = false;
                        break;
                      }
                    }
                  }
                }
                Trace("cbqi-bound") << std::endl;
                if( new_best ){
                  for( unsigned t=0; t<3; t++ ){
                    best_bound_value[t] = value[t];
                  }
                  best = j;
                }
              }
              if( best!=-1 ){
                Trace("cbqi-bound") << "...best bound is " << best << " : ";
                if( best_bound_value[0]!=d_zero ){
                  Trace("cbqi-bound") << "( " << best_bound_value[0] << " * INF ) + ";
                }
                Trace("cbqi-bound") << best_bound_value[1];
                if( best_bound_value[2]!=d_zero ){
                  Trace("cbqi-bound") << " + ( " << best_bound_value[2] << " * DELTA )";
                }
                Trace("cbqi-bound") << std::endl;
                best_used[rr] = (unsigned)best;
                Node val = mbp_bounds[rr][best];
                val = getModelBasedProjectionValue( val, rr==0, mbp_coeff[rr][best], pv_value, t_values[rr][best], theta,
                                                    mbp_vts_coeff[rr][0][best], vts_sym[0], mbp_vts_coeff[rr][1][best], vts_sym[1] );
                if( !val.isNull() ){
                  if( subs_proc[val].find( mbp_coeff[rr][best] )==subs_proc[val].end() ){
                    subs_proc[val][mbp_coeff[rr][best]] = true;
                    if( addInstantiationInc( val, pv, mbp_coeff[rr][best], rr==0 ? 1 : -1, subs, vars, coeff, btyp, has_coeff, theta, i, effort ) ){
                      return true;
                    }
                  }
                }
              }
            }
          }
          //if not using infinity, use model value of zero
          if( !use_inf && mbp_bounds[0].empty() && mbp_bounds[1].empty() ){
            Node val = d_zero;
            Node c; //null (one) coefficient
            val = getModelBasedProjectionValue( val, true, c, pv_value, d_zero, theta, Node::null(), vts_sym[0], Node::null(), vts_sym[1] );
            if( !val.isNull() ){
              if( subs_proc[val].find( c )==subs_proc[val].end() ){
                subs_proc[val][c] = true;
                if( addInstantiationInc( val, pv, c, 0, subs, vars, coeff, btyp, has_coeff, theta, i, effort ) ){
                  return true;
                }
              }
            }
          }
#ifdef MBP_STRICT_ASSERTIONS
          Assert( false );
#endif
          //try non-optimal bounds (heuristic, may help when nested quantification) ?
          Trace("cbqi-bound") << "Try non-optimal bounds..." << std::endl;
          for( unsigned r=0; r<2; r++ ){
            int rr = upper_first ? (1-r) : r;
            for( unsigned j=0; j<mbp_bounds[rr].size(); j++ ){
              if( j!=best_used[rr] ){
                Node val = getModelBasedProjectionValue( mbp_bounds[rr][j], rr==0, mbp_coeff[rr][j], pv_value, t_values[rr][j], theta,
                                                         mbp_vts_coeff[rr][0][j], vts_sym[0], mbp_vts_coeff[rr][1][j], vts_sym[1] );
                if( !val.isNull() ){
                  if( subs_proc[val].find( mbp_coeff[rr][j] )==subs_proc[val].end() ){
                    subs_proc[val][mbp_coeff[rr][j]] = true;
                    if( addInstantiationInc( val, pv, mbp_coeff[rr][j], rr==0 ? 1 : -1, subs, vars, coeff, btyp, has_coeff, theta, i, effort ) ){
                      return true;
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    //[4] resort to using value in model
    if( effort>0 || pvtn.isBoolean() ){
      Node mv = d_qe->getModel()->getValue( pv );
      Node pv_coeff_m;
      Trace("cbqi-inst-debug") << "[4] " << i << "...try model value " << mv << std::endl;
      int new_effort = pvtn.isBoolean() ? effort : 1;
#ifdef MBP_STRICT_ASSERTIONS
      //we only resort to values in the case of booleans
      Assert( ( pvtn.isInteger() ? !options::cbqiUseInfInt() : !options::cbqiUseInfReal() ) || pvtn.isBoolean() );
#endif
      if( addInstantiationInc( mv, pv, pv_coeff_m, 0, subs, vars, coeff, btyp, has_coeff, theta, i, new_effort ) ){
        return true;
      }
    }
    Trace("cbqi-inst-debug") << "[No instantiation found for " << pv << "]" << std::endl;
    return false;
  }
}


bool CegInstantiator::addInstantiationInc( Node n, Node pv, Node pv_coeff, int bt, std::vector< Node >& subs, std::vector< Node >& vars,
                                           std::vector< Node >& coeff, std::vector< int >& btyp, 
                                           std::vector< Node >& has_coeff, Node theta, unsigned i, unsigned effort ) {
  if( Trace.isOn("cbqi-inst") ){
    for( unsigned j=0; j<subs.size(); j++ ){
      Trace("cbqi-inst") << " ";
    }
    Trace("cbqi-inst") << subs.size() << ": ";
    if( !pv_coeff.isNull() ){
      Trace("cbqi-inst") << pv_coeff << " * ";
    }
    Trace("cbqi-inst") << pv << " -> " << n << std::endl;
  }
  //must ensure variables have been computed for n
  computeProgVars( n );
  //substitute into previous substitutions, when applicable
  std::vector< Node > a_subs;
  a_subs.push_back( n );
  std::vector< Node > a_var;
  a_var.push_back( pv );
  std::vector< Node > a_coeff;
  std::vector< Node > a_has_coeff;
  if( !pv_coeff.isNull() ){
    a_coeff.push_back( pv_coeff );
    a_has_coeff.push_back( pv );
  }

  bool success = true;
  std::map< int, Node > prev_subs;
  std::map< int, Node > prev_coeff;
  std::vector< Node > new_has_coeff;
  for( unsigned j=0; j<subs.size(); j++ ){
    Assert( d_prog_var.find( subs[j] )!=d_prog_var.end() );
    if( d_prog_var[subs[j]].find( pv )!=d_prog_var[subs[j]].end() ){
      prev_subs[j] = subs[j];
      TNode tv = pv;
      TNode ts = n;
      Node a_pv_coeff;
      Node new_subs = applySubstitution( subs[j], a_subs, a_var, a_coeff, a_has_coeff, a_pv_coeff, true );
      if( !new_subs.isNull() ){
        subs[j] = new_subs;
        if( !a_pv_coeff.isNull() ){
          prev_coeff[j] = coeff[j];
          if( coeff[j].isNull() ){
            Assert( std::find( has_coeff.begin(), has_coeff.end(), vars[j] )==has_coeff.end() );
            //now has coefficient
            new_has_coeff.push_back( vars[j] );
            has_coeff.push_back( vars[j] );
            coeff[j] = a_pv_coeff;
          }else{
            coeff[j] = Rewriter::rewrite( NodeManager::currentNM()->mkNode( MULT, coeff[j], a_pv_coeff ) );
          }
        }
        if( subs[j]!=prev_subs[j] ){
          computeProgVars( subs[j] );
        }
      }else{
        Trace("cbqi-inst-debug") << "...failed to apply substitution to " << subs[j] << std::endl;
        success = false;
        break;
      }
    }
  }
  if( success ){
    subs.push_back( n );
    vars.push_back( pv );
    coeff.push_back( pv_coeff );
    btyp.push_back( bt );
    if( !pv_coeff.isNull() ){
      has_coeff.push_back( pv );
    }
    Node new_theta = theta;
    if( !pv_coeff.isNull() ){
      if( new_theta.isNull() ){
        new_theta = pv_coeff;
      }else{
        new_theta = NodeManager::currentNM()->mkNode( MULT, new_theta, pv_coeff );
        new_theta = Rewriter::rewrite( new_theta );
      }
    }
    success = addInstantiation( subs, vars, coeff, btyp, has_coeff, new_theta, i+1, effort );
    if( !success ){
      subs.pop_back();
      vars.pop_back();
      coeff.pop_back();
      btyp.pop_back();
      if( !pv_coeff.isNull() ){
        has_coeff.pop_back();
      }
    }
  }
  if( success ){
    return true;
  }else{
    //revert substitution information
    for( std::map< int, Node >::iterator it = prev_subs.begin(); it != prev_subs.end(); it++ ){
      subs[it->first] = it->second;
    }
    for( std::map< int, Node >::iterator it = prev_coeff.begin(); it != prev_coeff.end(); it++ ){
      coeff[it->first] = it->second;
    }
    for( unsigned i=0; i<new_has_coeff.size(); i++ ){
      has_coeff.pop_back();
    }
    return false;
  }
}

bool CegInstantiator::addInstantiationCoeff( std::vector< Node >& subs, std::vector< Node >& vars,
                                             std::vector< Node >& coeff, std::vector< int >& btyp, std::vector< Node >& has_coeff, unsigned j ) {
  if( j==has_coeff.size() ){
    return addInstantiation( subs, vars );
  }else{
    Assert( std::find( vars.begin(), vars.end(), has_coeff[j] )!=vars.end() );
    unsigned index = std::find( vars.begin(), vars.end(), has_coeff[j] )-vars.begin();
    Node prev = subs[index];
    Assert( !coeff[index].isNull() );
    Trace("cbqi-inst-debug") << "Normalize substitution for " << coeff[index] << " * " << vars[index] << " = " << subs[index] << std::endl;
    Assert( vars[index].getType().isInteger() );
    //must ensure that divisibility constraints are met
    //solve updated rewritten equality for vars[index], if coefficient is one, then we are successful
    Node eq_lhs = NodeManager::currentNM()->mkNode( MULT, coeff[index], vars[index] );
    Node eq_rhs = subs[index];
    Node eq = eq_lhs.eqNode( eq_rhs );
    eq = Rewriter::rewrite( eq );
    Trace("cbqi-inst-debug") << "...equality is " << eq << std::endl;
    std::map< Node, Node > msum;
    if( QuantArith::getMonomialSumLit( eq, msum ) ){
      Node veq;
      if( QuantArith::isolate( vars[index], msum, veq, EQUAL, true )!=0 ){
        Node veq_c;
        if( veq[0]!=vars[index] ){
          Node veq_v;
          if( QuantArith::getMonomial( veq[0], veq_c, veq_v ) ){
            Assert( veq_v==vars[index] );
          }
        }
        subs[index] = veq[1];
        if( !veq_c.isNull() ){
          subs[index] = NodeManager::currentNM()->mkNode( INTS_DIVISION, veq[1], veq_c );
          Trace("cbqi-inst-debug") << "...bound type is : " << btyp[index] << std::endl;
          //intger division rounding up if from a lower bound
          if( btyp[index]==1 ){
            subs[index] = NodeManager::currentNM()->mkNode( PLUS, subs[index],
              NodeManager::currentNM()->mkNode( ITE,
                NodeManager::currentNM()->mkNode( EQUAL,
                  NodeManager::currentNM()->mkNode( INTS_MODULUS, veq[1], veq_c ),
                  d_zero ),
                d_zero, d_one )
            );
          }
        }
        Trace("cbqi-inst-debug") << "...normalize integers : " << subs[index] << std::endl;
        if( addInstantiationCoeff( subs, vars, coeff, btyp, has_coeff, j+1 ) ){
          return true;
        }
      }
    }
    subs[index] = prev;
    Trace("cbqi-inst-debug") << "...failed." << std::endl;
    return false;
  }
}

bool CegInstantiator::addInstantiation( std::vector< Node >& subs, std::vector< Node >& vars ) {
  bool ret = d_out->addInstantiation( subs );
#ifdef MBP_STRICT_ASSERTIONS
  Assert( ret );
#endif
  return ret;
}


Node CegInstantiator::applySubstitution( Node n, std::vector< Node >& subs, std::vector< Node >& vars,
                                                 std::vector< Node >& coeff, std::vector< Node >& has_coeff, Node& pv_coeff, bool try_coeff ) {
  Assert( d_prog_var.find( n )!=d_prog_var.end() );
  Assert( n==Rewriter::rewrite( n ) );
  bool req_coeff = false;
  if( !has_coeff.empty() ){
    for( std::map< Node, bool >::iterator it = d_prog_var[n].begin(); it != d_prog_var[n].end(); ++it ){
      if( std::find( has_coeff.begin(), has_coeff.end(), it->first )!=has_coeff.end() ){
        req_coeff = true;
        break;
      }
    }
  }
  if( !req_coeff ){
    Node nret = n.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
    if( n!=nret ){
      nret = Rewriter::rewrite( nret );
    }
    //result is nret
    return nret;
  }else{
    if( try_coeff ){
      //must convert to monomial representation
      std::map< Node, Node > msum;
      if( QuantArith::getMonomialSum( n, msum ) ){
        std::map< Node, Node > msum_coeff;
        std::map< Node, Node > msum_term;
        for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
          //check if in substitution
          std::vector< Node >::iterator its = std::find( vars.begin(), vars.end(), it->first );
          if( its!=vars.end() ){
            int index = its-vars.begin();
            if( coeff[index].isNull() ){
              //apply substitution
              msum_term[it->first] = subs[index];
            }else{
              //apply substitution, multiply to ensure no divisibility conflict
              msum_term[it->first] = subs[index];
              //relative coefficient
              msum_coeff[it->first] = coeff[index];
              if( pv_coeff.isNull() ){
                pv_coeff = coeff[index];
              }else{
                pv_coeff = NodeManager::currentNM()->mkNode( MULT, pv_coeff, coeff[index] );
              }
            }
          }else{
            msum_term[it->first] = it->first;
          }
        }
        //make sum with normalized coefficient
        Assert( !pv_coeff.isNull() );
        pv_coeff = Rewriter::rewrite( pv_coeff );
        Trace("cegqi-si-apply-subs-debug") << "Combined coeff : " << pv_coeff << std::endl;
        std::vector< Node > children;
        for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
          Node c_coeff;
          if( !msum_coeff[it->first].isNull() ){
            c_coeff = Rewriter::rewrite( NodeManager::currentNM()->mkConst( pv_coeff.getConst<Rational>() / msum_coeff[it->first].getConst<Rational>() ) );
          }else{
            c_coeff = pv_coeff;
          }
          if( !it->second.isNull() ){
            c_coeff = NodeManager::currentNM()->mkNode( MULT, c_coeff, it->second );
          }
          Node c = NodeManager::currentNM()->mkNode( MULT, c_coeff, msum_term[it->first] );
          children.push_back( c );
          Trace("cegqi-si-apply-subs-debug") << "Add child : " << c << std::endl;
        }
        Node nret = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( PLUS, children );
        nret = Rewriter::rewrite( nret );
        //result is ( nret / pv_coeff )
        return nret;
      }else{
        Trace("cegqi-si-apply-subs-debug") << "Failed to find monomial sum " << n << std::endl;
      }
    }
    // failed to apply the substitution
    return Node::null();
  }
}

Node CegInstantiator::getModelBasedProjectionValue( Node t, bool isLower, Node c, Node me, Node mt, Node theta,
                                                    Node inf_coeff, Node vts_inf, Node delta_coeff, Node vts_delta ) {
  Node val = t;
  Trace("cbqi-bound2") << "Value : " << val << std::endl;
  //add rho value
  //get the value of c*e
  Node ceValue = me;
  Node new_theta = theta;
  if( !c.isNull() ){
    ceValue = NodeManager::currentNM()->mkNode( MULT, ceValue, c );
    ceValue = Rewriter::rewrite( ceValue );
    if( new_theta.isNull() ){
      new_theta = c;
    }else{
      new_theta = NodeManager::currentNM()->mkNode( MULT, new_theta, c );
      new_theta = Rewriter::rewrite( new_theta );
    }
    Trace("cbqi-bound2") << "...c*e = " << ceValue << std::endl;
    Trace("cbqi-bound2") << "...theta = " << new_theta << std::endl;
  }
  if( !new_theta.isNull() ){
    Node rho;
    if( isLower ){
      rho = NodeManager::currentNM()->mkNode( MINUS, ceValue, mt );
    }else{
      rho = NodeManager::currentNM()->mkNode( MINUS, mt, ceValue );
    }
    rho = Rewriter::rewrite( rho );
    Trace("cbqi-bound2") << "...rho = " << me << " - " << mt << " = " << rho << std::endl;
    Trace("cbqi-bound2") << "..." << rho << " mod " << new_theta << " = ";
    rho = NodeManager::currentNM()->mkNode( INTS_MODULUS_TOTAL, rho, new_theta );
    rho = Rewriter::rewrite( rho );
    Trace("cbqi-bound2") << rho << std::endl;
    Kind rk = isLower ? PLUS : MINUS;
    val = NodeManager::currentNM()->mkNode( rk, val, rho );
    val = Rewriter::rewrite( val );
    Trace("cbqi-bound2") << "(after rho) : " << val << std::endl;
  }
  if( !inf_coeff.isNull() ){
    Assert( !vts_inf.isNull() );
    val = NodeManager::currentNM()->mkNode( PLUS, val, NodeManager::currentNM()->mkNode( MULT, inf_coeff, vts_inf ) );
    val = Rewriter::rewrite( val );
  }
  if( !delta_coeff.isNull() ){
    //create delta here if necessary
    if( vts_delta.isNull() ){
      vts_delta = d_qe->getTermDatabase()->getVtsDelta();
    }
    val = NodeManager::currentNM()->mkNode( PLUS, val, NodeManager::currentNM()->mkNode( MULT, delta_coeff, vts_delta ) );
    val = Rewriter::rewrite( val );
  }
  return val;
}

bool CegInstantiator::check() {
  if( d_qe->getTheoryEngine()->needCheck() ){
    Trace("cegqi-engine") << "  CEGQI instantiator : wait until all ground theories are finished." << std::endl;
    return false;
  }
  processAssertions();
  for( unsigned r=0; r<2; r++ ){
    std::vector< Node > subs;
    std::vector< Node > vars;
    std::vector< Node > coeff;
    std::vector< int > btyp;
    std::vector< Node > has_coeff;
    Node theta;
    //try to add an instantiation
    if( addInstantiation( subs, vars, coeff, btyp, has_coeff, theta, 0, r==0 ? 0 : 2 ) ){
      return true;
    }
  }
  Trace("cegqi-engine") << "  WARNING : unable to find CEGQI single invocation instantiation." << std::endl;
  return false;
}

void collectPresolveEqTerms( Node n, std::map< Node, std::vector< Node > >& teq ) {
  if( n.getKind()==FORALL || n.getKind()==EXISTS ){
    //do nothing
  }else{
    if( n.getKind()==EQUAL ){
      for( unsigned i=0; i<2; i++ ){
        std::map< Node, std::vector< Node > >::iterator it = teq.find( n[i] );
        if( it!=teq.end() ){
          Node nn = n[ i==0 ? 1 : 0 ];
          if( std::find( it->second.begin(), it->second.end(), nn )==it->second.end() ){
            it->second.push_back( nn );
            Trace("cbqi-presolve") << "  - " << n[i] << " = " << nn << std::endl;
          }
        }
      }
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      collectPresolveEqTerms( n[i], teq );
    }
  }
}

void getPresolveEqConjuncts( std::vector< Node >& vars, std::vector< Node >& terms,
                             std::map< Node, std::vector< Node > >& teq, Node f, std::vector< Node >& conj ) {
  if( conj.size()<1000 ){
    if( terms.size()==f[0].getNumChildren() ){
      Node c = f[1].substitute( vars.begin(), vars.end(), terms.begin(), terms.end() );
      conj.push_back( c );
    }else{
      unsigned i = terms.size();
      Node v = f[0][i];
      terms.push_back( Node::null() );
      for( unsigned j=0; j<teq[v].size(); j++ ){
        terms[i] = teq[v][j];
        getPresolveEqConjuncts( vars, terms, teq, f, conj );
      }
      terms.pop_back();
    }
  }
}

void CegInstantiator::presolve( Node q ) {
  Trace("cbqi-presolve") << "CBQI presolve " << q << std::endl;
  //at preregister time, add proxy of obvious instantiations up front, which helps learning during preprocessing
  std::vector< Node > vars;
  std::map< Node, std::vector< Node > > teq;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    vars.push_back( q[0][i] );
    teq[q[0][i]].clear();
  }
  collectPresolveEqTerms( q[1], teq );
  std::vector< Node > terms;
  std::vector< Node > conj;
  getPresolveEqConjuncts( vars, terms, teq, q, conj );

  if( !conj.empty() ){
    Node lem = conj.size()==1 ? conj[0] : NodeManager::currentNM()->mkNode( AND, conj );
    Node g = NodeManager::currentNM()->mkSkolem( "g", NodeManager::currentNM()->booleanType() );
    lem = NodeManager::currentNM()->mkNode( OR, g, lem );
    Trace("cbqi-presolve-debug") << "Presolve lemma : " << lem << std::endl;
    d_qe->getOutputChannel().lemma( lem, false, true );
  }
}

void CegInstantiator::processAssertions() {
  Trace("cbqi-proc") << "--- Process assertions, #var = " << d_vars.size() << ", #aux-var = " << d_aux_vars.size() << std::endl;
  d_curr_asserts.clear();
  d_curr_eqc.clear();
  d_curr_rep.clear();
  d_curr_arith_eqc.clear();

  eq::EqualityEngine* ee = d_qe->getMasterEqualityEngine();
  //to eliminate identified illegal terms
  std::map< Node, Node > aux_subs;

  //for each variable
  bool has_arith_var = false;
  for( unsigned i=0; i<d_vars.size(); i++ ){
    Node pv = d_vars[i];
    TypeNode pvtn = pv.getType();
    //collect current assertions
    unsigned rmax = Theory::theoryOf( pv )==Theory::theoryOf( pv.getType() ) ? 1 : 2;
    for( unsigned r=0; r<rmax; r++ ){
      TheoryId tid = r==0 ? Theory::theoryOf( pv ) : Theory::theoryOf( pv.getType() );
      Theory* theory = d_qe->getTheoryEngine()->theoryOf( tid );
      Trace("cbqi-proc-debug") << "...theory of " << pv << " (r=" << r << ") is " << tid << std::endl;
      if( d_curr_asserts.find( tid )==d_curr_asserts.end() ){
        if (theory && d_qe->getTheoryEngine()->isTheoryEnabled(tid)) {
          Trace("cbqi-proc") << "Collect assertions from " << tid << std::endl;
          d_curr_asserts[tid].clear();
          //collect all assertions from theory
          for( context::CDList<Assertion>::const_iterator it = theory->facts_begin(); it != theory->facts_end(); ++ it) {
            Node lit = (*it).assertion;
            d_curr_asserts[tid].push_back( lit );
            Trace("cbqi-proc-debug") << "...add : " << lit << std::endl;
            if( lit.getKind()==EQUAL ){
              std::map< Node, std::map< Node, Node > >::iterator itae = d_aux_eq.find( lit );
              if( itae!=d_aux_eq.end() ){
                for( std::map< Node, Node >::iterator itae2 = itae->second.begin(); itae2 != itae->second.end(); ++itae2 ){
                  aux_subs[ itae2->first ] = itae2->second;
                  Trace("cbqi-proc") << "......add substitution : " << itae2->first << " -> " << itae2->second << std::endl;
                }
              }
            }
          }
        }
      }
    }
    //collect information about eqc
    if( ee->hasTerm( pv ) ){
      Node pvr = ee->getRepresentative( pv );
      d_curr_rep[pv] = pvr;
      if( d_curr_eqc.find( pvr )==d_curr_eqc.end() ){
        Trace("cbqi-proc") << "Collect equivalence class " << pvr << std::endl;
        eq::EqClassIterator eqc_i = eq::EqClassIterator( pvr, ee );
        while( !eqc_i.isFinished() ){
          d_curr_eqc[pvr].push_back( *eqc_i );
          ++eqc_i;
        }
      }
    }
    //has arith var
    if( pvtn.isInteger() || pvtn.isReal() ){
      has_arith_var = true;
    }
  }
  //must process all arithmetic eqc if any arithmetic variable
  if( has_arith_var ){
    Trace("cbqi-proc-debug") << "...collect arithmetic equivalence classes" << std::endl;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
    while( !eqcs_i.isFinished() ){
      Node r = *eqcs_i;
      TypeNode rtn = r.getType();
      if( rtn.isInteger() || rtn.isReal() ){
        Trace("cbqi-proc-debug") << "...arith eqc: " << r << std::endl;
        d_curr_arith_eqc.push_back( r );
        if( d_curr_eqc.find( r )==d_curr_eqc.end() ){
          Trace("cbqi-proc") << "Collect equivalence class " << r << std::endl;
          eq::EqClassIterator eqc_i = eq::EqClassIterator( r, ee );
          while( !eqc_i.isFinished() ){
            d_curr_eqc[r].push_back( *eqc_i );
            ++eqc_i;
          }
        }
      }
      ++eqcs_i;
    }
  }
  //construct substitution from union find
  std::vector< Node > subs_lhs;
  std::vector< Node > subs_rhs;
  for( unsigned i=0; i<d_aux_vars.size(); i++ ){
    Node r = d_aux_vars[i];
    std::map< Node, Node >::iterator it = aux_subs.find( r );
    if( it!=aux_subs.end() ){
      addToAuxVarSubstitution( subs_lhs, subs_rhs, r, it->second );
    }else{
      Trace("cbqi-proc") << "....no substitution found for auxiliary variable " << r << "!!!" << std::endl;
#ifdef MBP_STRICT_ASSERTIONS
      Assert( false );
#endif
    }
  }

  //apply substitutions to everything, if necessary
  if( !subs_lhs.empty() ){
    Trace("cbqi-proc") << "Applying substitution : " << std::endl;
    for( unsigned i=0; i<subs_lhs.size(); i++ ){
      Trace("cbqi-proc") << "  " << subs_lhs[i] << " -> " << subs_rhs[i] << std::endl;
    }

    for( std::map< TheoryId, std::vector< Node > >::iterator it = d_curr_asserts.begin(); it != d_curr_asserts.end(); ++it ){
      for( unsigned i=0; i<it->second.size(); i++ ){
        Node lit = it->second[i];
        lit = lit.substitute( subs_lhs.begin(), subs_lhs.end(), subs_rhs.begin(), subs_rhs.end() );
        lit = Rewriter::rewrite( lit );
        it->second[i] = lit;
      }
    }
    for( std::map< Node, std::vector< Node > >::iterator it = d_curr_eqc.begin(); it != d_curr_eqc.end(); ++it ){
      for( unsigned i=0; i<it->second.size(); i++ ){
        Node n = it->second[i];
        n = n.substitute( subs_lhs.begin(), subs_lhs.end(), subs_rhs.begin(), subs_rhs.end() );
        n = Rewriter::rewrite( n  );
        it->second[i] = n;
      }
    }
  }

  //remove unecessary assertions
  for( std::map< TheoryId, std::vector< Node > >::iterator it = d_curr_asserts.begin(); it != d_curr_asserts.end(); ++it ){
    std::vector< Node > akeep;
    for( unsigned i=0; i<it->second.size(); i++ ){
      Node n = it->second[i];
      //compute the variables in assertion
      computeProgVars( n );
      //must be an eligible term
      if( d_inelig.find( n )==d_inelig.end() ){
        //must contain at least one variable
        if( !d_prog_var[n].empty() ){
          Trace("cbqi-proc") << "...literal[" << it->first << "] : " << n << std::endl;
          akeep.push_back( n );
        }else{
          Trace("cbqi-proc") << "...remove literal from " << it->first << " : " << n << " since it contains no relevant variables." << std::endl;
        }
      }else{
        Trace("cbqi-proc") << "...remove literal from " << it->first << " : " << n << " since it contains ineligible terms." << std::endl;
      }
    }
    it->second.clear();
    it->second.insert( it->second.end(), akeep.begin(), akeep.end() );
  }

  //remove duplicate terms from eqc
  for( std::map< Node, std::vector< Node > >::iterator it = d_curr_eqc.begin(); it != d_curr_eqc.end(); ++it ){
    std::vector< Node > new_eqc;
    for( unsigned i=0; i<it->second.size(); i++ ){
      if( std::find( new_eqc.begin(), new_eqc.end(), it->second[i] )==new_eqc.end() ){
        new_eqc.push_back( it->second[i] );
      }
    }
    it->second.clear();
    it->second.insert( it->second.end(), new_eqc.begin(), new_eqc.end() );
  }
}

void CegInstantiator::addToAuxVarSubstitution( std::vector< Node >& subs_lhs, std::vector< Node >& subs_rhs, Node l, Node r ) {
  r = r.substitute( subs_lhs.begin(), subs_lhs.end(), subs_rhs.begin(), subs_rhs.end() );

  std::vector< Node > cl;
  cl.push_back( l );
  std::vector< Node > cr;
  cr.push_back( r );
  for( unsigned i=0; i<subs_lhs.size(); i++ ){
    Node nr = subs_rhs[i].substitute( cl.begin(), cl.end(), cr.begin(), cr.end() );
    nr = Rewriter::rewrite( nr );
    subs_rhs[i] = nr;
  }

  subs_lhs.push_back( l );
  subs_rhs.push_back( r );
}

void CegInstantiator::registerCounterexampleLemma( std::vector< Node >& lems, std::vector< Node >& ce_vars ) {
  Assert( d_vars.empty() );
  d_vars.insert( d_vars.end(), ce_vars.begin(), ce_vars.end() );
  IteSkolemMap iteSkolemMap;
  d_qe->getTheoryEngine()->getIteRemover()->run(lems, iteSkolemMap);
  Assert( d_aux_vars.empty() );
  for(IteSkolemMap::iterator i = iteSkolemMap.begin(); i != iteSkolemMap.end(); ++i) {
    Trace("cbqi-debug") << "  Auxiliary var (from ITE) : " << i->first << std::endl;
    d_aux_vars.push_back( i->first );
  }
  for( unsigned i=0; i<lems.size(); i++ ){
    Trace("cbqi-debug") << "Counterexample lemma (pre-rewrite)  " << i << " : " << lems[i] << std::endl;
    Node rlem = lems[i];
    rlem = Rewriter::rewrite( rlem );
    Trace("cbqi-debug") << "Counterexample lemma (post-rewrite) " << i << " : " << rlem << std::endl;
    //record the literals that imply auxiliary variables to be equal to terms
    if( lems[i].getKind()==ITE && rlem.getKind()==ITE ){
      if( lems[i][1].getKind()==EQUAL && lems[i][2].getKind()==EQUAL && lems[i][1][0]==lems[i][2][0] ){
        if( std::find( d_aux_vars.begin(), d_aux_vars.end(), lems[i][1][0] )!=d_aux_vars.end() ){
          Node v = lems[i][1][0];
          for( unsigned r=1; r<=2; r++ ){
            d_aux_eq[rlem[r]][v] = lems[i][r][1];
            Trace("cbqi-debug") << "  " << rlem[r] << " implies " << v << " = " << lems[i][r][1] << std::endl;
          }
        }
      }
    }
    lems[i] = rlem;
  }
}

//old implementation

InstStrategySimplex::InstStrategySimplex( TheoryArith* th, QuantifiersEngine* ie ) :
    InstStrategy( ie ), d_th( th ), d_counter( 0 ){
  d_negOne = NodeManager::currentNM()->mkConst( Rational(-1) );
  d_zero = NodeManager::currentNM()->mkConst( Rational(0) );
}

void getInstantiationConstants( Node n, std::vector< Node >& ics ){
  if( n.getKind()==INST_CONSTANT ){
    if( std::find( ics.begin(), ics.end(), n )==ics.end() ){
      ics.push_back( n );
    }
  }else{
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      getInstantiationConstants( n[i], ics );
    }
  }
}


void InstStrategySimplex::processResetInstantiationRound( Theory::Effort effort ){
  Debug("quant-arith") << "Setting up simplex for instantiator... " << std::endl;
  d_quantActive.clear();
  d_instRows.clear();
  d_tableaux_term.clear();
  d_tableaux.clear();
  d_ceTableaux.clear();
  //search for instantiation rows in simplex tableaux
  ArithVariables& avnm = d_th->d_internal->d_partialModel;
  ArithVariables::var_iterator vi, vend;
  for(vi = avnm.var_begin(), vend = avnm.var_end(); vi != vend; ++vi ){
    ArithVar x = *vi;
    Node n = avnm.asNode(x);

    //collect instantiation constants
    std::vector< Node > ics;
    getInstantiationConstants( n, ics );
    for( unsigned i=0; i<ics.size(); i++ ){
      NodeBuilder<> t(kind::PLUS);
      if( n.getKind()==PLUS ){
        for( int j=0; j<(int)n.getNumChildren(); j++ ){
          addTermToRow( ics[i], x, n[j], t );
        }
      }else{
        addTermToRow( ics[i], x, n, t );
      }
      d_instRows[ics[i]].push_back( x );
      //this theory has constraints from f
      Node f = TermDb::getInstConstAttr(ics[i]);
      Debug("quant-arith") << "Has constraints from " << f << std::endl;
      //set that we should process it
      d_quantActive[ f ] = true;
      //set tableaux term
      if( t.getNumChildren()==0 ){
        d_tableaux_term[ics[i]][x] = d_zero;
      }else if( t.getNumChildren()==1 ){
        d_tableaux_term[ics[i]][x] = t.getChild( 0 );
      }else{
        d_tableaux_term[ics[i]][x] = t;
      }
    }
  }
  //print debug
  Debug("quant-arith-debug") << std::endl;
  debugPrint( "quant-arith-debug" );
  d_counter++;
}

void InstStrategySimplex::addTermToRow( Node i, ArithVar x, Node n, NodeBuilder<>& t ){
  if( n.getKind()==MULT ){
    if( TermDb::hasInstConstAttr(n[1]) && n[0].getKind()==CONST_RATIONAL ){
      if( n[1]==i ){
        d_ceTableaux[i][x][ n[1] ] = n[0];
      }else{
        d_tableaux_ce_term[i][x][ n[1] ] = n[0];
      }
    }else{
      d_tableaux[i][x][ n[1] ] = n[0];
      t << n;
    }
  }else{
    if( TermDb::hasInstConstAttr(n) ){
      if( n==i ){
        d_ceTableaux[i][x][ n ] = Node::null();
      }else{
        d_tableaux_ce_term[i][x][ n ] = NodeManager::currentNM()->mkConst( Rational(1) );
      }
    }else{
      d_tableaux[i][x][ n ] = NodeManager::currentNM()->mkConst( Rational(1) );
      t << n;
    }
  }
}

int InstStrategySimplex::process( Node f, Theory::Effort effort, int e ){
  if( e<1 ){
    return STATUS_UNFINISHED;
  }else if( e==1 ){
    if( d_quantActive.find( f )!=d_quantActive.end() ){
      //the point instantiation
      InstMatch m_point( f );
      bool m_point_valid = true;
      int lem = 0;
      //scan over all instantiation rows
      for( int i=0; i<d_quantEngine->getTermDatabase()->getNumInstantiationConstants( f ); i++ ){
        Node ic = d_quantEngine->getTermDatabase()->getInstantiationConstant( f, i );
        Debug("quant-arith-simplex") << "InstStrategySimplex check " << ic << ", rows = " << d_instRows[ic].size() << std::endl;
        for( int j=0; j<(int)d_instRows[ic].size(); j++ ){
          ArithVar x = d_instRows[ic][j];
          if( !d_ceTableaux[ic][x].empty() ){
            if( Debug.isOn("quant-arith-simplex") ){
              Debug("quant-arith-simplex") << "--- Check row " << ic << " " << x << std::endl;
              Debug("quant-arith-simplex") << "  ";
              for( std::map< Node, Node >::iterator it = d_ceTableaux[ic][x].begin(); it != d_ceTableaux[ic][x].end(); ++it ){
                if( it!=d_ceTableaux[ic][x].begin() ){ Debug("quant-arith-simplex") << " + "; }
                Debug("quant-arith-simplex") << it->first << " * " << it->second;
              }
              Debug("quant-arith-simplex") << " = ";
              Node v = getTableauxValue( x, false );
              Debug("quant-arith-simplex") << v << std::endl;
              Debug("quant-arith-simplex") << "  term : " << d_tableaux_term[ic][x] << std::endl;
              Debug("quant-arith-simplex") << "  ce-term : ";
              for( std::map< Node, Node >::iterator it = d_tableaux_ce_term[ic][x].begin(); it != d_tableaux_ce_term[ic][x].end(); it++ ){
                if( it!=d_tableaux_ce_term[ic][x].begin() ){ Debug("quant-arith-simplex") << " + "; }
                Debug("quant-arith-simplex") << it->first << " * " << it->second;
              }
              Debug("quant-arith-simplex") << std::endl;
            }
            //instantiation row will be A*e + B*t = beta,
            // where e is a vector of terms , and t is vector of ground terms.
            // Say one term in A*e is coeff*e_i, where e_i is an instantiation constant
            // We will construct the term ( beta - B*t)/coeff to use for e_i.
            InstMatch m( f );
            for( unsigned k=0; k<f[0].getNumChildren(); k++ ){
              if( f[0][k].getType().isInteger() ){
                m.setValue( k, d_zero );
              }
            }
            //By default, choose the first instantiation constant to be e_i.
            Node var = d_ceTableaux[ic][x].begin()->first;
            //if it is integer, we need to find variable with coefficent +/- 1
            if( var.getType().isInteger() ){
              std::map< Node, Node >::iterator it = d_ceTableaux[ic][x].begin();
              while( !var.isNull() && !d_ceTableaux[ic][x][var].isNull() && d_ceTableaux[ic][x][var]!=d_negOne ){
                ++it;
                if( it==d_ceTableaux[ic][x].end() ){
                  var = Node::null();
                }else{
                  var = it->first;
                }
              }
              //Otherwise, try one that divides all ground term coefficients?
              //  Might be futile, if rewrite ensures gcd of coeffs is 1.
            }
            if( !var.isNull() ){
              //add to point instantiation if applicable
              if( d_tableaux_ce_term[ic][x].empty() && d_tableaux_term[ic][x]==d_zero ){
                Debug("quant-arith-simplex") << "*** Row contributes to point instantiation." << std::endl;
                Node v = getTableauxValue( x, false );
                if( !var.getType().isInteger() || v.getType().isInteger() ){
                  m_point.setValue( i, v );
                }else{
                  m_point_valid = false;
                }
              }
              Debug("quant-arith-simplex") << "Instantiate with var " << var << std::endl;
              if( doInstantiation( f, ic, d_tableaux_term[ic][x], x, m, var ) ){
                lem++;
              }
            }else{
              Debug("quant-arith-simplex") << "Could not find var." << std::endl;
            }
          }
        }
      }
      if( lem==0 && m_point_valid ){
        if( d_quantEngine->addInstantiation( f, m_point ) ){
          Debug("quant-arith-simplex") << "...added point instantiation." << std::endl;
        }
      }
    }
  }
  return STATUS_UNKNOWN;
}


void InstStrategySimplex::debugPrint( const char* c ){
  ArithVariables& avnm = d_th->d_internal->d_partialModel;
  ArithVariables::var_iterator vi, vend;
  for(vi = avnm.var_begin(), vend = avnm.var_end(); vi != vend; ++vi ){
    ArithVar x = *vi;
    Node n = avnm.asNode(x);
    //if( ((TheoryArith*)getTheory())->d_partialModel.hasEitherBound( x ) ){
      Debug(c) << x << " : " << n << ", bounds = ";
      if( d_th->d_internal->d_partialModel.hasLowerBound( x ) ){
        Debug(c) << d_th->d_internal->d_partialModel.getLowerBound( x );
      }else{
        Debug(c) << "-infty";
      }
      Debug(c) << " <= ";
      Debug(c) << d_th->d_internal->d_partialModel.getAssignment( x );
      Debug(c) << " <= ";
      if( d_th->d_internal->d_partialModel.hasUpperBound( x ) ){
        Debug(c) << d_th->d_internal->d_partialModel.getUpperBound( x );
      }else{
        Debug(c) << "+infty";
      }
      Debug(c) << std::endl;
      //Debug(c) << "   Term = " << d_tableaux_term[x] << std::endl;
      //Debug(c) << "   ";
      //for( std::map< Node, Node >::iterator it2 = d_tableaux[x].begin(); it2 != d_tableaux[x].end(); ++it2 ){
      //  Debug(c) << "( " << it2->first << ", " << it2->second << " ) ";
      //}
      //for( std::map< Node, Node >::iterator it2 = d_ceTableaux[x].begin(); it2 != d_ceTableaux[x].end(); ++it2 ){
      //  Debug(c) << "(CE)( " << it2->first << ", " << it2->second << " ) ";
      //}
      //for( std::map< Node, Node >::iterator it2 = d_tableaux_ce_term[x].begin(); it2 != d_tableaux_ce_term[x].end(); ++it2 ){
      //  Debug(c) << "(CE-term)( " << it2->first << ", " << it2->second << " ) ";
      //}
      //Debug(c) << std::endl;
    //}
  }
  Debug(c) << std::endl;

  for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
    Debug(c) << f << std::endl;
    Debug(c) << "   Inst constants: ";
    for( int i=0; i<(int)d_quantEngine->getTermDatabase()->getNumInstantiationConstants( f ); i++ ){
      if( i>0 ){
        Debug( c ) << ", ";
      }
      Debug( c ) << d_quantEngine->getTermDatabase()->getInstantiationConstant( f, i );
    }
    Debug(c) << std::endl;
    for( int j=0; j<d_quantEngine->getTermDatabase()->getNumInstantiationConstants( f ); j++ ){
      Node ic = d_quantEngine->getTermDatabase()->getInstantiationConstant( f, j );
      Debug(c) << "   Instantiation rows for " << ic << " : ";
      for( int i=0; i<(int)d_instRows[ic].size(); i++ ){
        if( i>0 ){
          Debug(c) << ", ";
        }
        Debug(c) << d_instRows[ic][i];
      }
      Debug(c) << std::endl;
    }
  }
}

//say instantiation row x for quantifier f is coeff*var + A*t[e] + term = beta,
// where var is an instantiation constant from f,
// t[e] is a vector of terms containing instantiation constants from f,
// and term is a ground term (c1*t1 + ... + cn*tn).
// We construct the term ( beta - term )/coeff to use as an instantiation for var.
bool InstStrategySimplex::doInstantiation( Node f, Node ic, Node term, ArithVar x, InstMatch& m, Node var ){
  //first try +delta
  if( doInstantiation2( f, ic, term, x, m, var ) ){
    ++(d_quantEngine->getInstantiationEngine()->d_statistics.d_instantiations_cbqi_arith);
    return true;
  }else{
#ifdef ARITH_INSTANTIATOR_USE_MINUS_DELTA
    //otherwise try -delta
    if( doInstantiation2( f, ic, term, x, m, var, true ) ){
      ++(d_quantEngine->getInstantiationEngine()->d_statistics.d_instantiations_cbqi_arith_minus);
      return true;
    }else{
      return false;
    }
#else
    return false;
#endif
  }
}

bool InstStrategySimplex::doInstantiation2( Node f, Node ic, Node term, ArithVar x, InstMatch& m, Node var, bool minus_delta ){
  // make term ( beta - term )/coeff
  bool vIsInteger = var.getType().isInteger();
  Node beta = getTableauxValue( x, minus_delta );
  if( !vIsInteger || beta.getType().isInteger() ){
    Node instVal = NodeManager::currentNM()->mkNode( MINUS, beta, term );
    if( !d_ceTableaux[ic][x][var].isNull() ){
      if( vIsInteger ){
        Assert( d_ceTableaux[ic][x][var]==NodeManager::currentNM()->mkConst( Rational(-1) ) );
        instVal = NodeManager::currentNM()->mkNode( MULT, d_ceTableaux[ic][x][var], instVal );
      }else{
        Assert( d_ceTableaux[ic][x][var].getKind()==CONST_RATIONAL );
        Node coeff = NodeManager::currentNM()->mkConst( Rational(1) / d_ceTableaux[ic][x][var].getConst<Rational>() );
        instVal = NodeManager::currentNM()->mkNode( MULT, coeff, instVal );
      }
    }
    instVal = Rewriter::rewrite( instVal );
    //use as instantiation value for var
    int vn = var.getAttribute(InstVarNumAttribute());
    m.setValue( vn, instVal );
    Debug("quant-arith") << "Add instantiation " << m << std::endl;
    return d_quantEngine->addInstantiation( f, m );
  }else{
    return false;
  }
}
/*
Node InstStrategySimplex::getTableauxValue( Node n, bool minus_delta ){
  if( d_th->d_internal->d_partialModel.hasArithVar(n) ){
    ArithVar v = d_th->d_internal->d_partialModel.asArithVar( n );
    return getTableauxValue( v, minus_delta );
  }else{
    return NodeManager::currentNM()->mkConst( Rational(0) );
  }
}
*/
Node InstStrategySimplex::getTableauxValue( ArithVar v, bool minus_delta ){
  const Rational& delta = d_th->d_internal->d_partialModel.getDelta();
  DeltaRational drv = d_th->d_internal->d_partialModel.getAssignment( v );
  Rational qmodel = drv.substituteDelta( minus_delta ? -delta : delta );
  return mkRationalNode(qmodel);
}



//new implementation

bool CegqiOutputInstStrategy::addInstantiation( std::vector< Node >& subs ) {
  return d_out->addInstantiation( subs );
}

bool CegqiOutputInstStrategy::isEligibleForInstantiation( Node n ) {
  return d_out->isEligibleForInstantiation( n );
}

bool CegqiOutputInstStrategy::addLemma( Node lem ) {
  return d_out->addLemma( lem );
}


InstStrategyCegqi::InstStrategyCegqi( QuantifiersEngine * qe ) : InstStrategy( qe ) {
  d_out = new CegqiOutputInstStrategy( this );
  d_small_const = NodeManager::currentNM()->mkConst( Rational(1)/Rational(1000000) );
}

void InstStrategyCegqi::processResetInstantiationRound( Theory::Effort effort ) {
  d_check_vts_lemma_lc = true;
}

int InstStrategyCegqi::process( Node f, Theory::Effort effort, int e ) {
  if( e<1 ){
    return STATUS_UNFINISHED;
  }else if( e==1 ){
    CegInstantiator * cinst = getInstantiator( f );
    Trace("inst-alg") << "-> Run cegqi for " << f << std::endl;
    d_curr_quant = f;
    bool addedLemma = cinst->check();
    d_curr_quant = Node::null();
    return addedLemma ? STATUS_UNKNOWN : STATUS_UNFINISHED;
  }else if( e==2 ){
    //minimize the free delta heuristically on demand
    if( d_check_vts_lemma_lc ){
      d_check_vts_lemma_lc = false;
      d_small_const = NodeManager::currentNM()->mkNode( MULT, d_small_const, d_small_const );
      d_small_const = Rewriter::rewrite( d_small_const );
      //heuristic for now, until we know how to do nested quantification
      Node delta = d_quantEngine->getTermDatabase()->getVtsDelta( true, false );
      if( !delta.isNull() ){
        Trace("quant-vts-debug") << "Delta lemma for " << d_small_const << std::endl;
        Node delta_lem_ub = NodeManager::currentNM()->mkNode( LT, delta, d_small_const );
        d_quantEngine->getOutputChannel().lemma( delta_lem_ub );
      }
      std::vector< Node > inf;
      d_quantEngine->getTermDatabase()->getVtsTerms( inf, true, false, false );
      for( unsigned i=0; i<inf.size(); i++ ){
        Trace("quant-vts-debug") << "Infinity lemma for " << inf[i] << " " << d_small_const << std::endl;
        Node inf_lem_lb = NodeManager::currentNM()->mkNode( GT, inf[i], NodeManager::currentNM()->mkConst( Rational(1)/d_small_const.getConst<Rational>() ) );
        d_quantEngine->getOutputChannel().lemma( inf_lem_lb );
      }
    }
  }
  return STATUS_UNKNOWN;
}

bool InstStrategyCegqi::addInstantiation( std::vector< Node >& subs ) {
  Assert( !d_curr_quant.isNull() );
  //check if we need virtual term substitution (if used delta or infinity)
  bool used_vts = d_quantEngine->getTermDatabase()->containsVtsTerm( subs, false );
  return d_quantEngine->addInstantiation( d_curr_quant, subs, false, false, false, used_vts );
}

bool InstStrategyCegqi::addLemma( Node lem ) {
  return d_quantEngine->addLemma( lem );
}

bool InstStrategyCegqi::isEligibleForInstantiation( Node n ) {
  if( n.getKind()==INST_CONSTANT || n.getKind()==SKOLEM ){
    //only legal if current quantified formula contains n
    return TermDb::containsTerm( d_curr_quant, n );
  }else{
    return true;
  }
}

CegInstantiator * InstStrategyCegqi::getInstantiator( Node q ) {
  std::map< Node, CegInstantiator * >::iterator it = d_cinst.find( q );
  if( it==d_cinst.end() ){
    CegInstantiator * cinst = new CegInstantiator( d_quantEngine, d_out, true, true );
    d_cinst[q] = cinst;
    return cinst;
  }else{
   return it->second;
  }
}

void InstStrategyCegqi::registerQuantifier( Node q ) {
  if( options::cbqiPreRegInst() ){
    //just get the instantiator
    getInstantiator( q );
  }
}

void InstStrategyCegqi::presolve() {
  if( options::cbqiPreRegInst() ){
    for( std::map< Node, CegInstantiator * >::iterator it = d_cinst.begin(); it != d_cinst.end(); ++it ){
      it->second->presolve( it->first );
    }
  }
}
