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

CegInstantiator::CegInstantiator( QuantifiersEngine * qe, CegqiOutput * out ) : d_qe( qe ), d_out( out ){
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
      if( d_has_delta.find( n[i] )!=d_has_delta.end() ){
        d_has_delta[n] = true;
      }
      for( std::map< Node, bool >::iterator it = d_prog_var[n[i]].begin(); it != d_prog_var[n[i]].end(); ++it ){
        d_prog_var[n][it->first] = true;
      }
    }
    if( n==d_n_delta ){
      d_has_delta[n] = true;
    }
  }
}

bool CegInstantiator::addInstantiation( std::vector< Node >& subs, std::vector< Node >& vars,
                                        std::vector< Node >& coeff, std::vector< Node >& has_coeff, std::vector< int >& subs_typ,
                                        unsigned i, unsigned effort ){
  if( i==d_vars.size() ){
    return addInstantiationCoeff( subs, vars, coeff, has_coeff, subs_typ, 0 );
  }else{
    eq::EqualityEngine* ee = d_qe->getMasterEqualityEngine();
    std::map< int, std::map< Node, std::map< Node, bool > > > subs_proc;
    //Node v = d_single_inv_map_to_prog[d_single_inv[0][i]];
    Node pv = d_vars[i];
    TypeNode pvtn = pv.getType();

    if( (i+1)<d_vars.size() || effort!=2 ){
      //[1] easy case : pv is in the equivalence class as another term not containing pv
      if( ee->hasTerm( pv ) ){
        Node pvr = ee->getRepresentative( pv );
        eq::EqClassIterator eqc_i = eq::EqClassIterator( pvr, ee );
        while( !eqc_i.isFinished() ){
          Node n = *eqc_i;
          if( n!=pv ){
            Trace("cegqi-si-inst-debug") << "[1] " << i << "...try based on equal term " << n << std::endl;
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
                  proc = subs_proc[0][pv_coeff].find( ns )==subs_proc[0][pv_coeff].end() && d_prog_var[ns].find( pv )==d_prog_var[ns].end();
                }
              }else{
                ns = n;
                proc = true;
              }
              if( d_has_delta.find( ns )!=d_has_delta.end() ){
                //also must set delta to zero
                ns = ns.substitute( (TNode)d_n_delta, (TNode)d_zero );
                ns = Rewriter::rewrite( ns );
                computeProgVars( ns );
              }
              if( proc ){
                //try the substitution
                subs_proc[0][ns][pv_coeff] = true;
                if( addInstantiationInc( ns, pv, pv_coeff, 0, subs, vars, coeff, has_coeff, subs_typ, i, effort ) ){
                  return true;
                }
              }
            }
          }
          ++eqc_i;
        }
      }

      //[2] : we can solve an equality for pv
      ///iterate over equivalence classes to find cases where we can solve for the variable
      if( pvtn.isInteger() || pvtn.isReal() ){
        eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
        while( !eqcs_i.isFinished() ){
          Node r = *eqcs_i;
          TypeNode rtn = r.getType();
          if( rtn.isInteger() || rtn.isReal() ){
            std::vector< Node > lhs;
            std::vector< bool > lhs_v;
            std::vector< Node > lhs_coeff;
            eq::EqClassIterator eqc_i = eq::EqClassIterator( r, ee );
            while( !eqc_i.isFinished() ){
              Node n = *eqc_i;
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
                      Trace("cegqi-si-inst-debug") << "[2] " << i << "...try based on equality " << lhs[j] << " " << ns << std::endl;
                      Node eq_lhs = lhs[j];
                      Node eq_rhs = ns;
                      //make the same coefficient
                      if( pv_coeff!=lhs_coeff[j] ){
                        if( !pv_coeff.isNull() ){
                          Trace("cegqi-si-inst-debug") << "...mult lhs by " << pv_coeff << std::endl;
                          eq_lhs = NodeManager::currentNM()->mkNode( MULT, pv_coeff, eq_lhs );
                          eq_lhs = Rewriter::rewrite( eq_lhs );
                        }
                        if( !lhs_coeff[j].isNull() ){
                          Trace("cegqi-si-inst-debug") << "...mult rhs by " << lhs_coeff[j] << std::endl;
                          eq_rhs = NodeManager::currentNM()->mkNode( MULT, lhs_coeff[j], eq_rhs );
                          eq_rhs = Rewriter::rewrite( eq_rhs );
                        }
                      }
                      Node eq = eq_lhs.eqNode( eq_rhs );
                      eq = Rewriter::rewrite( eq );
                      Trace("cegqi-si-inst-debug") << "...equality is " << eq << std::endl;
                      std::map< Node, Node > msum;
                      if( QuantArith::getMonomialSumLit( eq, msum ) ){
                        if( !d_n_delta.isNull() ){
                          msum.erase( d_n_delta );
                        }
                        if( Trace.isOn("cegqi-si-inst-debug") ){
                          Trace("cegqi-si-inst-debug") << "...got monomial sum: " << std::endl;
                          QuantArith::debugPrintMonomialSum( msum, "cegqi-si-inst-debug" );
                          Trace("cegqi-si-inst-debug") << "isolate for " << pv << "..." << std::endl;
                        }
                        Node veq;
                        if( QuantArith::isolate( pv, msum, veq, EQUAL, true )!=0 ){
                          Trace("cegqi-si-inst-debug") << "...isolated equality " << veq << "." << std::endl;
                          Node veq_c;
                          if( veq[0]!=pv ){
                            Node veq_v;
                            if( QuantArith::getMonomial( veq[0], veq_c, veq_v ) ){
                              Assert( veq_v==pv );
                            }
                          }
                          if( subs_proc[0][veq[1]].find( veq_c )==subs_proc[0][veq[1]].end() ){
                            subs_proc[0][veq[1]][veq_c] = true;
                            if( addInstantiationInc( veq[1], pv, veq_c, 0, subs, vars, coeff, has_coeff, subs_typ, i, effort ) ){
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
              ++eqc_i;
            }
          }
          ++eqcs_i;
        }
      }

      //[3] directly look at assertions
      unsigned rmax = Theory::theoryOf( pv )==Theory::theoryOf( pv.getType() ) ? 1 : 2;
      for( unsigned r=0; r<rmax; r++ ){
        TheoryId tid = r==0 ? Theory::theoryOf( pv ) : Theory::theoryOf( pv.getType() );
        Theory* theory = d_qe->getTheoryEngine()->theoryOf( tid );
        Trace("cegqi-si-inst-debug2") << "Theory of " << pv << " (r=" << r << ") is " << tid << std::endl;
        if (theory && d_qe->getTheoryEngine()->isTheoryEnabled(tid)) {
          Trace("cegqi-si-inst-debug2") << "Look at assertions of " << tid << std::endl;
          context::CDList<Assertion>::const_iterator it = theory->facts_begin(), it_end = theory->facts_end();
          for (unsigned j = 0; it != it_end; ++ it, ++j) {
            Node lit = (*it).assertion;
            Trace("cegqi-si-inst-debug2") << "  look at " << lit << std::endl;
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
                //if it contains pv
                if( !atom_lhs.isNull() && d_prog_var[atom_lhs].find( pv )!=d_prog_var[atom_lhs].end() ){
                  Node satom = NodeManager::currentNM()->mkNode( atom.getKind(), atom_lhs, atom_rhs );
                  Trace("cegqi-si-inst-debug") << "[3] From assertion : " << atom << ", pol = " << pol << std::endl;
                  Trace("cegqi-si-inst-debug") << "       substituted : " << satom << ", pol = " << pol << std::endl;
                  std::map< Node, Node > msum;
                  if( QuantArith::getMonomialSumLit( satom, msum ) ){
                    if( !d_n_delta.isNull() ){
                      msum.erase( d_n_delta );
                    }
                    if( Trace.isOn("cegqi-si-inst-debug") ){
                      Trace("cegqi-si-inst-debug") << "...got monomial sum: " << std::endl;
                      QuantArith::debugPrintMonomialSum( msum, "cegqi-si-inst-debug" );
                      Trace("cegqi-si-inst-debug") << "isolate for " << pv << "..." << std::endl;
                    }
                    Node vatom;
                    //isolate pv in the inequality
                    int ires = QuantArith::isolate( pv, msum, vatom, atom.getKind(), true );
                    if( ires!=0 ){
                      Trace("cegqi-si-inst-debug") << "...isolated atom " << vatom << "." << std::endl;
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
                      //disequalities are both strict upper and lower bounds
                      unsigned rmax = atom.getKind()==GEQ ? 1 : 2;
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
                            }else if( pvtn.isReal() ){
                              //now is strict inequality
                              uires = uires*2;
                            }else{
                              Assert( false );
                            }
                          }
                        }else{
                          Assert( atom.getKind()==EQUAL && !pol );
                          if( pvtn.isInteger() ){
                            uires = r==0 ? -1 : 1;
                            uval = NodeManager::currentNM()->mkNode( PLUS, val, NodeManager::currentNM()->mkConst( Rational( uires ) ) );
                            uval = Rewriter::rewrite( uval );
                          }else if( pvtn.isReal() ){
                            uires = r==0 ? -2 : 2;
                          }else{
                            Assert( false );
                          }
                        }
                        if( subs_proc[uires][uval].find( veq_c )==subs_proc[uires][uval].end() ){
                          subs_proc[uires][uval][veq_c] = true;
                          if( addInstantiationInc( uval, pv, veq_c, uires, subs, vars, coeff, has_coeff, subs_typ, i, effort ) ){
                            return true;
                          }
                        }else{
                          Trace("cegqi-si-inst-debug") << "...already processed." << std::endl;
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

    //[4] resort to using value in model
    if( effort>0 ){
      Node mv = d_qe->getModel()->getValue( pv );
      Node pv_coeff_m;
      Trace("cegqi-si-inst-debug") << i << "[4] ...try model value " << mv << std::endl;
      return addInstantiationInc( mv, pv, pv_coeff_m, 9, subs, vars, coeff, has_coeff, subs_typ, i, 1 );
    }else{
      return false;
    }
  }
}


bool CegInstantiator::addInstantiationInc( Node n, Node pv, Node pv_coeff, int styp, std::vector< Node >& subs, std::vector< Node >& vars,
                                           std::vector< Node >& coeff, std::vector< Node >& has_coeff, std::vector< int >& subs_typ,
                                           unsigned i, unsigned effort ) {
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
        success = false;
        break;
      }
    }
  }
  if( success ){
    subs.push_back( n );
    vars.push_back( pv );
    coeff.push_back( pv_coeff );
    if( !pv_coeff.isNull() ){
      has_coeff.push_back( pv );
    }
    subs_typ.push_back( styp );
    Trace("cegqi-si-inst-debug") << i << ": ";
    if( !pv_coeff.isNull() ){
      Trace("cegqi-si-inst-debug") << pv_coeff << "*";
    }
    Trace("cegqi-si-inst-debug") << pv << " -> " << n << std::endl;
    success = addInstantiation( subs, vars, coeff, has_coeff, subs_typ, i+1, effort );
    if( !success ){
      subs.pop_back();
      vars.pop_back();
      coeff.pop_back();
      if( !pv_coeff.isNull() ){
        has_coeff.pop_back();
      }
      subs_typ.pop_back();
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
                                             std::vector< Node >& coeff, std::vector< Node >& has_coeff, std::vector< int >& subs_typ, unsigned j ) {
  if( j==has_coeff.size() ){
    return addInstantiation( subs, vars, subs_typ );
  }else{
    Assert( std::find( vars.begin(), vars.end(), has_coeff[j] )!=vars.end() );
    unsigned index = std::find( vars.begin(), vars.end(), has_coeff[j] )-vars.begin();
    Node prev = subs[index];
    Assert( !coeff[index].isNull() );
    Trace("cegqi-si-inst-debug") << "Normalize substitution for " << coeff[index] << " * " << vars[index] << " = " << subs[index] << ", stype = " << subs_typ[index] << std::endl;
    if( vars[index].getType().isInteger() ){
      //must ensure that divisibility constraints are met
      //solve updated rewritten equality for vars[index], if coefficient is one, then we are successful
      Node eq_lhs = NodeManager::currentNM()->mkNode( MULT, coeff[index], vars[index] );
      Node eq_rhs = subs[index];
      Node eq = eq_lhs.eqNode( eq_rhs );
      eq = Rewriter::rewrite( eq );
      Trace("cegqi-si-inst-debug") << "...equality is " << eq << std::endl;
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
            if( subs_typ[index]>=1 && subs_typ[index]<=2 ){
              subs[index] = NodeManager::currentNM()->mkNode( PLUS, subs[index],
                NodeManager::currentNM()->mkNode( ITE,
                  NodeManager::currentNM()->mkNode( EQUAL,
                    NodeManager::currentNM()->mkNode( INTS_MODULUS, veq[1], veq_c ),
                    d_zero ),
                  d_zero, d_one )
              );
            }
          }
          Trace("cegqi-si-inst-debug") << "...normalize integers : " << subs[index] << std::endl;
          if( addInstantiationCoeff( subs, vars, coeff, has_coeff, subs_typ, j+1 ) ){
            return true;
          }
            //equalities are both upper and lower bounds
            /*
            if( subs_typ[index]==0 && !veq_c.isNull() ){
              subs[index] = NodeManager::currentNM()->mkNode( PLUS, subs[index],
                NodeManager::currentNM()->mkNode( ITE,
                  NodeManager::currentNM()->mkNode( EQUAL,
                    NodeManager::currentNM()->mkNode( INTS_MODULUS, veq[1], veq_c ),
                    NodeManager::currentNM()->mkConst( Rational( 0 ) ) ),
                  NodeManager::currentNM()->mkConst( Rational( 0 ) ),
                  NodeManager::currentNM()->mkConst( Rational( 1 ) ) )
              );
              if( addInstantiationCoeff( subs, vars, coeff, has_coeff, subs_typ, j+1 ) ){
                return true;
              }
            }
            */
        }
      }
    }else if( vars[index].getType().isReal() ){
      // can always invert
      subs[index] = NodeManager::currentNM()->mkNode( MULT, NodeManager::currentNM()->mkConst( Rational(1) / coeff[index].getConst<Rational>() ), subs[index] );
      subs[index] = Rewriter::rewrite( subs[index] );
      Trace("cegqi-si-inst-debug") << "...success, reals : " << subs[index] << std::endl;
      if( addInstantiationCoeff( subs, vars, coeff, has_coeff, subs_typ, j+1 ) ){
        return true;
      }
    }else{
      Assert( false );
    }
    subs[index] = prev;
    Trace("cegqi-si-inst-debug") << "...failed." << std::endl;
    return false;
  }
}

bool CegInstantiator::addInstantiation( std::vector< Node >& subs, std::vector< Node >& vars, std::vector< int >& subs_typ ) {
  // do delta rationals
  std::map< int, Node > prev;
  for( unsigned i=0; i<subs.size(); i++ ){
    if( subs_typ[i]==2 || subs_typ[i]==-2 ){
      prev[i] = subs[i];
      if( d_n_delta.isNull() ){
        d_n_delta = NodeManager::currentNM()->mkSkolem( "delta", vars[i].getType(), "delta for cegqi" );
        Node delta_lem = NodeManager::currentNM()->mkNode( GT, d_n_delta, d_zero );
        d_qe->getOutputChannel().lemma( delta_lem );
      }
      subs[i] = NodeManager::currentNM()->mkNode( subs_typ[i]==2 ? PLUS : MINUS, subs[i], d_n_delta );
    }
  }
  //check if we have already added this instantiation
  bool success = d_out->addInstantiation( subs, subs_typ );
  if( !success ){
    //revert the substitution
    for( std::map< int, Node >::iterator it = prev.begin(); it != prev.end(); ++it ){
      subs[it->first] = it->second;
    }
  }
  return success;
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

//check if delta has a lower bound L
// if so, add lemma L>0 => L>d
void CegInstantiator::getDeltaLemmas( std::vector< Node >& lems ) {
  if( !d_n_delta.isNull() ){
    Theory* theory = d_qe->getTheoryEngine()->theoryOf( THEORY_ARITH );
    if( theory && d_qe->getTheoryEngine()->isTheoryEnabled( THEORY_ARITH ) ){
      context::CDList<Assertion>::const_iterator it = theory->facts_begin(), it_end = theory->facts_end();
      for (unsigned j = 0; it != it_end; ++ it, ++j) {
        Node lit = (*it).assertion;
        Node atom = lit.getKind()==NOT ? lit[0] : lit;
        bool pol = lit.getKind()!=NOT;
        if( atom.getKind()==GEQ || ( pol && atom.getKind()==EQUAL ) ){
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
          //must be an eligible term with delta
          if( d_inelig.find( atom_lhs )==d_inelig.end() && d_has_delta.find( atom_lhs )!=d_has_delta.end() ){
            Node satom = NodeManager::currentNM()->mkNode( atom.getKind(), atom_lhs, atom_rhs );
            Trace("cegqi-delta") << "Delta assertion : " << atom << ", pol = " << pol << std::endl;
            std::map< Node, Node > msum;
            if( QuantArith::getMonomialSumLit( satom, msum ) ){
              Node vatom;
              //isolate delta in the inequality
              int ires = QuantArith::isolate( d_n_delta, msum, vatom, atom.getKind(), true );
              if( ((ires==1)==pol) || ( ires!=0 && lit.getKind()==EQUAL ) ){
                Node val = vatom[ ires==1 ? 1 : 0 ];
                Node pvm = vatom[ ires==1 ? 0 : 1 ];
                //get monomial
                if( pvm!=d_n_delta ){
                  Node veq_c;
                  Node veq_v;
                  if( QuantArith::getMonomial( pvm, veq_c, veq_v ) ){
                    Assert( veq_v==d_n_delta );
                    val = NodeManager::currentNM()->mkNode( MULT, val, NodeManager::currentNM()->mkConst( Rational(1) / veq_c.getConst<Rational>() ) );
                    val = Rewriter::rewrite( val );
                  }else{
                    val = Node::null();
                  }
                }
                if( !val.isNull()  ){
                  Node lem1 = NodeManager::currentNM()->mkNode( GT, val, d_zero );
                  lem1 = Rewriter::rewrite( lem1 );
                  if( !lem1.isConst() || lem1==d_true ){
                    Node lem2 = NodeManager::currentNM()->mkNode( GT, val, d_n_delta );
                    Node lem = lem1==d_true ? lem2 : NodeManager::currentNM()->mkNode( OR, lem1.negate(), lem2 );
                    lems.push_back( lem );
                    Trace("cegqi-delta") << "...lemma : " << lem << std::endl;
                  }
                }
              }else{
                Trace("cegqi-delta") << "...wrong polarity." << std::endl;
              }
            }
          }
        }
      }
    }
  }
}

void CegInstantiator::check() {

  for( unsigned r=0; r<2; r++ ){
    std::vector< Node > subs;
    std::vector< Node > vars;
    std::vector< Node > coeff;
    std::vector< Node > has_coeff;
    std::vector< int > subs_typ;
    //try to add an instantiation
    if( addInstantiation( subs, vars, coeff, has_coeff, subs_typ, 0, r==0 ? 0 : 2 ) ){
      return;
    }
  }
  Trace("cegqi-engine") << "  WARNING : unable to find CEGQI single invocation instantiation." << std::endl;
}


bool CegqiOutputSingleInv::addInstantiation( std::vector< Node >& subs, std::vector< int >& subs_typ ) {
  return d_out->addInstantiation( subs, subs_typ );
}

bool CegqiOutputSingleInv::isEligibleForInstantiation( Node n ) {
  return d_out->isEligibleForInstantiation( n );
}

bool CegqiOutputSingleInv::addLemma( Node n ) {
  return d_out->addLemma( n );
}


CegConjectureSingleInv::CegConjectureSingleInv( CegConjecture * p ) : d_parent( p ){
  d_sol = NULL;
  d_c_inst_match_trie = NULL;
  d_cinst = NULL;
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
    inst = TermDb::simpleNegate( inst );
    Trace("cegqi-si") << "Single invocation initial lemma : " << inst << std::endl;

    //initialize the instantiator for this
    CegqiOutputSingleInv * cosi = new CegqiOutputSingleInv( this );
    d_cinst = new CegInstantiator( d_qe, cosi );
    d_cinst->d_vars.insert( d_cinst->d_vars.end(), d_single_inv_sk.begin(), d_single_inv_sk.end() );

    return NodeManager::currentNM()->mkNode( OR, guard.negate(), inst );
  }else{
    return Node::null();
  }
}

void CegConjectureSingleInv::initialize( QuantifiersEngine * qe, Node q ) {
  //initialize data
  d_sol = new CegConjectureSingleInvSol( qe );
  d_qe = qe;
  d_quant = q;
  if( options::incrementalSolving() ){
    d_c_inst_match_trie = new inst::CDInstMatchTrie( qe->getUserContext() );
  }
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
          curr = TermDb::simpleNegate( curr );
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
          if( options::eMatching.wasSetByUser() ){
            Node bd = d_qe->getTermDatabase()->getInstConstantBody( d_single_inv );
            std::vector< Node > patTerms;
            std::vector< Node > exclude;
            inst::Trigger::collectPatTerms( d_qe, d_single_inv, bd, patTerms, inst::Trigger::TS_ALL, exclude );
            if( !patTerms.empty() ){
              Trace("cegqi-si-em") << "Triggers : " << std::endl;
              for( unsigned i=0; i<patTerms.size(); i++ ){
                Trace("cegqi-si-em") << "   " << patTerms[i] << std::endl;
              }
            }
          }
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

bool CegConjectureSingleInv::addInstantiation( std::vector< Node >& subs, std::vector< int >& subs_typ ){
  std::stringstream siss;
  if( Trace.isOn("cegqi-si-inst-debug") || Trace.isOn("cegqi-engine") ){
    siss << "  * single invocation: " << std::endl;
    for( unsigned j=0; j<d_single_inv_sk.size(); j++ ){
      Node v = d_single_inv_map_to_prog[d_single_inv[0][j]];
      siss << "    * " << v;
      siss << " (" << d_single_inv_sk[j] << ")";
      siss << " -> " << ( subs_typ[j]==9 ? "M:" : "") << subs[j] << std::endl;
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
    Assert( d_cinst!=NULL );
    d_curr_lemmas.clear();
    //check if there are delta lemmas
    d_cinst->getDeltaLemmas( lems );
    //if not, do ce-guided instantiation
    if( lems.empty() ){
      //call check for instantiator
      d_cinst->check();
      //add lemmas
      lems.insert( lems.end(), d_curr_lemmas.begin(), d_curr_lemmas.end() );
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
    cond = TermDb::simpleNegate( cond );
    Node ite1 = d_inst[index][i];
    Node ite2 = constructSolution( i, index+1 );
    return NodeManager::currentNM()->mkNode( ITE, cond, ite1, ite2 );
  }
}

Node CegConjectureSingleInv::getSolution( unsigned sol_index, TypeNode stn, int& reconstructed ){
  Assert( d_sol!=NULL );
  Assert( !d_lemmas_produced.empty() );
  const Datatype& dt = ((DatatypeType)(stn).toType()).getDatatype();
  Node varList = Node::fromExpr( dt.getSygusVarList() );
  Node prog = d_quant[0][sol_index];
  Node prog_app = d_single_inv_app_map[prog];
  //get variables
  std::vector< Node > vars;
  Trace("csi-sol") << "Get solution for " << prog << ", which is applied as " << prog_app << std::endl;
  Assert( prog_app.getNumChildren()==varList.getNumChildren()+1 );
  d_varList.clear();
  d_sol->d_varList.clear();
  for( unsigned i=1; i<prog_app.getNumChildren(); i++ ){
    if( varList[i-1].getType().isBoolean() ){
      //TODO force boolean term conversion mode
      Node c = NodeManager::currentNM()->mkConst(BitVector(1u, 1u));
      vars.push_back( prog_app[i].eqNode( c ) );
    }else{
      vars.push_back( prog_app[i] );
    }
    d_varList.push_back( varList[i-1] );
    d_sol->d_varList.push_back( varList[i-1] );
  }
  //construct the solution
  Node s = constructSolution( sol_index, 0 );
  s = s.substitute( vars.begin(), vars.end(), d_varList.begin(), d_varList.end() );
  d_orig_solution = s;

  //simplify the solution
  Trace("csi-sol") << "Solution (pre-simplification): " << d_orig_solution << std::endl;
  s = d_sol->simplifySolution( s, stn );
  Trace("csi-sol") << "Solution (post-simplification): " << s << std::endl;
  d_solution = s;

  //reconstruct the solution into sygus if necessary
  reconstructed = 0;
  if( options::cegqiSingleInvReconstruct() && !stn.isNull() ){
    d_sygus_solution = d_sol->reconstructSolution( s, stn, reconstructed );
    if( reconstructed==1 ){
      Trace("csi-sol") << "Solution (post-reconstruction into Sygus): " << d_sygus_solution << std::endl;
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

}