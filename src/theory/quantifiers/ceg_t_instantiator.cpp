/*********************                                                        */
/*! \file ceg_t_instantiator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of theory-specific counterexample-guided quantifier instantiation
 **/
 
#include "theory/quantifiers/ceg_t_instantiator.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/trigger.h"

#include "theory/arith/partial_model.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/theory_arith_private.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

Node ArithInstantiator::getModelBasedProjectionValue( CegInstantiator * ci, Node e, Node t, bool isLower, Node c, Node me, Node mt, Node theta, Node inf_coeff, Node delta_coeff ) {
  Node val = t;
  Trace("cbqi-bound2") << "Value : " << val << std::endl;
  Assert( !e.getType().isInteger() || t.getType().isInteger() );
  Assert( !e.getType().isInteger() || mt.getType().isInteger() );
  //add rho value
  //get the value of c*e
  Node ceValue = me;
  Node new_theta = theta;
  if( !c.isNull() ){
    Assert( c.getType().isInteger() );
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
  if( !new_theta.isNull() && e.getType().isInteger() ){
    Node rho;
    //if( !mt.getType().isInteger() ){
      //round up/down
      //mt = NodeManager::currentNM()->mkNode(
    //}
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
    Assert( !d_vts_sym[0].isNull() );
    val = NodeManager::currentNM()->mkNode( PLUS, val, NodeManager::currentNM()->mkNode( MULT, inf_coeff, d_vts_sym[0] ) );
    val = Rewriter::rewrite( val );
  }
  if( !delta_coeff.isNull() ){
    //create delta here if necessary
    val = NodeManager::currentNM()->mkNode( PLUS, val, NodeManager::currentNM()->mkNode( MULT, delta_coeff, ci->getQuantifiersEngine()->getTermDatabase()->getVtsDelta() ) );
    val = Rewriter::rewrite( val );
  }
  return val;
}

//this isolates the atom into solved form
//     veq_c * pv <> val + vts_coeff_delta * delta + vts_coeff_inf * inf
//  ensures val is Int if pv is Int, and val does not contain vts symbols
int ArithInstantiator::solve_arith( CegInstantiator * ci, Node pv, Node atom, Node& veq_c, Node& val, Node& vts_coeff_inf, Node& vts_coeff_delta ) {
  int ires = 0;
  Trace("cbqi-inst-debug") << "isolate for " << pv << " in " << atom << std::endl;
  std::map< Node, Node > msum;
  if( QuantArith::getMonomialSumLit( atom, msum ) ){
    Trace("cbqi-inst-debug") << "got monomial sum: " << std::endl;
    if( Trace.isOn("cbqi-inst-debug") ){
      QuantArith::debugPrintMonomialSum( msum, "cbqi-inst-debug" );
    }
    TypeNode pvtn = pv.getType();
    //remove vts symbols from polynomial
    Node vts_coeff[2];
    for( unsigned t=0; t<2; t++ ){
      if( !d_vts_sym[t].isNull() ){
        std::map< Node, Node >::iterator itminf = msum.find( d_vts_sym[t] );
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
          msum.erase( d_vts_sym[t] );
        }
      }
    }

    ires = QuantArith::isolate( pv, msum, veq_c, val, atom.getKind() );
    if( ires!=0 ){
      Node realPart;
      if( Trace.isOn("cbqi-inst-debug") ){
        Trace("cbqi-inst-debug") << "Isolate : ";
        if( !veq_c.isNull() ){
          Trace("cbqi-inst-debug") << veq_c << " * ";
        }
        Trace("cbqi-inst-debug") << pv << " " << atom.getKind() << " " << val << std::endl;
      }
      if( options::cbqiAll() ){
        // when not pure LIA/LRA, we must check whether the lhs contains pv
        if( TermDb::containsTerm( val, pv ) ){
          Trace("cbqi-inst-debug") << "fail : contains bad term" << std::endl;
          return 0;
        }
      }
      if( pvtn.isInteger() && ( ( !veq_c.isNull() && !veq_c.getType().isInteger() ) || !val.getType().isInteger() ) ){
        //redo, split integer/non-integer parts
        bool useCoeff = false;
        Integer coeff = ci->getQuantifiersEngine()->getTermDatabase()->d_one.getConst<Rational>().getNumerator();
        for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
          if( it->first.isNull() || it->first.getType().isInteger() ){
            if( !it->second.isNull() ){
              coeff = coeff.lcm( it->second.getConst<Rational>().getDenominator() );
              useCoeff = true;
            }
          }
        }
        //multiply everything by this coefficient
        Node rcoeff = NodeManager::currentNM()->mkConst( Rational( coeff ) );
        std::vector< Node > real_part;
        for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
          if( useCoeff ){
            if( it->second.isNull() ){
              msum[it->first] = rcoeff;
            }else{
              msum[it->first] = Rewriter::rewrite( NodeManager::currentNM()->mkNode( MULT, it->second, rcoeff ) );
            }
          }
          if( !it->first.isNull() && !it->first.getType().isInteger() ){
            real_part.push_back( msum[it->first].isNull() ? it->first : NodeManager::currentNM()->mkNode( MULT, msum[it->first], it->first ) );
          }
        }
        //remove delta  TODO: check this
        vts_coeff[1] = Node::null();
        //multiply inf
        if( !vts_coeff[0].isNull() ){
          vts_coeff[0] = Rewriter::rewrite( NodeManager::currentNM()->mkNode( MULT, rcoeff, vts_coeff[0] ) );
        }
        realPart = real_part.empty() ? ci->getQuantifiersEngine()->getTermDatabase()->d_zero : ( real_part.size()==1 ? real_part[0] : NodeManager::currentNM()->mkNode( PLUS, real_part ) );
        Assert( ci->getOutput()->isEligibleForInstantiation( realPart ) );
        //re-isolate
        Trace("cbqi-inst-debug") << "Re-isolate..." << std::endl;
        ires = QuantArith::isolate( pv, msum, veq_c, val, atom.getKind() );
        Trace("cbqi-inst-debug") << "Isolate for mixed Int/Real : " << veq_c << " * " << pv << " " << atom.getKind() << " " << val << std::endl;
        Trace("cbqi-inst-debug") << "                 real part : " << realPart << std::endl;
        if( ires!=0 ){
          int ires_use = ( msum[pv].isNull() || msum[pv].getConst<Rational>().sgn()==1 ) ? 1 : -1;
          val = Rewriter::rewrite( NodeManager::currentNM()->mkNode( ires_use==-1 ? PLUS : MINUS,
                                    NodeManager::currentNM()->mkNode( ires_use==-1 ? MINUS : PLUS, val, realPart ),
                                    NodeManager::currentNM()->mkNode( TO_INTEGER, realPart ) ) );  //TODO: round up for upper bounds?
          Trace("cbqi-inst-debug") << "result : " << val << std::endl;
          Assert( val.getType().isInteger() );
        }
      }
    }
    vts_coeff_inf = vts_coeff[0];
    vts_coeff_delta = vts_coeff[1];
    Trace("cbqi-inst-debug") << "Return " << veq_c << " * " << pv << " " << atom.getKind() << " " << val << ", vts = (" << vts_coeff_inf << ", " << vts_coeff_delta << ")" << std::endl;
  }else{
    Trace("cbqi-inst-debug") << "fail : could not get monomial sum" << std::endl;
  }
  return ires;
}

void ArithInstantiator::reset( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) {
  d_vts_sym[0] = ci->getQuantifiersEngine()->getTermDatabase()->getVtsInfinity( d_type, false, false );
  d_vts_sym[1] = ci->getQuantifiersEngine()->getTermDatabase()->getVtsDelta( false, false );
  for( unsigned i=0; i<2; i++ ){
    d_mbp_bounds[i].clear();
    d_mbp_coeff[i].clear();
    for( unsigned j=0; j<2; j++ ){
      d_mbp_vts_coeff[i][j].clear();
    }
    d_mbp_lit[i].clear();
  }
}

bool ArithInstantiator::processEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& term_coeffs, std::vector< Node >& terms, unsigned effort ) {
  Node eq_lhs = terms[0];
  Node eq_rhs = terms[1];
  Node lhs_coeff = term_coeffs[0];
  Node rhs_coeff = term_coeffs[1];
  //make the same coefficient
  if( rhs_coeff!=lhs_coeff ){
    if( !rhs_coeff.isNull() ){
      Trace("cbqi-inst-debug") << "...mult lhs by " << rhs_coeff << std::endl;
      eq_lhs = NodeManager::currentNM()->mkNode( MULT, rhs_coeff, eq_lhs );
      eq_lhs = Rewriter::rewrite( eq_lhs );
    }
    if( !lhs_coeff.isNull() ){
      Trace("cbqi-inst-debug") << "...mult rhs by " << lhs_coeff << std::endl;
      eq_rhs = NodeManager::currentNM()->mkNode( MULT, lhs_coeff, eq_rhs );
      eq_rhs = Rewriter::rewrite( eq_rhs );
    }
  }
  Node eq = eq_lhs.eqNode( eq_rhs );
  eq = Rewriter::rewrite( eq );
  Node val;
  Node veq_c;
  Node vts_coeff_inf;
  Node vts_coeff_delta;
  //isolate pv in the equality
  int ires = solve_arith( ci, pv, eq, veq_c, val, vts_coeff_inf, vts_coeff_delta );
  if( ires!=0 ){
    if( ci->doAddInstantiationInc( pv, val, veq_c, 0, sf, effort ) ){
      return true;
    }
  }

  return false;
}

bool ArithInstantiator::processAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort ) {
  Trace("cbqi-inst-debug2") << "  look at " << lit << std::endl;
  Node atom = lit.getKind()==NOT ? lit[0] : lit;
  bool pol = lit.getKind()!=NOT;
  //arithmetic inequalities and disequalities
  if( atom.getKind()==GEQ || ( atom.getKind()==EQUAL && !pol && atom[0].getType().isReal() ) ){
    Assert( atom.getKind()!=GEQ || atom[1].isConst() );
    Node atom_lhs;
    Node atom_rhs;
    if( atom.getKind()==GEQ ){
      atom_lhs = atom[0];
      atom_rhs = atom[1];
    }else{
      atom_lhs = NodeManager::currentNM()->mkNode( MINUS, atom[0], atom[1] );
      atom_lhs = Rewriter::rewrite( atom_lhs );
      atom_rhs = ci->getQuantifiersEngine()->getTermDatabase()->d_zero;
    }
    //must be an eligible term
    if( ci->isEligible( atom_lhs ) ){
      //apply substitution to LHS of atom
      Node atom_lhs_coeff;
      atom_lhs = ci->applySubstitution( d_type, atom_lhs, sf, atom_lhs_coeff );
      if( !atom_lhs.isNull() ){
        if( !atom_lhs_coeff.isNull() ){
          atom_rhs = Rewriter::rewrite( NodeManager::currentNM()->mkNode( MULT, atom_lhs_coeff, atom_rhs ) );
        }
      }
      //if it contains pv, not infinity
      if( !atom_lhs.isNull() && ci->hasVariable( atom_lhs, pv ) ){
        Node pv_value = ci->getModelValue( pv );
        Node satom = NodeManager::currentNM()->mkNode( atom.getKind(), atom_lhs, atom_rhs );
        //cannot contain infinity?
        Trace("cbqi-inst-debug") << "..[3] From assertion : " << atom << ", pol = " << pol << std::endl;
        Trace("cbqi-inst-debug") << "         substituted : " << satom << ", pol = " << pol << std::endl;
        Node vts_coeff_inf;
        Node vts_coeff_delta;
        Node val;
        Node veq_c;
        //isolate pv in the inequality
        int ires = solve_arith( ci, pv, satom, veq_c, val, vts_coeff_inf, vts_coeff_delta );
        if( ires!=0 ){
          //disequalities are either strict upper or lower bounds
          unsigned rmax = ( atom.getKind()==GEQ || options::cbqiModel() ) ? 1 : 2;
          for( unsigned r=0; r<rmax; r++ ){
            int uires = ires;
            Node uval = val;
            if( atom.getKind()==GEQ ){
              //push negation downwards
              if( !pol ){
                uires = -ires;
                if( d_type.isInteger() ){
                  uval = NodeManager::currentNM()->mkNode( PLUS, val, NodeManager::currentNM()->mkConst( Rational( uires ) ) );
                  uval = Rewriter::rewrite( uval );
                }else{
                  Assert( d_type.isReal() );
                  //now is strict inequality
                  uires = uires*2;
                }
              }
            }else{
              bool is_upper;
              if( options::cbqiModel() ){
                // disequality is a disjunction : only consider the bound in the direction of the model
                //first check if there is an infinity...
                if( !vts_coeff_inf.isNull() ){
                  //coefficient or val won't make a difference, just compare with zero
                  Trace("cbqi-inst-debug") << "Disequality : check infinity polarity " << vts_coeff_inf << std::endl;
                  Assert( vts_coeff_inf.isConst() );
                  is_upper = ( vts_coeff_inf.getConst<Rational>().sgn()==1 );
                }else{
                  Node rhs_value = ci->getModelValue( val );
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
                  is_upper = ( cmp!=ci->getQuantifiersEngine()->getTermDatabase()->d_true );
                }
              }else{
                is_upper = (r==0);
              }
              Assert( atom.getKind()==EQUAL && !pol );
              if( d_type.isInteger() ){
                uires = is_upper ? -1 : 1;
                uval = NodeManager::currentNM()->mkNode( PLUS, val, NodeManager::currentNM()->mkConst( Rational( uires ) ) );
                uval = Rewriter::rewrite( uval );
              }else{
                Assert( d_type.isReal() );
                uires = is_upper ? -2 : 2;
              }
            }
            Trace("cbqi-bound-inf") << "From " << lit << ", got : ";
            if( !veq_c.isNull() ){
              Trace("cbqi-bound-inf") << veq_c << " * ";
            }
            Trace("cbqi-bound-inf") << pv << " -> " << uval << ", styp = " << uires << std::endl;
            //take into account delta
            if( ci->useVtsDelta() && ( uires==2 || uires==-2 ) ){
              if( options::cbqiModel() ){
                Node delta_coeff = NodeManager::currentNM()->mkConst( Rational( uires > 0 ? 1 : -1 ) );
                if( vts_coeff_delta.isNull() ){
                  vts_coeff_delta = delta_coeff;
                }else{
                  vts_coeff_delta = NodeManager::currentNM()->mkNode( PLUS, vts_coeff_delta, delta_coeff );
                  vts_coeff_delta = Rewriter::rewrite( vts_coeff_delta );
                }
              }else{
                Node delta = ci->getQuantifiersEngine()->getTermDatabase()->getVtsDelta();
                uval = NodeManager::currentNM()->mkNode( uires==2 ? PLUS : MINUS, uval, delta );
                uval = Rewriter::rewrite( uval );
              }
            }
            if( options::cbqiModel() ){
              //just store bounds, will choose based on tighest bound
              unsigned index = uires>0 ? 0 : 1;
              d_mbp_bounds[index].push_back( uval );
              d_mbp_coeff[index].push_back( veq_c );
              Trace("cbqi-inst-debug") << "Store bound " << index << " " << uval << " " << veq_c << " " << vts_coeff_inf << " " << vts_coeff_delta << " " << lit << std::endl;
              for( unsigned t=0; t<2; t++ ){
                d_mbp_vts_coeff[index][t].push_back( t==0 ? vts_coeff_inf : vts_coeff_delta );
              }
              d_mbp_lit[index].push_back( lit );
            }else{
              //try this bound
              if( ci->doAddInstantiationInc( pv, uval, veq_c, uires>0 ? 1 : -1, sf, effort ) ){
                return true;
              }
            }
          }
        }
      }
    }
  }


  return false;
}

bool ArithInstantiator::processAssertions( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& lits, unsigned effort ) {
 if( options::cbqiModel() ){
    bool use_inf = ci->useVtsInfinity() && ( d_type.isInteger() ? options::cbqiUseInfInt() : options::cbqiUseInfReal() );
    bool upper_first = false;
    if( options::cbqiMinBounds() ){
      upper_first = d_mbp_bounds[1].size()<d_mbp_bounds[0].size();
    }
    int best_used[2];
    std::vector< Node > t_values[3];
    Node zero = ci->getQuantifiersEngine()->getTermDatabase()->d_zero;
    Node one = ci->getQuantifiersEngine()->getTermDatabase()->d_one;
    Node pv_value = ci->getModelValue( pv );
    //try optimal bounds
    for( unsigned r=0; r<2; r++ ){
      int rr = upper_first ? (1-r) : r;
      best_used[rr] = -1;
      if( d_mbp_bounds[rr].empty() ){
        if( use_inf ){
          Trace("cbqi-bound") << "No " << ( rr==0 ? "lower" : "upper" ) << " bounds for " << pv << " (type=" << d_type << ")" << std::endl;
          //no bounds, we do +- infinity
          Node val = ci->getQuantifiersEngine()->getTermDatabase()->getVtsInfinity( d_type );
          //TODO : rho value for infinity?
          if( rr==0 ){
            val = NodeManager::currentNM()->mkNode( UMINUS, val );
            val = Rewriter::rewrite( val );
          }
          if( ci->doAddInstantiationInc( pv, val, Node::null(), 0, sf, effort ) ){
            return true;
          }
        }
      }else{
        Trace("cbqi-bound") << ( rr==0 ? "Lower" : "Upper" ) << " bounds for " << pv << " (type=" << d_type << ") : " << std::endl;
        int best = -1;
        Node best_bound_value[3];
        for( unsigned j=0; j<d_mbp_bounds[rr].size(); j++ ){
          Node value[3];
          if( Trace.isOn("cbqi-bound") ){
            Assert( !d_mbp_bounds[rr][j].isNull() );
            Trace("cbqi-bound") << "  " << j << ": " << d_mbp_bounds[rr][j];
            if( !d_mbp_vts_coeff[rr][0][j].isNull() ){
              Trace("cbqi-bound") << " (+ " << d_mbp_vts_coeff[rr][0][j] << " * INF)";
            }
            if( !d_mbp_vts_coeff[rr][1][j].isNull() ){
              Trace("cbqi-bound") << " (+ " << d_mbp_vts_coeff[rr][1][j] << " * DELTA)";
            }
            if( !d_mbp_coeff[rr][j].isNull() ){
              Trace("cbqi-bound") << " (div " << d_mbp_coeff[rr][j] << ")";
            }
            Trace("cbqi-bound") << ", value = ";
          }
          t_values[rr].push_back( Node::null() );
          //check if it is better than the current best bound : lexicographic order infinite/finite/infinitesimal parts
          bool new_best = true;
          for( unsigned t=0; t<3; t++ ){
            //get the value
            if( t==0 ){
              value[0] = d_mbp_vts_coeff[rr][0][j];
              if( !value[0].isNull() ){
                Trace("cbqi-bound") << "( " << value[0] << " * INF ) + ";
              }else{
                value[0] = zero;
              }
            }else if( t==1 ){
              Node t_value = ci->getModelValue( d_mbp_bounds[rr][j] );
              t_values[rr][j] = t_value;
              value[1] = t_value;
              Trace("cbqi-bound") << value[1];
            }else{
              value[2] = d_mbp_vts_coeff[rr][1][j];
              if( !value[2].isNull() ){
                Trace("cbqi-bound") << " + ( " << value[2] << " * DELTA )";
              }else{
                value[2] = zero;
              }
            }
            //multiply by coefficient
            if( value[t]!=zero && !d_mbp_coeff[rr][j].isNull() ){
              Assert( d_mbp_coeff[rr][j].isConst() );
              value[t] = NodeManager::currentNM()->mkNode( MULT, NodeManager::currentNM()->mkConst( Rational(1) / d_mbp_coeff[rr][j].getConst<Rational>() ), value[t] );
              value[t] = Rewriter::rewrite( value[t] );
            }
            //check if new best
            if( best!=-1 ){
              Assert( !value[t].isNull() && !best_bound_value[t].isNull() );
              if( value[t]!=best_bound_value[t] ){
                Kind k = rr==0 ? GEQ : LEQ;
                Node cmp_bound = NodeManager::currentNM()->mkNode( k, value[t], best_bound_value[t] );
                cmp_bound = Rewriter::rewrite( cmp_bound );
                if( cmp_bound!=ci->getQuantifiersEngine()->getTermDatabase()->d_true ){
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
          if( best_bound_value[0]!=zero ){
            Trace("cbqi-bound") << "( " << best_bound_value[0] << " * INF ) + ";
          }
          Trace("cbqi-bound") << best_bound_value[1];
          if( best_bound_value[2]!=zero ){
            Trace("cbqi-bound") << " + ( " << best_bound_value[2] << " * DELTA )";
          }
          Trace("cbqi-bound") << std::endl;
          best_used[rr] = best;
          //if using cbqiMidpoint, only add the instance based on one bound if the bound is non-strict
          if( !options::cbqiMidpoint() || d_type.isInteger() || d_mbp_vts_coeff[rr][1][best].isNull() ){
            Node val = d_mbp_bounds[rr][best];
            val = getModelBasedProjectionValue( ci, pv, val, rr==0, d_mbp_coeff[rr][best], pv_value, t_values[rr][best], sf.d_theta,
                                                d_mbp_vts_coeff[rr][0][best], d_mbp_vts_coeff[rr][1][best] );
            if( !val.isNull() ){
              if( ci->doAddInstantiationInc( pv, val, d_mbp_coeff[rr][best], rr==0 ? 1 : -1, sf, effort ) ){
                return true;
              }
            }
          }
        }
      }
    }
    //if not using infinity, use model value of zero
    if( !use_inf && d_mbp_bounds[0].empty() && d_mbp_bounds[1].empty() ){
      Node val = zero;
      Node c; //null (one) coefficient
      val = getModelBasedProjectionValue( ci, pv, val, true, c, pv_value, zero, sf.d_theta, Node::null(), Node::null() );
      if( !val.isNull() ){
        if( ci->doAddInstantiationInc( pv, val, c, 0, sf, effort ) ){
          return true;
        }
      }
    }
    if( options::cbqiMidpoint() && !d_type.isInteger() ){
      Node vals[2];
      bool bothBounds = true;
      Trace("cbqi-bound") << "Try midpoint of bounds..." << std::endl;
      for( unsigned rr=0; rr<2; rr++ ){
        int best = best_used[rr];
        if( best==-1 ){
          bothBounds = false;
        }else{
          vals[rr] = d_mbp_bounds[rr][best];
          vals[rr] = getModelBasedProjectionValue( ci, pv, vals[rr], rr==0, Node::null(), pv_value, t_values[rr][best], sf.d_theta,
                                                   d_mbp_vts_coeff[rr][0][best], Node::null() );
        }
        Trace("cbqi-bound") << "Bound : " << vals[rr] << std::endl;
      }
      Node val;
      if( bothBounds ){
        Assert( !vals[0].isNull() && !vals[1].isNull() );
        if( vals[0]==vals[1] ){
          val = vals[0];
        }else{
          val = NodeManager::currentNM()->mkNode( MULT, NodeManager::currentNM()->mkNode( PLUS, vals[0], vals[1] ),
                                                        NodeManager::currentNM()->mkConst( Rational(1)/Rational(2) ) );
          val = Rewriter::rewrite( val );
        }
      }else{
        if( !vals[0].isNull() ){
          val = NodeManager::currentNM()->mkNode( PLUS, vals[0], one );
          val = Rewriter::rewrite( val );
        }else if( !vals[1].isNull() ){
          val = NodeManager::currentNM()->mkNode( MINUS, vals[1], one );
          val = Rewriter::rewrite( val );
        }
      }
      Trace("cbqi-bound") << "Midpoint value : " << val << std::endl;
      if( !val.isNull() ){
        if( ci->doAddInstantiationInc( pv, val, Node::null(), 0, sf, effort ) ){
          return true;
        }
      }
    }
    //generally should not make it to this point FIXME: write proper assertion
    //Assert( ( ci->hasNestedQuantification() && !options::cbqiNestedQE() ) || options::cbqiAll() );
    
    if( options::cbqiNopt() ){
      //try non-optimal bounds (heuristic, may help when nested quantification) ?
      Trace("cbqi-bound") << "Try non-optimal bounds..." << std::endl;
      for( unsigned r=0; r<2; r++ ){
        int rr = upper_first ? (1-r) : r;
        for( unsigned j=0; j<d_mbp_bounds[rr].size(); j++ ){
          if( (int)j!=best_used[rr] && ( !options::cbqiMidpoint() || d_mbp_vts_coeff[rr][1][j].isNull() ) ){
            Node val = getModelBasedProjectionValue( ci, pv, d_mbp_bounds[rr][j], rr==0, d_mbp_coeff[rr][j], pv_value, t_values[rr][j], sf.d_theta,
                                                     d_mbp_vts_coeff[rr][0][j], d_mbp_vts_coeff[rr][1][j] );
            if( !val.isNull() ){
              if( ci->doAddInstantiationInc( pv, val, d_mbp_coeff[rr][j], rr==0 ? 1 : -1, sf, effort ) ){
                return true;
              }
            }
          }
        }
      }
    }
  }
  return false;
}

bool ArithInstantiator::needsPostProcessInstantiation( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) {
  return std::find( sf.d_has_coeff.begin(), sf.d_has_coeff.end(), pv )!=sf.d_has_coeff.end();
}

bool ArithInstantiator::postProcessInstantiation( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) {
  Assert( std::find( sf.d_has_coeff.begin(), sf.d_has_coeff.end(), pv )!=sf.d_has_coeff.end() );
  Assert( std::find( sf.d_vars.begin(), sf.d_vars.end(), pv )!=sf.d_vars.end() );
  unsigned index = std::find( sf.d_vars.begin(), sf.d_vars.end(), pv )-sf.d_vars.begin();
  Assert( !sf.d_coeff[index].isNull() );
  Trace("cbqi-inst-debug") << "Normalize substitution for " << sf.d_coeff[index] << " * " << sf.d_vars[index] << " = " << sf.d_subs[index] << std::endl;
  Assert( sf.d_vars[index].getType().isInteger() );
  //must ensure that divisibility constraints are met
  //solve updated rewritten equality for vars[index], if coefficient is one, then we are successful
  Node eq_lhs = NodeManager::currentNM()->mkNode( MULT, sf.d_coeff[index], sf.d_vars[index] );
  Node eq_rhs = sf.d_subs[index];
  Node eq = eq_lhs.eqNode( eq_rhs );
  eq = Rewriter::rewrite( eq );
  Trace("cbqi-inst-debug") << "...equality is " << eq << std::endl;
  std::map< Node, Node > msum;
  if( QuantArith::getMonomialSumLit( eq, msum ) ){
    Node veq;
    if( QuantArith::isolate( sf.d_vars[index], msum, veq, EQUAL, true )!=0 ){
      Node veq_c;
      if( veq[0]!=sf.d_vars[index] ){
        Node veq_v;
        if( QuantArith::getMonomial( veq[0], veq_c, veq_v ) ){
          Assert( veq_v==sf.d_vars[index] );
        }
      }
      sf.d_subs[index] = veq[1];
      if( !veq_c.isNull() ){
        sf.d_subs[index] = NodeManager::currentNM()->mkNode( INTS_DIVISION_TOTAL, veq[1], veq_c );
        Trace("cbqi-inst-debug") << "...bound type is : " << sf.d_btyp[index] << std::endl;
        //intger division rounding up if from a lower bound
        if( sf.d_btyp[index]==1 && options::cbqiRoundUpLowerLia() ){
          sf.d_subs[index] = NodeManager::currentNM()->mkNode( PLUS, sf.d_subs[index],
            NodeManager::currentNM()->mkNode( ITE,
              NodeManager::currentNM()->mkNode( EQUAL,
                NodeManager::currentNM()->mkNode( INTS_MODULUS_TOTAL, veq[1], veq_c ),
                ci->getQuantifiersEngine()->getTermDatabase()->d_zero ),
              ci->getQuantifiersEngine()->getTermDatabase()->d_zero, ci->getQuantifiersEngine()->getTermDatabase()->d_one )
          );
        }
      }
      Trace("cbqi-inst-debug") << "...normalize integers : " << sf.d_vars[index] << " -> " << sf.d_subs[index] << std::endl;
    }else{
      Trace("cbqi-inst-debug") << "...failed to isolate." << std::endl;
      return false;
    }
  }else{
    Trace("cbqi-inst-debug") << "...failed to get monomial sum." << std::endl;
    return false;
  }
  return true;
}

void DtInstantiator::reset( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) {

}

Node DtInstantiator::solve_dt( Node v, Node a, Node b, Node sa, Node sb ) {
  Trace("cbqi-inst-debug2") << "Solve dt : " << v << " " << a << " " << b << " " << sa << " " << sb << std::endl;
  Node ret;
  if( !a.isNull() && a==v ){
    ret = sb;
  }else if( !b.isNull() && b==v ){
    ret = sa;
  }else if( !a.isNull() && a.getKind()==APPLY_CONSTRUCTOR ){
    if( !b.isNull() && b.getKind()==APPLY_CONSTRUCTOR ){
      if( a.getOperator()==b.getOperator() ){
        for( unsigned i=0; i<a.getNumChildren(); i++ ){
          Node s = solve_dt( v, a[i], b[i], sa[i], sb[i] );
          if( !s.isNull() ){
            return s;
          }
        }
      }
    }else{
      unsigned cindex = Datatype::indexOf( a.getOperator().toExpr() );
      TypeNode tn = a.getType();
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      for( unsigned i=0; i<a.getNumChildren(); i++ ){
        Node nn = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[cindex][i].getSelector() ), sb );
        Node s = solve_dt( v, a[i], Node::null(), sa[i], nn );
        if( !s.isNull() ){
          return s;
        }
      }
    }
  }else if( !b.isNull() && b.getKind()==APPLY_CONSTRUCTOR ){
    return solve_dt( v, b, a, sb, sa );
  }
  if( !ret.isNull() ){
    //ensure does not contain
    if( TermDb::containsTerm( ret, v ) ){
      ret = Node::null();
    }
  }
  return ret;
}

bool DtInstantiator::processEqualTerms( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& eqc, unsigned effort ) {
  Trace("cbqi-inst-debug") << "[2] try based on constructors in equivalence class." << std::endl;
  //[2] look in equivalence class for a constructor
  for( unsigned k=0; k<eqc.size(); k++ ){
    Node n = eqc[k];
    if( n.getKind()==APPLY_CONSTRUCTOR ){
      Trace("cbqi-inst-debug") << "...try based on constructor term " << n << std::endl;
      std::vector< Node > children;
      children.push_back( n.getOperator() );
      const Datatype& dt = ((DatatypeType)(d_type).toType()).getDatatype();
      unsigned cindex = Datatype::indexOf( n.getOperator().toExpr() );
      //now must solve for selectors applied to pv
      for( unsigned j=0; j<dt[cindex].getNumArgs(); j++ ){
        Node c = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[cindex][j].getSelector() ), pv );
        ci->pushStackVariable( c );
        children.push_back( c );
      }
      Node val = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, children );
      if( ci->doAddInstantiationInc( pv, val, Node::null(), 0, sf, effort ) ){
        return true;
      }else{
        //cleanup
        for( unsigned j=0; j<dt[cindex].getNumArgs(); j++ ){
          ci->popStackVariable();
        }
        break;
      }
    }
  }
  return false;
}

bool DtInstantiator::processEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& term_coeffs, std::vector< Node >& terms, unsigned effort ) {
  Node val = solve_dt( pv, terms[0], terms[1], terms[0], terms[1] );
  if( !val.isNull() ){
    Node veq_c;
    if( ci->doAddInstantiationInc( pv, val, veq_c, 0, sf, effort ) ){
      return true;
    }
  }
  return false;
}

void EprInstantiator::reset( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) {
  d_equal_terms.clear();
}

bool EprInstantiator::processEqualTerm( CegInstantiator * ci, SolvedForm& sf, Node pv, Node pv_coeff, Node n, unsigned effort ) {
  if( options::quantEprMatching() ){
    Assert( pv_coeff.isNull() );
    d_equal_terms.push_back( n ); 
    return false;  
  }else{
    return ci->doAddInstantiationInc( pv, n, pv_coeff, 0, sf, effort );
  }
}

void EprInstantiator::computeMatchScore( CegInstantiator * ci, Node pv, Node catom, std::vector< Node >& arg_reps, TermArgTrie * tat, unsigned index, std::map< Node, int >& match_score ) {
  if( index==catom.getNumChildren() ){
    Assert( tat->hasNodeData() );
    Node gcatom = tat->getNodeData();
    Trace("epr-inst") << "Matched : " << catom << " and " << gcatom << std::endl;
    for( unsigned i=0; i<catom.getNumChildren(); i++ ){
      if( catom[i]==pv ){
        Trace("epr-inst") << "...increment " << gcatom[i] << std::endl;
        match_score[gcatom[i]]++;
      }else{
        //recursive matching
        computeMatchScore( ci, pv, catom[i], gcatom[i], match_score );
      }
    }
  }else{
    std::map< TNode, TermArgTrie >::iterator it = tat->d_data.find( arg_reps[index] );
    if( it!=tat->d_data.end() ){
      computeMatchScore( ci, pv, catom, arg_reps, &it->second, index+1, match_score );
    }
  }
}

void EprInstantiator::computeMatchScore( CegInstantiator * ci, Node pv, Node catom, Node eqc, std::map< Node, int >& match_score ) {
  if( inst::Trigger::isAtomicTrigger( catom ) && TermDb::containsTerm( catom, pv ) ){
    Trace("epr-inst") << "Find matches for " << catom << "..." << std::endl;
    std::vector< Node > arg_reps;
    for( unsigned j=0; j<catom.getNumChildren(); j++ ){
      arg_reps.push_back( ci->getQuantifiersEngine()->getMasterEqualityEngine()->getRepresentative( catom[j] ) );
    }
    if( ci->getQuantifiersEngine()->getMasterEqualityEngine()->hasTerm( eqc ) ){
      Node rep = ci->getQuantifiersEngine()->getMasterEqualityEngine()->getRepresentative( eqc );
      Node op = ci->getQuantifiersEngine()->getTermDatabase()->getMatchOperator( catom );
      TermArgTrie * tat = ci->getQuantifiersEngine()->getTermDatabase()->getTermArgTrie( rep, op );
      Trace("epr-inst") << "EPR instantiation match term : " << catom << ", check ground terms=" << (tat!=NULL) << std::endl;
      if( tat ){
        computeMatchScore( ci, pv, catom, arg_reps, tat, 0, match_score );
      }
    }
  }
}

struct sortEqTermsMatch {
  std::map< Node, int > d_match_score;
  bool operator() (Node i, Node j) {
    int match_score_i = d_match_score[i];
    int match_score_j = d_match_score[j];
    return match_score_i>match_score_j || ( match_score_i==match_score_j && i<j );
  }
};

    
bool EprInstantiator::processEqualTerms( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& eqc, unsigned effort ) {
  if( options::quantEprMatching() ){
    //heuristic for best matching constant
    sortEqTermsMatch setm;
    for( unsigned i=0; i<ci->getNumCEAtoms(); i++ ){
      Node catom = ci->getCEAtom( i );
      computeMatchScore( ci, pv, catom, catom, setm.d_match_score );
    }
    //sort by match score
    std::sort( d_equal_terms.begin(), d_equal_terms.end(), setm );
    Node pv_coeff;
    for( unsigned i=0; i<d_equal_terms.size(); i++ ){
      if( ci->doAddInstantiationInc( pv, d_equal_terms[i], pv_coeff, 0, sf, effort ) ){
        return true;
      }
    }
  }
  return false;
}

bool BvInstantiator::processAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort ) {
  /*   TODO: algebraic reasoning for bitvector instantiation
  if( atom.getKind()==BITVECTOR_ULT || atom.getKind()==BITVECTOR_ULE ){
    for( unsigned t=0; t<2; t++ ){
      if( atom[t]==pv ){
        computeProgVars( atom[1-t] );
        if( d_inelig.find( atom[1-t] )==d_inelig.end() ){
          //only ground terms  TODO: more
          if( d_prog_var[atom[1-t]].empty() ){
            Node veq_c;
            Node uval;
            if( ( !pol && atom.getKind()==BITVECTOR_ULT ) || ( pol && atom.getKind()==BITVECTOR_ULE ) ){
              uval = atom[1-t];
            }else{
              uval = NodeManager::currentNM()->mkNode( (atom.getKind()==BITVECTOR_ULT)==(t==1) ? BITVECTOR_PLUS : BITVECTOR_SUB, atom[1-t], 
                                                       bv::utils::mkConst(pvtn.getConst<BitVectorSize>(), 1) );
            }
            if( doAddInstantiationInc( pv, uval, veq_c, 0, sf, effort ) ){
              return true;
            }
          }
        }
      }
    }
  }
  */

  return false;
}


