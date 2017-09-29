/*********************                                                        */
/*! \file ceg_t_instantiator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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

#include <algorithm>

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

Node ArithInstantiator::getModelBasedProjectionValue( CegInstantiator * ci, Node e, Node t, bool isLower, Node c, Node me, Node mt, Node theta, Node inf_coeff, Node delta_coeff ) {
  Node val = t;
  Trace("cegqi-arith-bound2") << "Value : " << val << std::endl;
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
    Trace("cegqi-arith-bound2") << "...c*e = " << ceValue << std::endl;
    Trace("cegqi-arith-bound2") << "...theta = " << new_theta << std::endl;
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
    Trace("cegqi-arith-bound2") << "...rho = " << me << " - " << mt << " = " << rho << std::endl;
    Trace("cegqi-arith-bound2") << "..." << rho << " mod " << new_theta << " = ";
    rho = NodeManager::currentNM()->mkNode( INTS_MODULUS_TOTAL, rho, new_theta );
    rho = Rewriter::rewrite( rho );
    Trace("cegqi-arith-bound2") << rho << std::endl;
    Kind rk = isLower ? PLUS : MINUS;
    val = NodeManager::currentNM()->mkNode( rk, val, rho );
    val = Rewriter::rewrite( val );
    Trace("cegqi-arith-bound2") << "(after rho) : " << val << std::endl;
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
  Trace("cegqi-arith-debug") << "isolate for " << pv << " in " << atom << std::endl;
  std::map< Node, Node > msum;
  if( QuantArith::getMonomialSumLit( atom, msum ) ){
    Trace("cegqi-arith-debug") << "got monomial sum: " << std::endl;
    if( Trace.isOn("cegqi-arith-debug") ){
      QuantArith::debugPrintMonomialSum( msum, "cegqi-arith-debug" );
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
          Trace("cegqi-arith-debug") << "vts[" << t << "] coefficient is " << vts_coeff[t] << std::endl;
          msum.erase( d_vts_sym[t] );
        }
      }
    }

    ires = QuantArith::isolate( pv, msum, veq_c, val, atom.getKind() );
    if( ires!=0 ){
      Node realPart;
      if( Trace.isOn("cegqi-arith-debug") ){
        Trace("cegqi-arith-debug") << "Isolate : ";
        if( !veq_c.isNull() ){
          Trace("cegqi-arith-debug") << veq_c << " * ";
        }
        Trace("cegqi-arith-debug") << pv << " " << atom.getKind() << " " << val << std::endl;
      }
      if( options::cbqiAll() ){
        // when not pure LIA/LRA, we must check whether the lhs contains pv
        if( TermDb::containsTerm( val, pv ) ){
          Trace("cegqi-arith-debug") << "fail : contains bad term" << std::endl;
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
        Trace("cegqi-arith-debug") << "Re-isolate..." << std::endl;
        ires = QuantArith::isolate( pv, msum, veq_c, val, atom.getKind() );
        Trace("cegqi-arith-debug") << "Isolate for mixed Int/Real : " << veq_c << " * " << pv << " " << atom.getKind() << " " << val << std::endl;
        Trace("cegqi-arith-debug") << "                 real part : " << realPart << std::endl;
        if( ires!=0 ){
          int ires_use = ( msum[pv].isNull() || msum[pv].getConst<Rational>().sgn()==1 ) ? 1 : -1;
          val = Rewriter::rewrite( NodeManager::currentNM()->mkNode( ires_use==-1 ? PLUS : MINUS,
                                    NodeManager::currentNM()->mkNode( ires_use==-1 ? MINUS : PLUS, val, realPart ),
                                    NodeManager::currentNM()->mkNode( TO_INTEGER, realPart ) ) );  //TODO: round up for upper bounds?
          Trace("cegqi-arith-debug") << "result : " << val << std::endl;
          Assert( val.getType().isInteger() );
        }
      }
    }
    vts_coeff_inf = vts_coeff[0];
    vts_coeff_delta = vts_coeff[1];
    Trace("cegqi-arith-debug") << "Return " << veq_c << " * " << pv << " " << atom.getKind() << " " << val << ", vts = (" << vts_coeff_inf << ", " << vts_coeff_delta << ")" << std::endl;
  }else{
    Trace("cegqi-arith-debug") << "fail : could not get monomial sum" << std::endl;
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

bool ArithInstantiator::processEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< TermProperties >& term_props, std::vector< Node >& terms, unsigned effort ) {
  Node eq_lhs = terms[0];
  Node eq_rhs = terms[1];
  Node lhs_coeff = term_props[0].d_coeff;
  Node rhs_coeff = term_props[1].d_coeff;
  //make the same coefficient
  if( rhs_coeff!=lhs_coeff ){
    if( !rhs_coeff.isNull() ){
      Trace("cegqi-arith-debug") << "...mult lhs by " << rhs_coeff << std::endl;
      eq_lhs = NodeManager::currentNM()->mkNode( MULT, rhs_coeff, eq_lhs );
      eq_lhs = Rewriter::rewrite( eq_lhs );
    }
    if( !lhs_coeff.isNull() ){
      Trace("cegqi-arith-debug") << "...mult rhs by " << lhs_coeff << std::endl;
      eq_rhs = NodeManager::currentNM()->mkNode( MULT, lhs_coeff, eq_rhs );
      eq_rhs = Rewriter::rewrite( eq_rhs );
    }
  }
  Node eq = eq_lhs.eqNode( eq_rhs );
  eq = Rewriter::rewrite( eq );
  Node val;
  TermProperties pv_prop;
  Node vts_coeff_inf;
  Node vts_coeff_delta;
  //isolate pv in the equality
  int ires = solve_arith( ci, pv, eq, pv_prop.d_coeff, val, vts_coeff_inf, vts_coeff_delta );
  if( ires!=0 ){
    pv_prop.d_type = 0;
    if( ci->doAddInstantiationInc( pv, val, pv_prop, sf, effort ) ){
      return true;
    }
  }

  return false;
}

bool ArithInstantiator::hasProcessAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort ) {
  Node atom = lit.getKind()==NOT ? lit[0] : lit;
  bool pol = lit.getKind()!=NOT;
  //arithmetic inequalities and disequalities
  return atom.getKind()==GEQ || ( atom.getKind()==EQUAL && !pol && atom[0].getType().isReal() );
}

bool ArithInstantiator::processAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort ) {
  Node atom = lit.getKind()==NOT ? lit[0] : lit;
  bool pol = lit.getKind()!=NOT;
  //arithmetic inequalities and disequalities
  Assert( atom.getKind()==GEQ || ( atom.getKind()==EQUAL && !pol && atom[0].getType().isReal() ) );
  // get model value for pv
  Node pv_value = ci->getModelValue( pv );
  //cannot contain infinity?
  Node vts_coeff_inf;
  Node vts_coeff_delta;
  Node val;
  TermProperties pv_prop;
  //isolate pv in the inequality
  int ires = solve_arith( ci, pv, atom, pv_prop.d_coeff, val, vts_coeff_inf, vts_coeff_delta );
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
            Trace("cegqi-arith-debug") << "Disequality : check infinity polarity " << vts_coeff_inf << std::endl;
            Assert( vts_coeff_inf.isConst() );
            is_upper = ( vts_coeff_inf.getConst<Rational>().sgn()==1 );
          }else{
            Node rhs_value = ci->getModelValue( val );
            Node lhs_value = pv_prop.getModifiedTerm( pv_value );
            if( !pv_prop.isBasic() ){
              lhs_value = pv_prop.getModifiedTerm( pv_value );
              lhs_value = Rewriter::rewrite( lhs_value );
            }
            Trace("cegqi-arith-debug") << "Disequality : check model values " << lhs_value << " " << rhs_value << std::endl;
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
      if( Trace.isOn("cegqi-arith-bound-inf") ){
        Node pvmod = pv_prop.getModifiedTerm( pv );
        Trace("cegqi-arith-bound-inf") << "From " << lit << ", got : ";
        Trace("cegqi-arith-bound-inf") << pvmod << " -> " << uval << ", styp = " << uires << std::endl;
      }
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
        d_mbp_coeff[index].push_back( pv_prop.d_coeff );
        Trace("cegqi-arith-debug") << "Store bound " << index << " " << uval << " " << pv_prop.d_coeff << " " << vts_coeff_inf << " " << vts_coeff_delta << " " << lit << std::endl;
        for( unsigned t=0; t<2; t++ ){
          d_mbp_vts_coeff[index][t].push_back( t==0 ? vts_coeff_inf : vts_coeff_delta );
        }
        d_mbp_lit[index].push_back( lit );
      }else{
        //try this bound
        pv_prop.d_type = uires>0 ? 1 : -1;
        if( ci->doAddInstantiationInc( pv, uval, pv_prop, sf, effort ) ){
          return true;
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
          Trace("cegqi-arith-bound") << "No " << ( rr==0 ? "lower" : "upper" ) << " bounds for " << pv << " (type=" << d_type << ")" << std::endl;
          //no bounds, we do +- infinity
          Node val = ci->getQuantifiersEngine()->getTermDatabase()->getVtsInfinity( d_type );
          //TODO : rho value for infinity?
          if( rr==0 ){
            val = NodeManager::currentNM()->mkNode( UMINUS, val );
            val = Rewriter::rewrite( val );
          }
          TermProperties pv_prop_no_bound;
          if( ci->doAddInstantiationInc( pv, val, pv_prop_no_bound, sf, effort ) ){
            return true;
          }
        }
      }else{
        Trace("cegqi-arith-bound") << ( rr==0 ? "Lower" : "Upper" ) << " bounds for " << pv << " (type=" << d_type << ") : " << std::endl;
        int best = -1;
        Node best_bound_value[3];
        for( unsigned j=0; j<d_mbp_bounds[rr].size(); j++ ){
          Node value[3];
          if( Trace.isOn("cegqi-arith-bound") ){
            Assert( !d_mbp_bounds[rr][j].isNull() );
            Trace("cegqi-arith-bound") << "  " << j << ": " << d_mbp_bounds[rr][j];
            if( !d_mbp_vts_coeff[rr][0][j].isNull() ){
              Trace("cegqi-arith-bound") << " (+ " << d_mbp_vts_coeff[rr][0][j] << " * INF)";
            }
            if( !d_mbp_vts_coeff[rr][1][j].isNull() ){
              Trace("cegqi-arith-bound") << " (+ " << d_mbp_vts_coeff[rr][1][j] << " * DELTA)";
            }
            if( !d_mbp_coeff[rr][j].isNull() ){
              Trace("cegqi-arith-bound") << " (div " << d_mbp_coeff[rr][j] << ")";
            }
            Trace("cegqi-arith-bound") << ", value = ";
          }
          t_values[rr].push_back( Node::null() );
          //check if it is better than the current best bound : lexicographic order infinite/finite/infinitesimal parts
          bool new_best = true;
          for( unsigned t=0; t<3; t++ ){
            //get the value
            if( t==0 ){
              value[0] = d_mbp_vts_coeff[rr][0][j];
              if( !value[0].isNull() ){
                Trace("cegqi-arith-bound") << "( " << value[0] << " * INF ) + ";
              }else{
                value[0] = zero;
              }
            }else if( t==1 ){
              Node t_value = ci->getModelValue( d_mbp_bounds[rr][j] );
              t_values[rr][j] = t_value;
              value[1] = t_value;
              Trace("cegqi-arith-bound") << value[1];
            }else{
              value[2] = d_mbp_vts_coeff[rr][1][j];
              if( !value[2].isNull() ){
                Trace("cegqi-arith-bound") << " + ( " << value[2] << " * DELTA )";
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
          Trace("cegqi-arith-bound") << std::endl;
          if( new_best ){
            for( unsigned t=0; t<3; t++ ){
              best_bound_value[t] = value[t];
            }
            best = j;
          }
        }
        if( best!=-1 ){
          Trace("cegqi-arith-bound") << "...best bound is " << best << " : ";
          if( best_bound_value[0]!=zero ){
            Trace("cegqi-arith-bound") << "( " << best_bound_value[0] << " * INF ) + ";
          }
          Trace("cegqi-arith-bound") << best_bound_value[1];
          if( best_bound_value[2]!=zero ){
            Trace("cegqi-arith-bound") << " + ( " << best_bound_value[2] << " * DELTA )";
          }
          Trace("cegqi-arith-bound") << std::endl;
          best_used[rr] = best;
          //if using cbqiMidpoint, only add the instance based on one bound if the bound is non-strict
          if( !options::cbqiMidpoint() || d_type.isInteger() || d_mbp_vts_coeff[rr][1][best].isNull() ){
            Node val = d_mbp_bounds[rr][best];
            val = getModelBasedProjectionValue( ci, pv, val, rr==0, d_mbp_coeff[rr][best], pv_value, t_values[rr][best], sf.getTheta(),
                                                d_mbp_vts_coeff[rr][0][best], d_mbp_vts_coeff[rr][1][best] );
            if( !val.isNull() ){
              TermProperties pv_prop_bound;
              pv_prop_bound.d_coeff = d_mbp_coeff[rr][best];
              pv_prop_bound.d_type = rr==0 ? 1 : -1;
              if( ci->doAddInstantiationInc( pv, val, pv_prop_bound, sf, effort ) ){
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
      TermProperties pv_prop_zero;
      Node theta = sf.getTheta();
      val = getModelBasedProjectionValue( ci, pv, val, true, pv_prop_zero.d_coeff, pv_value, zero, sf.getTheta(), Node::null(), Node::null() );
      if( !val.isNull() ){
        if( ci->doAddInstantiationInc( pv, val, pv_prop_zero, sf, effort ) ){
          return true;
        }
      }
    }
    if( options::cbqiMidpoint() && !d_type.isInteger() ){
      Node vals[2];
      bool bothBounds = true;
      Trace("cegqi-arith-bound") << "Try midpoint of bounds..." << std::endl;
      for( unsigned rr=0; rr<2; rr++ ){
        int best = best_used[rr];
        if( best==-1 ){
          bothBounds = false;
        }else{
          vals[rr] = d_mbp_bounds[rr][best];
          vals[rr] = getModelBasedProjectionValue( ci, pv, vals[rr], rr==0, Node::null(), pv_value, t_values[rr][best], sf.getTheta(),
                                                   d_mbp_vts_coeff[rr][0][best], Node::null() );
        }
        Trace("cegqi-arith-bound") << "Bound : " << vals[rr] << std::endl;
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
      Trace("cegqi-arith-bound") << "Midpoint value : " << val << std::endl;
      if( !val.isNull() ){
        TermProperties pv_prop_midpoint;
        if( ci->doAddInstantiationInc( pv, val, pv_prop_midpoint, sf, effort ) ){
          return true;
        }
      }
    }
    //generally should not make it to this point FIXME: write proper assertion
    //Assert( ( ci->hasNestedQuantification() && !options::cbqiNestedQE() ) || options::cbqiAll() );

    if( options::cbqiNopt() ){
      //try non-optimal bounds (heuristic, may help when nested quantification) ?
      Trace("cegqi-arith-bound") << "Try non-optimal bounds..." << std::endl;
      for( unsigned r=0; r<2; r++ ){
        int rr = upper_first ? (1-r) : r;
        for( unsigned j=0; j<d_mbp_bounds[rr].size(); j++ ){
          if( (int)j!=best_used[rr] && ( !options::cbqiMidpoint() || d_mbp_vts_coeff[rr][1][j].isNull() ) ){
            Node val = getModelBasedProjectionValue( ci, pv, d_mbp_bounds[rr][j], rr==0, d_mbp_coeff[rr][j], pv_value, t_values[rr][j], sf.getTheta(),
                                                     d_mbp_vts_coeff[rr][0][j], d_mbp_vts_coeff[rr][1][j] );
            if( !val.isNull() ){
              TermProperties pv_prop_nopt_bound;
              pv_prop_nopt_bound.d_coeff = d_mbp_coeff[rr][j];
              pv_prop_nopt_bound.d_type = rr==0 ? 1 : -1;
              if( ci->doAddInstantiationInc( pv, val, pv_prop_nopt_bound, sf, effort ) ){
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

bool ArithInstantiator::needsPostProcessInstantiationForVariable( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) {
  return std::find( sf.d_non_basic.begin(), sf.d_non_basic.end(), pv )!=sf.d_non_basic.end();
}

bool ArithInstantiator::postProcessInstantiationForVariable( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort, 
                                                             std::vector< Node >& lemmas ) {
  Assert( std::find( sf.d_non_basic.begin(), sf.d_non_basic.end(), pv )!=sf.d_non_basic.end() );
  Assert( std::find( sf.d_vars.begin(), sf.d_vars.end(), pv )!=sf.d_vars.end() );
  unsigned index = std::find( sf.d_vars.begin(), sf.d_vars.end(), pv )-sf.d_vars.begin();
  Assert( !sf.d_props[index].isBasic() );
  Node eq_lhs = sf.d_props[index].getModifiedTerm( sf.d_vars[index] );
  if( Trace.isOn("cegqi-arith-debug") ){
    Trace("cegqi-arith-debug") << "Normalize substitution for ";
    Trace("cegqi-arith-debug") << eq_lhs << " = " << sf.d_subs[index] << std::endl;
  }
  Assert( sf.d_vars[index].getType().isInteger() );
  //must ensure that divisibility constraints are met
  //solve updated rewritten equality for vars[index], if coefficient is one, then we are successful
  Node eq_rhs = sf.d_subs[index];
  Node eq = eq_lhs.eqNode( eq_rhs );
  eq = Rewriter::rewrite( eq );
  Trace("cegqi-arith-debug") << "...equality is " << eq << std::endl;
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
        Trace("cegqi-arith-debug") << "...bound type is : " << sf.d_props[index].d_type << std::endl;
        //intger division rounding up if from a lower bound
        if( sf.d_props[index].d_type==1 && options::cbqiRoundUpLowerLia() ){
          sf.d_subs[index] = NodeManager::currentNM()->mkNode( PLUS, sf.d_subs[index],
            NodeManager::currentNM()->mkNode( ITE,
              NodeManager::currentNM()->mkNode( EQUAL,
                NodeManager::currentNM()->mkNode( INTS_MODULUS_TOTAL, veq[1], veq_c ),
                ci->getQuantifiersEngine()->getTermDatabase()->d_zero ),
              ci->getQuantifiersEngine()->getTermDatabase()->d_zero, ci->getQuantifiersEngine()->getTermDatabase()->d_one )
          );
        }
      }
      Trace("cegqi-arith-debug") << "...normalize integers : " << sf.d_vars[index] << " -> " << sf.d_subs[index] << std::endl;
    }else{
      Trace("cegqi-arith-debug") << "...failed to isolate." << std::endl;
      return false;
    }
  }else{
    Trace("cegqi-arith-debug") << "...failed to get monomial sum." << std::endl;
    return false;
  }
  return true;
}

void DtInstantiator::reset( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) {

}

Node DtInstantiator::solve_dt( Node v, Node a, Node b, Node sa, Node sb ) {
  Trace("cegqi-arith-debug2") << "Solve dt : " << v << " " << a << " " << b << " " << sa << " " << sb << std::endl;
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
        Node nn = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[cindex].getSelectorInternal( tn.toType(), i ) ), sb );
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
  Trace("cegqi-dt-debug") << "[2] try based on constructors in equivalence class." << std::endl;
  //[2] look in equivalence class for a constructor
  for( unsigned k=0; k<eqc.size(); k++ ){
    Node n = eqc[k];
    if( n.getKind()==APPLY_CONSTRUCTOR ){
      Trace("cegqi-dt-debug") << "...try based on constructor term " << n << std::endl;
      std::vector< Node > children;
      children.push_back( n.getOperator() );
      const Datatype& dt = ((DatatypeType)(d_type).toType()).getDatatype();
      unsigned cindex = Datatype::indexOf( n.getOperator().toExpr() );
      //now must solve for selectors applied to pv
      for( unsigned j=0; j<dt[cindex].getNumArgs(); j++ ){
        Node c = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[cindex].getSelectorInternal( d_type.toType(), j ) ), pv );
        ci->pushStackVariable( c );
        children.push_back( c );
      }
      Node val = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, children );
      TermProperties pv_prop_dt;
      if( ci->doAddInstantiationInc( pv, val, pv_prop_dt, sf, effort ) ){
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

bool DtInstantiator::processEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< TermProperties >& term_props, std::vector< Node >& terms, unsigned effort ) {
  Node val = solve_dt( pv, terms[0], terms[1], terms[0], terms[1] );
  if( !val.isNull() ){
    TermProperties pv_prop;
    if( ci->doAddInstantiationInc( pv, val, pv_prop, sf, effort ) ){
      return true;
    }
  }
  return false;
}

void EprInstantiator::reset( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) {
  d_equal_terms.clear();
}

bool EprInstantiator::processEqualTerm( CegInstantiator * ci, SolvedForm& sf, Node pv, TermProperties& pv_prop, Node n, unsigned effort ) {
  if( options::quantEprMatching() ){
    Assert( pv_prop.isBasic() );
    d_equal_terms.push_back( n );
    return false;
  }else{
    pv_prop.d_type = 0;
    return ci->doAddInstantiationInc( pv, n, pv_prop, sf, effort );
  }
}

void EprInstantiator::computeMatchScore( CegInstantiator * ci, Node pv, Node catom, std::vector< Node >& arg_reps, TermArgTrie * tat, unsigned index, std::map< Node, int >& match_score ) {
  if( index==catom.getNumChildren() ){
    Assert( tat->hasNodeData() );
    Node gcatom = tat->getNodeData();
    Trace("cegqi-epr") << "Matched : " << catom << " and " << gcatom << std::endl;
    for( unsigned i=0; i<catom.getNumChildren(); i++ ){
      if( catom[i]==pv ){
        Trace("cegqi-epr") << "...increment " << gcatom[i] << std::endl;
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
    Trace("cegqi-epr") << "Find matches for " << catom << "..." << std::endl;
    std::vector< Node > arg_reps;
    for( unsigned j=0; j<catom.getNumChildren(); j++ ){
      arg_reps.push_back( ci->getQuantifiersEngine()->getMasterEqualityEngine()->getRepresentative( catom[j] ) );
    }
    if( ci->getQuantifiersEngine()->getMasterEqualityEngine()->hasTerm( eqc ) ){
      Node rep = ci->getQuantifiersEngine()->getMasterEqualityEngine()->getRepresentative( eqc );
      Node op = ci->getQuantifiersEngine()->getTermDatabase()->getMatchOperator( catom );
      TermArgTrie * tat = ci->getQuantifiersEngine()->getTermDatabase()->getTermArgTrie( rep, op );
      Trace("cegqi-epr") << "EPR instantiation match term : " << catom << ", check ground terms=" << (tat!=NULL) << std::endl;
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
    TermProperties pv_prop;
    pv_prop.d_type = 0;
    for( unsigned i=0; i<d_equal_terms.size(); i++ ){
      if( ci->doAddInstantiationInc( pv, d_equal_terms[i], pv_prop, sf, effort ) ){
        return true;
      }
    }
  }
  return false;
}

Node BvInverter::getSolveVariable( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator its = d_solve_var.find( tn );
  if( its==d_solve_var.end() ){
    std::stringstream ss;
    if( tn.isFunction() ){
      Assert( tn.getNumChildren()==2 );
      Assert( tn[0].isBoolean() );
      ss << "slv_f";
    }else{
      ss << "slv";
    }
    Node k = NodeManager::currentNM()->mkSkolem( ss.str(), tn );
    // marked as a virtual term (it is eligible for instantiation)
    VirtualTermSkolemAttribute vtsa;
    k.setAttribute(vtsa,true);
    d_solve_var[tn] = k;
    return k;
  }else{
    return its->second;
  }
}

Node BvInverter::getInversionSkolemFor( Node cond, TypeNode tn ) {
  // condition should be rewritten
  Assert( Rewriter::rewrite(cond)==cond );
  std::unordered_map< Node, Node, NodeHashFunction >::iterator it = d_inversion_skolem_cache.find( cond );
  if( it==d_inversion_skolem_cache.end() ){
    Node skv;
    if( cond.getKind()==EQUAL ){
      // optimization : if condition is ( x = v ) should just return v and not introduce a Skolem
      // this can happen when we ask for the multiplicative inversion with bv1
      Node x = getSolveVariable( tn );
      for( unsigned i=0; i<2; i++ ){
        if( cond[i]==x ){
          skv = cond[1-i];
          Trace("cegqi-bv-skvinv") << "SKVINV : " << skv << " is trivially associated with conditon " << cond << std::endl;
          break;
        }
      }
    }
    if( skv.isNull() ){
      // TODO : compute the value if the condition is deterministic, e.g. calc multiplicative inverse of 2 constants
      skv = NodeManager::currentNM()->mkSkolem ("skvinv", tn, "created for BvInverter");
      Trace("cegqi-bv-skvinv") << "SKVINV : " << skv << " is the skolem associated with conditon " << cond << std::endl;
      // marked as a virtual term (it is eligible for instantiation)
      VirtualTermSkolemAttribute vtsa;
      skv.setAttribute(vtsa,true);
    }
    d_inversion_skolem_cache[cond] = skv;
    return skv;
  }else{
    Assert( it->second.getType()==tn );
    return it->second;
  }
}

Node BvInverter::getInversionSkolemFunctionFor( TypeNode tn ) {
  // function maps conditions to skolems
  TypeNode ftn = NodeManager::currentNM()->mkFunctionType( NodeManager::currentNM()->booleanType(), tn );
  return getSolveVariable( ftn );
}

Node BvInverter::getInversionNode( Node cond, TypeNode tn ) {
  // condition should be rewritten
  Node new_cond = Rewriter::rewrite(cond);
  if( new_cond!=cond ){
    Trace("bv-invert-debug") << "Condition " << cond << " was rewritten to " << new_cond << std::endl;
  } 
  Node f = getInversionSkolemFunctionFor( tn );
  return NodeManager::currentNM()->mkNode( kind::APPLY_UF, f, new_cond );
}

bool BvInverter::isInvertible( Kind k ) {
  // TODO : make this precise (this should correspond to all kinds that we handle in solve_bv_lit/solve_bv_constraint)
  return k!=APPLY_UF;
}

Node BvInverter::getPathToPv( Node lit, Node pv, Node sv, std::vector< unsigned >& path, std::unordered_set< TNode, TNodeHashFunction >& visited ) {
  if( visited.find( lit )==visited.end() ){
    visited.insert( lit );
    if( lit==pv ){
      return sv;
    }else{
      // only recurse if the kind is invertible 
      // this allows us to avoid paths that go through skolem functions
      if( isInvertible( lit.getKind() ) ){
        unsigned rmod = 0; // TODO : randomize?
        for( unsigned i=0; i<lit.getNumChildren(); i++ ){
          unsigned ii = ( i + rmod )%lit.getNumChildren();
          Node litc = getPathToPv( lit[ii], pv, sv, path, visited );
          if( !litc.isNull() ){
            // path is outermost term index last
            path.push_back( ii );
            std::vector< Node > children;
            if( lit.getMetaKind() == kind::metakind::PARAMETERIZED ){
              children.push_back( lit.getOperator() );
            }
            for( unsigned j=0; j<lit.getNumChildren(); j++ ){
              children.push_back( j==ii ? litc : lit[j] );
            }
            return NodeManager::currentNM()->mkNode( lit.getKind(), children );
          }
        }
      }
    }
  }
  return Node::null();
}

Node BvInverter::eliminateSkolemFunctions( TNode n, std::vector< Node >& side_conditions, std::unordered_map< TNode, Node, TNodeHashFunction >& visited ) {
  std::unordered_map< TNode, Node, TNodeHashFunction >::iterator it = visited.find( n );
  if( it==visited.end() ){
    Trace("bv-invert-debug") << "eliminateSkolemFunctions from " << n << "..." << std::endl;
    Node ret = n;
    bool childChanged = false;
    std::vector< Node > children;
    if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
      children.push_back( n.getOperator() );
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      Node nc = eliminateSkolemFunctions( n[i], side_conditions, visited );
      childChanged = childChanged || n[i]!=nc;
      children.push_back( nc );
    } 
    if( childChanged ){
      ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
    }
    // now, check if it is a skolem function
    if( ret.getKind()==APPLY_UF ){
      Node op = ret.getOperator();
      TypeNode tnp = op.getType();
      // is this a skolem function?
      std::map< TypeNode, Node >::iterator its = d_solve_var.find( tnp );
      if( its!=d_solve_var.end() && its->second==op ){
        Assert( ret.getNumChildren()==1 );
        Assert( ret[0].getType().isBoolean() );
        
        Node cond = ret[0];
        // must rewrite now to ensure we lookup the correct skolem 
        cond = Rewriter::rewrite( cond );
        
        // if so, we replace by the (finalized) skolem variable
        // Notice that since we are post-rewriting, skolem functions are already eliminated from cond
        ret = getInversionSkolemFor( cond, ret.getType() );
        
        // also must add (substituted) side condition to vector
        // substitute ( solve variable -> inversion skolem )
        TNode solve_var = getSolveVariable( ret.getType() );
        TNode tret = ret;
        cond = cond.substitute( solve_var, tret );
        if( std::find( side_conditions.begin(), side_conditions.end(), cond )==side_conditions.end() ){
          side_conditions.push_back( cond );
        }
      }
    }
    Trace("bv-invert-debug") << "eliminateSkolemFunctions from " << n << " returned " << ret << std::endl;
    visited[n] = ret;
    return ret;
  }else{
    return it->second;
  }
}

Node BvInverter::eliminateSkolemFunctions( TNode n, std::vector< Node >& side_conditions ) {
  std::unordered_map< TNode, Node, TNodeHashFunction > visited;
  return eliminateSkolemFunctions( n, side_conditions, visited );
}
  
Node BvInverter::getPathToPv( Node lit, Node pv, Node sv, Node pvs, std::vector< unsigned >& path ) {
  std::unordered_set< TNode, TNodeHashFunction > visited;
  Node slit = getPathToPv( lit, pv, sv, path, visited );
  // if we are able to find a (invertible) path to pv
  if( !slit.isNull() ){
    // substitute pvs for the other occurrences of pv
    TNode tpv = pv;
    TNode tpvs = pvs;
    slit = slit.substitute( tpv, tpvs );
  }
  return slit;
}

Node BvInverter::solve_bv_constraint( Node sv, Node sv_t, Node t, Kind rk, bool pol, std::vector< unsigned >& path,
                                      BvInverterModelQuery * m, BvInverterStatus& status ) {
  NodeManager *nm = NodeManager::currentNM();
  while( !path.empty() ){
    unsigned index = path.back();
    Assert (sv_t.getNumChildren() <= 2);
    Assert( index<sv_t.getNumChildren() );
    path.pop_back();
    Kind k = sv_t.getKind();
    // inversions
    if( k==BITVECTOR_PLUS ){
      t = nm->mkNode( BITVECTOR_SUB, t, sv_t[1-index] );
    }else if( k==BITVECTOR_SUB ){
      t = nm->mkNode( BITVECTOR_PLUS, t, sv_t[1-index] );
    }else if( k==BITVECTOR_MULT ){
      // t = skv (fresh skolem constant)
      TypeNode solve_tn = sv_t[index].getType();
      Node x = getSolveVariable( solve_tn );
      // with side condition:
      // ctz(t) >= ctz(s) <-> x * s = t
      // where
      // ctz(t) >= ctz(s) -> (t & -t) >= (s & -s)
      Node s = sv_t[1-index];
      // left hand side of side condition
      Node scl = nm->mkNode (BITVECTOR_UGE,
          nm->mkNode (BITVECTOR_AND, t, nm->mkNode (BITVECTOR_NEG, t)),
          nm->mkNode (BITVECTOR_AND, s, nm->mkNode (BITVECTOR_NEG, s)));
      // right hand side of side condition
      Node scr = nm->mkNode (EQUAL, nm->mkNode (BITVECTOR_MULT, x, s), t);
      // overall side condition
      Node sc = nm->mkNode (IMPLIES, scl, scr);
      // add side condition
      status.d_conds.push_back (sc);
      
      // get the skolem node for this side condition
      Node skv = getInversionNode (sc, solve_tn);
      // now solving with the skolem node as the RHS
      t = skv;

    }else if( k==BITVECTOR_NEG || k==BITVECTOR_NOT ){
      t = NodeManager::currentNM()->mkNode( k, t );
    //}else if( k==BITVECTOR_AND || k==BITVECTOR_OR ){
      // TODO
    //}else if( k==BITVECTOR_CONCAT ){
      // TODO
    //}else if( k==BITVECTOR_SHL || k==BITVECTOR_LSHR ){
      // TODO
    //}else if( k==BITVECTOR_ASHR ){
      // TODO
    }else{
      Trace("bv-invert") << "bv-invert : Unknown kind for bit-vector term " << k << ", from " << sv_t << std::endl;
      return Node::null();
    }
    sv_t = sv_t[index];
  }
  Assert( sv_t==sv );
  // finalize based on the kind of constraint
  //TODO
  if( rk==EQUAL ){
    return t;
  }else{
    Trace("bv-invert") << "bv-invert : Unknown relation kind for bit-vector literal " << rk << std::endl;
    return t;
  }
}

Node BvInverter::solve_bv_lit( Node sv, Node lit, bool pol, std::vector< unsigned >& path,
                               BvInverterModelQuery * m, BvInverterStatus& status ){
  Assert( !path.empty() );
  unsigned index = path.back();
  Assert( index<lit.getNumChildren() );
  path.pop_back();
  Kind k = lit.getKind();
  if( k==NOT ){
    Assert( index==0 );
    return solve_bv_lit( sv, lit[index], !pol, path, m, status );
  }else if( k==EQUAL ){
    return solve_bv_constraint( sv, lit[index], lit[1-index], k, pol, path, m, status );
  }else if( k==BITVECTOR_ULT || k==BITVECTOR_ULE || k==BITVECTOR_SLT || k==BITVECTOR_SLE ){
    if( !pol ){
      if( k==BITVECTOR_ULT ){
        k = index==1 ? BITVECTOR_ULE : BITVECTOR_UGE;
      }else if( k==BITVECTOR_ULE ){
        k = index==1 ? BITVECTOR_ULT : BITVECTOR_UGT;
      }else if( k==BITVECTOR_SLT ){
        k = index==1 ? BITVECTOR_SLE : BITVECTOR_SGE;
      }else{
        Assert( k==BITVECTOR_SLE );
        k = index==1 ? BITVECTOR_SLT : BITVECTOR_SGT;
      }
    }else if( index==1 ){
      if( k==BITVECTOR_ULT ){
        k = BITVECTOR_UGT;
      }else if( k==BITVECTOR_ULE ){
        k = BITVECTOR_UGE;
      }else if( k==BITVECTOR_SLT ){
        k = BITVECTOR_SGT;
      }else{
        Assert( k==BITVECTOR_SLE );
        k = BITVECTOR_SGE;
      }
    }
    return solve_bv_constraint( sv, lit[index], lit[1-index], k, true, path, m, status );
  }else{
    Trace("bv-invert") << "bv-invert : Unknown kind for bit-vector literal " << lit << std::endl;
  }
  return Node::null();
}

// this class can be used to query the model value through the CegInstaniator class
class CegInstantiatorBvInverterModelQuery : public BvInverterModelQuery {
protected:
  // pointer to class that is able to query model values
  CegInstantiator * d_ci;
public:
  CegInstantiatorBvInverterModelQuery( CegInstantiator * ci ) : 
    BvInverterModelQuery(), d_ci( ci ){}
  ~CegInstantiatorBvInverterModelQuery(){}
  // get the model value of n
  Node getModelValue( Node n ) {
    return d_ci->getModelValue( n );
  }
};

BvInstantiator::BvInstantiator( QuantifiersEngine * qe, TypeNode tn ) : Instantiator( qe, tn ){
  // get the global inverter utility
  // this must be global since we need to:
  // * process Skolem functions properly across multiple variables within the same quantifier
  // * cache Skolem variables uniformly across multiple quantified formulas
  d_inverter = qe->getBvInverter();
}

BvInstantiator::~BvInstantiator(){

}

void BvInstantiator::reset( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) {
  d_inst_id_counter = 0;
  d_var_to_inst_id.clear();
  d_inst_id_to_term.clear();
  d_inst_id_to_status.clear();
  d_var_to_curr_inst_id.clear();
}


void BvInstantiator::processLiteral( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort ) {
  Assert( d_inverter!=NULL );
  // find path to pv
  std::vector< unsigned > path;
  Node sv = d_inverter->getSolveVariable( pv.getType() );
  Node pvs = ci->getModelValue( pv );
  Node slit = d_inverter->getPathToPv( lit, pv, sv, pvs, path );
  if( !slit.isNull() ){
    CegInstantiatorBvInverterModelQuery m( ci );
    unsigned iid = d_inst_id_counter;
    Node inst = d_inverter->solve_bv_lit( sv, slit, true, path, &m, d_inst_id_to_status[iid] );
    if( !inst.isNull() ){
      // store information for id and increment
      d_var_to_inst_id[pv].push_back( iid );
      d_inst_id_to_term[iid] = inst;
      d_inst_id_counter++;
    }else{
      // cleanup information if we failed to solve
      d_inst_id_to_status.erase( iid );
    }
  }
}

bool BvInstantiator::hasProcessAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort ) {
  return true;
}

bool BvInstantiator::processAssertion( CegInstantiator * ci, SolvedForm& sf, Node pv, Node lit, unsigned effort ) {
  Trace("cegqi-bv") << "BvInstantiator::processAssertion : solve " << pv << " in " << lit << std::endl;
  if( options::cbqiBv() ){
    // if option enabled, use approach for word-level inversion for BV instantiation
    processLiteral( ci, sf, pv, lit, effort );
  }
  return false;
}

bool BvInstantiator::processAssertions( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& lits, unsigned effort ) {
  std::unordered_map< Node, std::vector< unsigned >, NodeHashFunction >::iterator iti = d_var_to_inst_id.find( pv );
  if( iti!=d_var_to_inst_id.end() ){
    Trace("cegqi-bv") << "BvInstantiator::processAssertions for " << pv << std::endl;
    // get inst id list
    Trace("cegqi-bv") << "  " << iti->second.size() << " candidate instantiations for " << pv << " : " << std::endl;
    // the order of instantiation ids we will try
    std::vector< unsigned > inst_ids_try;
    // until we have a model-preserving selection function for BV, this must be heuristic (we only pick one literal)
    // hence we randomize the list
    // this helps robustness, since picking the same literal every time may be lead to a stream of value instantiations
    std::random_shuffle( iti->second.begin(), iti->second.end() );
    
    for( unsigned j=0; j<iti->second.size(); j++ ){
      unsigned inst_id = iti->second[j];
      Assert( d_inst_id_to_term.find(inst_id)!=d_inst_id_to_term.end() );
      Node inst_term = d_inst_id_to_term[inst_id];
      // debug printing
      if( Trace.isOn("cegqi-bv") ){
        Trace("cegqi-bv") << "   [" << j << "] : ";
        Trace("cegqi-bv") << inst_term << std::endl;
        // process information about solved status
        std::unordered_map< unsigned, BvInverterStatus >::iterator its = d_inst_id_to_status.find( inst_id );
        Assert( its!=d_inst_id_to_status.end() );
        if( !(*its).second.d_conds.empty() ){
          Trace("cegqi-bv") << "   ...with " << (*its).second.d_conds.size() << " side conditions : " << std::endl;
          for( unsigned k=0; k<(*its).second.d_conds.size(); k++ ){
            Node cond = (*its).second.d_conds[k];
            Trace("cegqi-bv") << "       " << cond << std::endl;
          }
        }
        Trace("cegqi-bv") << std::endl;
      }
      // TODO : selection criteria across multiple literals goes here
      
      // currently, we use a naive heuristic which takes only the first solved term
      if( inst_ids_try.empty() ){
        inst_ids_try.push_back( inst_id );
      }
    }
    
    // now, try all instantiation ids we want to try
    // typically size( inst_ids_try )=0, otherwise worst-case performance for constructing
    // instantiations is exponential on the number of variables in this quantifier
    for( unsigned j = 0; j<inst_ids_try.size(); j++ ){
      unsigned inst_id = iti->second[j];
      Assert( d_inst_id_to_term.find(inst_id)!=d_inst_id_to_term.end() );
      Node inst_term = d_inst_id_to_term[inst_id];
      // try instantiation pv -> inst_term
      TermProperties pv_prop_bv;
      Trace("cegqi-bv") << "*** try " << pv << " -> " << inst_term << std::endl;
      d_var_to_curr_inst_id[pv] = inst_id;
      if( ci->doAddInstantiationInc( pv, inst_term, pv_prop_bv, sf, effort ) ){
        return true;
      }
    }
    Trace("cegqi-bv") << "...failed to add instantiation for " << pv << std::endl;
    d_var_to_curr_inst_id.erase( pv );
  }

  return false;
}


bool BvInstantiator::needsPostProcessInstantiationForVariable( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort ) {
  // we may need to post-process the instantiation since inversion skolems need to be finalized
  // TODO : technically skolem functions can appear in datatypes with bit-vector fields. We need to eliminate them there too.
  return true;
}

bool BvInstantiator::postProcessInstantiationForVariable( CegInstantiator * ci, SolvedForm& sf, Node pv, unsigned effort, std::vector< Node >& lemmas ) {
  Trace("cegqi-bv") << "BvInstantiator::postProcessInstantiation " << pv << std::endl;
  Assert( std::find( sf.d_vars.begin(), sf.d_vars.end(), pv )!=sf.d_vars.end() );
  unsigned index = std::find( sf.d_vars.begin(), sf.d_vars.end(), pv )-sf.d_vars.begin();
  Trace("cegqi-bv") << "  postprocess : " << pv << " -> " << sf.d_subs[index] << std::endl;
  // eliminate skolem functions from the substitution
  unsigned prev_lem_size = lemmas.size();
  sf.d_subs[index] = d_inverter->eliminateSkolemFunctions( sf.d_subs[index], lemmas );
  if( Trace.isOn("cegqi-bv") ){
    Trace("cegqi-bv") << "  got : " << pv << " -> " << sf.d_subs[index] << std::endl;
    for( unsigned i=prev_lem_size; i<lemmas.size(); i++ ){
      Trace("cegqi-bv") << "  side condition : " << lemmas[i] << std::endl;
    }
  }

  return true;
}


