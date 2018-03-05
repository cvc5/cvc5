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

#include "theory/quantifiers/cegqi/ceg_t_instantiator.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/ematching/trigger.h"

#include "theory/arith/arith_msum.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/theory_arith_private.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"
#include "util/random.h"

#include <algorithm>
#include <stack>

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

struct BvLinearAttributeId {};
using BvLinearAttribute = expr::Attribute<BvLinearAttributeId, bool>;

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
    val = NodeManager::currentNM()->mkNode( PLUS, val, NodeManager::currentNM()->mkNode( MULT, delta_coeff, ci->getQuantifiersEngine()->getTermUtil()->getVtsDelta() ) );
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
  if (ArithMSum::getMonomialSumLit(atom, msum))
  {
    Trace("cegqi-arith-debug") << "got monomial sum: " << std::endl;
    if( Trace.isOn("cegqi-arith-debug") ){
      ArithMSum::debugPrintMonomialSum(msum, "cegqi-arith-debug");
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
              vts_coeff[t] = ArithMSum::negate(vts_coeff[t]);
            }else{
              if( !pvtn.isInteger() ){
                vts_coeff[t] = NodeManager::currentNM()->mkNode( MULT, NodeManager::currentNM()->mkConst( Rational(-1) / itv->second.getConst<Rational>() ), vts_coeff[t] );
                vts_coeff[t] = Rewriter::rewrite( vts_coeff[t] );
              }else if( itv->second.getConst<Rational>().sgn()==1 ){
                vts_coeff[t] = ArithMSum::negate(vts_coeff[t]);
              }
            }
          }
          Trace("cegqi-arith-debug") << "vts[" << t << "] coefficient is " << vts_coeff[t] << std::endl;
          msum.erase( d_vts_sym[t] );
        }
      }
    }

    ires = ArithMSum::isolate(pv, msum, veq_c, val, atom.getKind());
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
        if( TermUtil::containsTerm( val, pv ) ){
          Trace("cegqi-arith-debug") << "fail : contains bad term" << std::endl;
          return 0;
        }
      }
      if( pvtn.isInteger() && ( ( !veq_c.isNull() && !veq_c.getType().isInteger() ) || !val.getType().isInteger() ) ){
        //redo, split integer/non-integer parts
        bool useCoeff = false;
        Integer coeff = ci->getQuantifiersEngine()->getTermUtil()->d_one.getConst<Rational>().getNumerator();
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
        realPart = real_part.empty() ? ci->getQuantifiersEngine()->getTermUtil()->d_zero : ( real_part.size()==1 ? real_part[0] : NodeManager::currentNM()->mkNode( PLUS, real_part ) );
        Assert( ci->getOutput()->isEligibleForInstantiation( realPart ) );
        //re-isolate
        Trace("cegqi-arith-debug") << "Re-isolate..." << std::endl;
        ires = ArithMSum::isolate(pv, msum, veq_c, val, atom.getKind());
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

void ArithInstantiator::reset(CegInstantiator* ci,
                              SolvedForm& sf,
                              Node pv,
                              CegInstEffort effort)
{
  d_vts_sym[0] = ci->getQuantifiersEngine()->getTermUtil()->getVtsInfinity( d_type, false, false );
  d_vts_sym[1] = ci->getQuantifiersEngine()->getTermUtil()->getVtsDelta( false, false );
  for( unsigned i=0; i<2; i++ ){
    d_mbp_bounds[i].clear();
    d_mbp_coeff[i].clear();
    for( unsigned j=0; j<2; j++ ){
      d_mbp_vts_coeff[i][j].clear();
    }
    d_mbp_lit[i].clear();
  }
}

bool ArithInstantiator::processEquality(CegInstantiator* ci,
                                        SolvedForm& sf,
                                        Node pv,
                                        std::vector<TermProperties>& term_props,
                                        std::vector<Node>& terms,
                                        CegInstEffort effort)
{
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
    if (ci->constructInstantiationInc(pv, val, pv_prop, sf))
    {
      return true;
    }
  }

  return false;
}

Node ArithInstantiator::hasProcessAssertion(CegInstantiator* ci,
                                            SolvedForm& sf,
                                            Node pv,
                                            Node lit,
                                            CegInstEffort effort)
{
  Node atom = lit.getKind()==NOT ? lit[0] : lit;
  bool pol = lit.getKind()!=NOT;
  //arithmetic inequalities and disequalities
  if (atom.getKind() == GEQ ||
      (atom.getKind() == EQUAL && !pol && atom[0].getType().isReal())) {
    return lit;
  } else {
    return Node::null();
  }
}

bool ArithInstantiator::processAssertion(CegInstantiator* ci,
                                         SolvedForm& sf,
                                         Node pv,
                                         Node lit,
                                         Node alit,
                                         CegInstEffort effort)
{
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
            is_upper = ( cmp!=ci->getQuantifiersEngine()->getTermUtil()->d_true );
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
          Node delta = ci->getQuantifiersEngine()->getTermUtil()->getVtsDelta();
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
        if (ci->constructInstantiationInc(pv, uval, pv_prop, sf))
        {
          return true;
        }
      }
    }
  }


  return false;
}

bool ArithInstantiator::processAssertions(CegInstantiator* ci,
                                          SolvedForm& sf,
                                          Node pv,
                                          CegInstEffort effort)
{
  if (options::cbqiModel()) {
    bool use_inf = ci->useVtsInfinity() && ( d_type.isInteger() ? options::cbqiUseInfInt() : options::cbqiUseInfReal() );
    bool upper_first = false;
    if( options::cbqiMinBounds() ){
      upper_first = d_mbp_bounds[1].size()<d_mbp_bounds[0].size();
    }
    int best_used[2];
    std::vector< Node > t_values[3];
    Node zero = ci->getQuantifiersEngine()->getTermUtil()->d_zero;
    Node one = ci->getQuantifiersEngine()->getTermUtil()->d_one;
    Node pv_value = ci->getModelValue( pv );
    //try optimal bounds
    for( unsigned r=0; r<2; r++ ){
      int rr = upper_first ? (1-r) : r;
      best_used[rr] = -1;
      if( d_mbp_bounds[rr].empty() ){
        if( use_inf ){
          Trace("cegqi-arith-bound") << "No " << ( rr==0 ? "lower" : "upper" ) << " bounds for " << pv << " (type=" << d_type << ")" << std::endl;
          //no bounds, we do +- infinity
          Node val = ci->getQuantifiersEngine()->getTermUtil()->getVtsInfinity( d_type );
          //TODO : rho value for infinity?
          if( rr==0 ){
            val = NodeManager::currentNM()->mkNode( UMINUS, val );
            val = Rewriter::rewrite( val );
          }
          TermProperties pv_prop_no_bound;
          if (ci->constructInstantiationInc(pv, val, pv_prop_no_bound, sf))
          {
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
                if( cmp_bound!=ci->getQuantifiersEngine()->getTermUtil()->d_true ){
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
          if (!options::cbqiMidpoint() || d_type.isInteger()
              || (ci->useVtsDelta() && d_mbp_vts_coeff[rr][1][best].isNull()))
          {
            Node val = d_mbp_bounds[rr][best];
            val = getModelBasedProjectionValue( ci, pv, val, rr==0, d_mbp_coeff[rr][best], pv_value, t_values[rr][best], sf.getTheta(),
                                                d_mbp_vts_coeff[rr][0][best], d_mbp_vts_coeff[rr][1][best] );
            if( !val.isNull() ){
              TermProperties pv_prop_bound;
              pv_prop_bound.d_coeff = d_mbp_coeff[rr][best];
              pv_prop_bound.d_type = rr==0 ? 1 : -1;
              if (ci->constructInstantiationInc(pv, val, pv_prop_bound, sf))
              {
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
        if (ci->constructInstantiationInc(pv, val, pv_prop_zero, sf))
        {
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
        if (ci->constructInstantiationInc(pv, val, pv_prop_midpoint, sf))
        {
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
              if (ci->constructInstantiationInc(
                      pv, val, pv_prop_nopt_bound, sf))
              {
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

bool ArithInstantiator::needsPostProcessInstantiationForVariable(
    CegInstantiator* ci, SolvedForm& sf, Node pv, CegInstEffort effort)
{
  return std::find( sf.d_non_basic.begin(), sf.d_non_basic.end(), pv )!=sf.d_non_basic.end();
}

bool ArithInstantiator::postProcessInstantiationForVariable(
    CegInstantiator* ci,
    SolvedForm& sf,
    Node pv,
    CegInstEffort effort,
    std::vector<Node>& lemmas)
{
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
  if (ArithMSum::getMonomialSumLit(eq, msum))
  {
    Node veq;
    if (ArithMSum::isolate(sf.d_vars[index], msum, veq, EQUAL, true) != 0)
    {
      Node veq_c;
      if( veq[0]!=sf.d_vars[index] ){
        Node veq_v;
        if (ArithMSum::getMonomial(veq[0], veq_c, veq_v))
        {
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
                ci->getQuantifiersEngine()->getTermUtil()->d_zero ),
              ci->getQuantifiersEngine()->getTermUtil()->d_zero, ci->getQuantifiersEngine()->getTermUtil()->d_one )
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

void DtInstantiator::reset(CegInstantiator* ci,
                           SolvedForm& sf,
                           Node pv,
                           CegInstEffort effort)
{
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
    if( TermUtil::containsTerm( ret, v ) ){
      ret = Node::null();
    }
  }
  return ret;
}

bool DtInstantiator::processEqualTerms(CegInstantiator* ci,
                                       SolvedForm& sf,
                                       Node pv,
                                       std::vector<Node>& eqc,
                                       CegInstEffort effort)
{
  Trace("cegqi-dt-debug") << "try based on constructors in equivalence class."
                          << std::endl;
  // look in equivalence class for a constructor
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
      if (ci->constructInstantiationInc(pv, val, pv_prop_dt, sf))
      {
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

bool DtInstantiator::processEquality(CegInstantiator* ci,
                                     SolvedForm& sf,
                                     Node pv,
                                     std::vector<TermProperties>& term_props,
                                     std::vector<Node>& terms,
                                     CegInstEffort effort)
{
  Node val = solve_dt( pv, terms[0], terms[1], terms[0], terms[1] );
  if( !val.isNull() ){
    TermProperties pv_prop;
    if (ci->constructInstantiationInc(pv, val, pv_prop, sf))
    {
      return true;
    }
  }
  return false;
}

void EprInstantiator::reset(CegInstantiator* ci,
                            SolvedForm& sf,
                            Node pv,
                            CegInstEffort effort)
{
  d_equal_terms.clear();
}

bool EprInstantiator::processEqualTerm(CegInstantiator* ci,
                                       SolvedForm& sf,
                                       Node pv,
                                       TermProperties& pv_prop,
                                       Node n,
                                       CegInstEffort effort)
{
  if( options::quantEprMatching() ){
    Assert( pv_prop.isBasic() );
    d_equal_terms.push_back( n );
    return false;
  }else{
    pv_prop.d_type = 0;
    return ci->constructInstantiationInc(pv, n, pv_prop, sf);
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
  if( inst::Trigger::isAtomicTrigger( catom ) && TermUtil::containsTerm( catom, pv ) ){
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

bool EprInstantiator::processEqualTerms(CegInstantiator* ci,
                                        SolvedForm& sf,
                                        Node pv,
                                        std::vector<Node>& eqc,
                                        CegInstEffort effort)
{
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
      if (ci->constructInstantiationInc(pv, d_equal_terms[i], pv_prop, sf))
      {
        return true;
      }
    }
  }
  return false;
}

// this class can be used to query the model value through the CegInstaniator class
class CegInstantiatorBvInverterQuery : public BvInverterQuery
{
 public:
  CegInstantiatorBvInverterQuery(CegInstantiator* ci)
      : BvInverterQuery(), d_ci(ci)
  {
  }
  ~CegInstantiatorBvInverterQuery() {}
  /** return the model value of n */
  Node getModelValue(Node n) override { return d_ci->getModelValue(n); }
  /** get bound variable of type tn */
  Node getBoundVariable(TypeNode tn) override
  {
    return d_ci->getBoundVariable(tn);
  }

 protected:
  // pointer to class that is able to query model values
  CegInstantiator * d_ci;
};

BvInstantiator::BvInstantiator(QuantifiersEngine* qe, TypeNode tn)
    : Instantiator(qe, tn), d_tried_assertion_inst(false)
{
  // get the global inverter utility
  // this must be global since we need to:
  // * process Skolem functions properly across multiple variables within the same quantifier
  // * cache Skolem variables uniformly across multiple quantified formulas
  d_inverter = qe->getBvInverter();
}

BvInstantiator::~BvInstantiator(){

}
void BvInstantiator::reset(CegInstantiator* ci,
                           SolvedForm& sf,
                           Node pv,
                           CegInstEffort effort)
{
  d_inst_id_counter = 0;
  d_var_to_inst_id.clear();
  d_inst_id_to_term.clear();
  d_inst_id_to_alit.clear();
  d_var_to_curr_inst_id.clear();
  d_alit_to_model_slack.clear();
  d_tried_assertion_inst = false;
}

void BvInstantiator::processLiteral(CegInstantiator* ci,
                                    SolvedForm& sf,
                                    Node pv,
                                    Node lit,
                                    Node alit,
                                    CegInstEffort effort)
{
  Assert(d_inverter != NULL);
  // find path to pv
  std::vector<unsigned> path;
  Node sv = d_inverter->getSolveVariable(pv.getType());
  Node pvs = ci->getModelValue(pv);
  Trace("cegqi-bv") << "Get path to pv : " << lit << std::endl;
  Node slit = d_inverter->getPathToPv(lit, pv, sv, pvs, path);
  if (!slit.isNull())
  {
    CegInstantiatorBvInverterQuery m(ci);
    unsigned iid = d_inst_id_counter;
    Trace("cegqi-bv") << "Solve lit to bv inverter : " << slit << std::endl;
    Node inst = d_inverter->solveBvLit(sv, slit, path, &m);
    if (!inst.isNull())
    {
      inst = Rewriter::rewrite(inst);
      if (inst.isConst() || !ci->hasNestedQuantification())
      {
        Trace("cegqi-bv") << "...solved form is " << inst << std::endl;
        // store information for id and increment
        d_var_to_inst_id[pv].push_back(iid);
        d_inst_id_to_term[iid] = inst;
        d_inst_id_to_alit[iid] = alit;
        d_inst_id_counter++;
      }
    }
    else
    {
      Trace("cegqi-bv") << "...failed to solve." << std::endl;
    }
  }
}

Node BvInstantiator::hasProcessAssertion(CegInstantiator* ci,
                                         SolvedForm& sf,
                                         Node pv,
                                         Node lit,
                                         CegInstEffort effort)
{
  if (effort == CEG_INST_EFFORT_FULL)
  {
    // always use model values at full effort
    return Node::null();
  }
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool pol = lit.getKind() != NOT;
  Kind k = atom.getKind();
  if (k != EQUAL && k != BITVECTOR_ULT && k != BITVECTOR_SLT)
  {
    // others are unhandled
    return Node::null();
  }
  else if (!atom[0].getType().isBitVector())
  {
    return Node::null();
  }
  else if (options::cbqiBvIneqMode() == CBQI_BV_INEQ_KEEP
           || (pol && k == EQUAL))
  {
    return lit;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node s = atom[0];
  Node t = atom[1];

  Node sm = ci->getModelValue(s);
  Node tm = ci->getModelValue(t);
  Assert(!sm.isNull() && sm.isConst());
  Assert(!tm.isNull() && tm.isConst());
  Trace("cegqi-bv") << "Model value: " << std::endl;
  Trace("cegqi-bv") << "   " << s << " " << k << " " << t << " is "
                    << std::endl;
  Trace("cegqi-bv") << "   " << sm << " <> " << tm << std::endl;

  Node ret;
  if (options::cbqiBvIneqMode() == CBQI_BV_INEQ_EQ_SLACK)
  {
    // if using slack, we convert constraints to a positive equality based on
    // the current model M, e.g.:
    //   (not) s ~ t  --->  s = t + ( s^M - t^M )
    if (sm != tm)
    {
      Node slack = Rewriter::rewrite(nm->mkNode(BITVECTOR_SUB, sm, tm));
      Assert(slack.isConst());
      // remember the slack value for the asserted literal
      d_alit_to_model_slack[lit] = slack;
      ret = nm->mkNode(EQUAL, s, nm->mkNode(BITVECTOR_PLUS, t, slack));
      Trace("cegqi-bv") << "Slack is " << slack << std::endl;
    }
    else
    {
      ret = s.eqNode(t);
    }
  } else {
    // turn disequality into an inequality
    // e.g. s != t becomes s < t or t < s
    if (k == EQUAL)
    {
      if (Random::getRandom().pickWithProb(0.5))
      {
        std::swap(s, t);
      }
      pol = true;
    }
    // otherwise, we optimistically solve for the boundary point of an
    // inequality, for example:
    //   for s < t, we solve s+1 = t
    //   for ~( s < t ), we solve s = t
    // notice that this equality does not necessarily hold in the model, and
    // hence the corresponding instantiation strategy is not guaranteed to be
    // monotonic.
    if (!pol)
    {
      ret = s.eqNode(t);
    } else {
      Node bv_one = bv::utils::mkOne(bv::utils::getSize(s));
      ret = nm->mkNode(BITVECTOR_PLUS, s, bv_one).eqNode(t);
    }
  }
  Trace("cegqi-bv") << "Process " << lit << " as " << ret << std::endl;
  return ret;
}

bool BvInstantiator::processAssertion(CegInstantiator* ci,
                                      SolvedForm& sf,
                                      Node pv,
                                      Node lit,
                                      Node alit,
                                      CegInstEffort effort)
{
  // if option enabled, use approach for word-level inversion for BV instantiation
  if( options::cbqiBv() ){
    // get the best rewritten form of lit for solving for pv 
    //   this should remove instances of non-invertible operators, and "linearize" lit with respect to pv as much as possible
    Node rlit = rewriteAssertionForSolvePv(ci, pv, lit);
    if( Trace.isOn("cegqi-bv") ){
      Trace("cegqi-bv") << "BvInstantiator::processAssertion : solve " << pv << " in " << lit << std::endl;
      if( lit!=rlit ){
        Trace("cegqi-bv") << "...rewritten to " << rlit << std::endl;
      }
    }
    if (!rlit.isNull())
    {
      processLiteral(ci, sf, pv, rlit, alit, effort);
    }
  }
  return false;
}

bool BvInstantiator::useModelValue(CegInstantiator* ci,
                                   SolvedForm& sf,
                                   Node pv,
                                   CegInstEffort effort)
{
  return !d_tried_assertion_inst
         && (effort < CEG_INST_EFFORT_FULL || options::cbqiFullEffort());
}

bool BvInstantiator::processAssertions(CegInstantiator* ci,
                                       SolvedForm& sf,
                                       Node pv,
                                       CegInstEffort effort)
{
  std::unordered_map< Node, std::vector< unsigned >, NodeHashFunction >::iterator iti = d_var_to_inst_id.find( pv );
  if( iti!=d_var_to_inst_id.end() ){
    Trace("cegqi-bv") << "BvInstantiator::processAssertions for " << pv << std::endl;
    // if interleaving, do not do inversion half the time
    if (!options::cbqiBvInterleaveValue() || Random::getRandom().pickWithProb(0.5))
    {
      bool firstVar = sf.empty();
      // get inst id list
      if (Trace.isOn("cegqi-bv"))
      {
        Trace("cegqi-bv") << "  " << iti->second.size()
                          << " candidate instantiations for " << pv << " : "
                          << std::endl;
        if (firstVar)
        {
          Trace("cegqi-bv") << "  ...this is the first variable" << std::endl;
        }
      }
      // until we have a model-preserving selection function for BV, this must
      // be heuristic (we only pick one literal)
      // hence we randomize the list
      // this helps robustness, since picking the same literal every time may
      // lead to a stream of value instantiations, whereas with randomization
      // we may find an invertible literal that leads to a useful instantiation.
      std::random_shuffle(iti->second.begin(), iti->second.end());

      if (Trace.isOn("cegqi-bv"))
      {
        for (unsigned j = 0, size = iti->second.size(); j < size; j++)
        {
          unsigned inst_id = iti->second[j];
          Assert(d_inst_id_to_term.find(inst_id) != d_inst_id_to_term.end());
          Node inst_term = d_inst_id_to_term[inst_id];
          Assert(d_inst_id_to_alit.find(inst_id) != d_inst_id_to_alit.end());
          Node alit = d_inst_id_to_alit[inst_id];

          // get the slack value introduced for the asserted literal
          Node curr_slack_val;
          std::unordered_map<Node, Node, NodeHashFunction>::iterator itms =
              d_alit_to_model_slack.find(alit);
          if (itms != d_alit_to_model_slack.end())
          {
            curr_slack_val = itms->second;
          }

          // debug printing
          Trace("cegqi-bv") << "   [" << j << "] : ";
          Trace("cegqi-bv") << inst_term << std::endl;
          if (!curr_slack_val.isNull()) {
            Trace("cegqi-bv") << "   ...with slack value : " << curr_slack_val
                              << std::endl;
          }
          Trace("cegqi-bv-debug") << "   ...from : " << alit << std::endl;
          Trace("cegqi-bv") << std::endl;
        }
      }

      // Now, try all instantiation ids we want to try
      // Typically we try only one, otherwise worst-case performance
      // for constructing instantiations is exponential on the number of
      // variables in this quantifier prefix.
      bool ret = false;
      bool tryMultipleInst = firstVar && options::cbqiMultiInst();
      bool revertOnSuccess = tryMultipleInst;
      for (unsigned j = 0, size = iti->second.size(); j < size; j++)
      {
        unsigned inst_id = iti->second[j];
        Assert(d_inst_id_to_term.find(inst_id) != d_inst_id_to_term.end());
        Node inst_term = d_inst_id_to_term[inst_id];
        Node alit = d_inst_id_to_alit[inst_id];
        // try instantiation pv -> inst_term
        TermProperties pv_prop_bv;
        Trace("cegqi-bv") << "*** try " << pv << " -> " << inst_term
                          << std::endl;
        d_var_to_curr_inst_id[pv] = inst_id;
        d_tried_assertion_inst = true;
        ci->markSolved(alit);
        if (ci->constructInstantiationInc(
                pv, inst_term, pv_prop_bv, sf, revertOnSuccess))
        {
          ret = true;
        }
        ci->markSolved(alit, false);
        // we are done unless we try multiple instances
        if (!tryMultipleInst)
        {
          break;
        }
      }
      if (ret)
      {
        return true;
      }
      Trace("cegqi-bv") << "...failed to add instantiation for " << pv
                        << std::endl;
      d_var_to_curr_inst_id.erase(pv);
    } else {
      Trace("cegqi-bv") << "...do not do instantiation for " << pv
                        << " (skip, based on heuristic)" << std::endl;
    }
  }

  return false;
}

Node BvInstantiator::rewriteAssertionForSolvePv(CegInstantiator* ci,
                                                Node pv,
                                                Node lit)
{
  // result of rewriting the visited term
  std::stack<std::unordered_map<TNode, Node, TNodeHashFunction> > visited;
  visited.push(std::unordered_map<TNode, Node, TNodeHashFunction>());
  // whether the visited term contains pv
  std::unordered_map<TNode, bool, TNodeHashFunction> visited_contains_pv;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::unordered_map<TNode, Node, TNodeHashFunction> curr_subs;
  std::stack<std::stack<TNode> > visit;
  TNode cur;
  visit.push(std::stack<TNode>());
  visit.top().push(lit);
  do {
    cur = visit.top().top();
    visit.top().pop();
    it = visited.top().find(cur);

    if (it == visited.top().end())
    {
      std::unordered_map<TNode, Node, TNodeHashFunction>::iterator itc =
          curr_subs.find(cur);
      if (itc != curr_subs.end())
      {
        visited.top()[cur] = itc->second;
      }
      else
      {
        if (cur.getKind() == CHOICE)
        {
          // must replace variables of choice functions
          // with new variables to avoid variable
          // capture when considering substitutions
          // with multiple literals.
          Node bv = ci->getBoundVariable(cur[0][0].getType());
          // should not have captured variables
          Assert(curr_subs.find(cur[0][0]) == curr_subs.end());
          curr_subs[cur[0][0]] = bv;
          // we cannot cache the results of subterms
          // of this choice expression since we are
          // now in the context { cur[0][0] -> bv },
          // hence we push a context here
          visited.push(std::unordered_map<TNode, Node, TNodeHashFunction>());
          visit.push(std::stack<TNode>());
        }
        visited.top()[cur] = Node::null();
        visit.top().push(cur);
        for (unsigned i = 0; i < cur.getNumChildren(); i++)
        {
          visit.top().push(cur[i]);
        }
      }
    } else if (it->second.isNull()) {
      Node ret;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED) {
        children.push_back(cur.getOperator());
      }
      bool contains_pv = ( cur==pv );
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        it = visited.top().find(cur[i]);
        Assert(it != visited.top().end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cur[i] != it->second;
        children.push_back(it->second);
        contains_pv = contains_pv || visited_contains_pv[cur[i]];
      }
      // careful that rewrites above do not affect whether this term contains pv
      visited_contains_pv[cur] = contains_pv;

      // rewrite the term
      ret = rewriteTermForSolvePv(pv, cur, children, visited_contains_pv);

      // return original if the above function does not produce a result
      if (ret.isNull()) {
        if (childChanged) {
          ret = NodeManager::currentNM()->mkNode(cur.getKind(), children);
        }else{
          ret = cur;
        }
      }

      /* We need to update contains_pv also for rewritten nodes, since
       * the normalizePv* functions rely on the information if pv occurs in a
       * rewritten node or not. */
      if (ret != cur)
      {
        contains_pv = (ret == pv);
        for (unsigned i = 0, size = ret.getNumChildren(); i < size; ++i)
        {
          contains_pv = contains_pv || visited_contains_pv[ret[i]];
        }
        visited_contains_pv[ret] = contains_pv;
      }

      // if was choice, pop context
      if (cur.getKind() == CHOICE)
      {
        Assert(curr_subs.find(cur[0][0]) != curr_subs.end());
        curr_subs.erase(cur[0][0]);
        visited.pop();
        visit.pop();
        Assert(visited.size() == visit.size());
        Assert(!visit.empty());
      }

      visited.top()[cur] = ret;
    }
  } while (!visit.top().empty());
  Assert(visited.size() == 1);
  Assert(visited.top().find(lit) != visited.top().end());
  Assert(!visited.top().find(lit)->second.isNull());

  Node result = visited.top()[lit];

  if (Trace.isOn("cegqi-bv-nl"))
  {
    std::vector<TNode> trace_visit;
    std::unordered_set<TNode, TNodeHashFunction> trace_visited;

    trace_visit.push_back(result);
    do
    {
      cur = trace_visit.back();
      trace_visit.pop_back();

      if (trace_visited.find(cur) == trace_visited.end())
      {
        trace_visited.insert(cur);
        trace_visit.insert(trace_visit.end(), cur.begin(), cur.end());
      }
      else if (cur == pv)
      {
        Trace("cegqi-bv-nl")
            << "NONLINEAR LITERAL for " << pv << " : " << lit << std::endl;
      }
    } while (!trace_visit.empty());
  }

  return result;
}

/**
 * Determine coefficient of pv in term n, where n has the form pv, -pv, pv * t,
 * or -pv * t. Extracting the coefficient of multiplications only succeeds if
 * the multiplication are normalized with normalizePvMult.
 *
 * If sucessful it returns
 *   1    if n ==  pv,
 *  -1    if n == -pv,
 *   t    if n ==  pv * t,
 *  -t    if n == -pv * t.
 * If n is not a linear term, a null node is returned.
 */
static Node getPvCoeff(TNode pv, TNode n)
{
  bool neg = false;
  Node coeff;

  if (n.getKind() == BITVECTOR_NEG)
  {
    neg = true;
    n = n[0];
  }

  if (n == pv)
  {
    coeff = bv::utils::mkOne(bv::utils::getSize(pv));
  }
  /* All multiplications are normalized to pv * (t1 * t2). */
  else if (n.getKind() == BITVECTOR_MULT && n.getAttribute(BvLinearAttribute()))
  {
    Assert(n.getNumChildren() == 2);
    Assert(n[0] == pv);
    coeff = n[1];
  }
  else /* n is in no form to extract the coefficient for pv */
  {
    Trace("cegqi-bv-nl") << "Cannot extract coefficient for " << pv << " in "
                         << n << std::endl;
    return Node::null();
  }
  Assert(!coeff.isNull());

  if (neg) return NodeManager::currentNM()->mkNode(BITVECTOR_NEG, coeff);
  return coeff;
}

/**
 * Normalizes the children of a BITVECTOR_MULT w.r.t. pv. contains_pv marks
 * terms in which pv occurs.
 * For example,
 *
 *  a * -pv * b * c
 *
 * is rewritten to
 *
 *  pv * -(a * b * c)
 *
 * Returns the normalized node if the resulting term is linear w.r.t. pv and
 * a null node otherwise. If pv does not occur in children it returns a
 * multiplication over children.
 */
static Node normalizePvMult(
    TNode pv,
    const std::vector<Node>& children,
    std::unordered_map<TNode, bool, TNodeHashFunction>& contains_pv)
{
  bool neg, neg_coeff = false;
  bool found_pv = false;
  NodeManager* nm;
  NodeBuilder<> nb(BITVECTOR_MULT);
  BvLinearAttribute is_linear;

  nm = NodeManager::currentNM();
  for (TNode nc : children)
  {
    if (!contains_pv[nc])
    {
      nb << nc;
      continue;
    }

    neg = false;
    if (nc.getKind() == BITVECTOR_NEG)
    {
      neg = true;
      nc = nc[0];
    }

    if (!found_pv && nc == pv)
    {
      found_pv = true;
      neg_coeff = neg;
      continue;
    }
    else if (!found_pv && nc.getKind() == BITVECTOR_MULT
             && nc.getAttribute(is_linear))
    {
      Assert(nc.getNumChildren() == 2);
      Assert(nc[0] == pv);
      Assert(!contains_pv[nc[1]]);
      found_pv = true;
      neg_coeff = neg;
      nb << nc[1];
      continue;
    }
    return Node::null(); /* non-linear */
  }
  Assert(nb.getNumChildren() > 0);

  Node coeff = (nb.getNumChildren() == 1) ? nb[0] : nb.constructNode();
  if (neg_coeff)
  {
    coeff = nm->mkNode(BITVECTOR_NEG, coeff);
  }
  coeff = Rewriter::rewrite(coeff);
  unsigned size_coeff = bv::utils::getSize(coeff);
  Node zero = bv::utils::mkZero(size_coeff);
  if (coeff == zero)
  {
    return zero;
  }
  Node result;
  if (found_pv)
  {
    if (coeff == bv::utils::mkOne(size_coeff))
    {
      return pv;
    }
    result = nm->mkNode(BITVECTOR_MULT, pv, coeff);
    contains_pv[result] = true;
    result.setAttribute(is_linear, true);
  }
  else
  {
    result = coeff;
  }
  return result;
}

#ifdef CVC4_ASSERTIONS
static bool isLinearPlus(
    TNode n,
    TNode pv,
    std::unordered_map<TNode, bool, TNodeHashFunction>& contains_pv)
{
  Node coeff;
  Assert(n.getAttribute(BvLinearAttribute()));
  Assert(n.getNumChildren() == 2);
  if (n[0] != pv)
  {
    Assert(n[0].getKind() == BITVECTOR_MULT);
    Assert(n[0].getNumChildren() == 2);
    Assert(n[0][0] == pv);
    Assert(!contains_pv[n[0][1]]);
  }
  Assert(!contains_pv[n[1]]);
  coeff = getPvCoeff(pv, n[0]);
  Assert(!coeff.isNull());
  Assert(!contains_pv[coeff]);
  return true;
}
#endif

/**
 * Normalizes the children of a BITVECTOR_PLUS w.r.t. pv. contains_pv marks
 * terms in which pv occurs.
 * For example,
 *
 *  a * pv + b + c * -pv
 *
 * is rewritten to
 *
 *  pv * (a - c) + b
 *
 * Returns the normalized node if the resulting term is linear w.r.t. pv and
 * a null node otherwise. If pv does not occur in children it returns an
 * addition over children.
 */
static Node normalizePvPlus(
    Node pv,
    const std::vector<Node>& children,
    std::unordered_map<TNode, bool, TNodeHashFunction>& contains_pv)
{
  NodeManager* nm;
  NodeBuilder<> nb_c(BITVECTOR_PLUS);
  NodeBuilder<> nb_l(BITVECTOR_PLUS);
  BvLinearAttribute is_linear;
  bool neg;

  nm = NodeManager::currentNM();
  for (TNode nc : children)
  {
    if (!contains_pv[nc])
    {
      nb_l << nc;
      continue;
    }

    neg = false;
    if (nc.getKind() == BITVECTOR_NEG)
    {
      neg = true;
      nc = nc[0];
    }

    if (nc == pv
        || (nc.getKind() == BITVECTOR_MULT && nc.getAttribute(is_linear)))
    {
      Node coeff = getPvCoeff(pv, nc);
      Assert(!coeff.isNull());
      if (neg)
      {
        coeff = nm->mkNode(BITVECTOR_NEG, coeff);
      }
      nb_c << coeff;
      continue;
    }
    else if (nc.getKind() == BITVECTOR_PLUS && nc.getAttribute(is_linear))
    {
      Assert(isLinearPlus(nc, pv, contains_pv));
      Node coeff = getPvCoeff(pv, nc[0]);
      Assert(!coeff.isNull());
      Node leaf = nc[1];
      if (neg)
      {
        coeff = nm->mkNode(BITVECTOR_NEG, coeff);
        leaf = nm->mkNode(BITVECTOR_NEG, leaf);
      }
      nb_c << coeff;
      nb_l << leaf;
      continue;
    }
    /* can't collect coefficients of 'pv' in 'cur' -> non-linear */
    return Node::null();
  }
  Assert(nb_c.getNumChildren() > 0 || nb_l.getNumChildren() > 0);

  Node pv_mult_coeffs, result;
  if (nb_c.getNumChildren() > 0)
  {
    Node coeffs = (nb_c.getNumChildren() == 1) ? nb_c[0] : nb_c.constructNode();
    coeffs = Rewriter::rewrite(coeffs);
    result = pv_mult_coeffs = normalizePvMult(pv, {pv, coeffs}, contains_pv);
  }

  if (nb_l.getNumChildren() > 0)
  {
    Node leafs = (nb_l.getNumChildren() == 1) ? nb_l[0] : nb_l.constructNode();
    leafs = Rewriter::rewrite(leafs);
    Node zero = bv::utils::mkZero(bv::utils::getSize(pv));
    /* pv * 0 + t --> t */
    if (pv_mult_coeffs.isNull() || pv_mult_coeffs == zero)
    {
      result = leafs;
    }
    else
    {
      result = nm->mkNode(BITVECTOR_PLUS, pv_mult_coeffs, leafs);
      contains_pv[result] = true;
      result.setAttribute(is_linear, true);
    }
  }
  Assert(!result.isNull());
  return result;
}

/**
 * Linearize an equality w.r.t. pv such that pv only occurs once. contains_pv
 * marks terms in which pv occurs.
 * For example, equality
 *
 *   -pv * a + b = c + pv
 *
 * rewrites to
 *
 *   pv * (-a - 1) = c - b.
 */
static Node normalizePvEqual(
    Node pv,
    const std::vector<Node>& children,
    std::unordered_map<TNode, bool, TNodeHashFunction>& contains_pv)
{
  Assert(children.size() == 2);

  NodeManager* nm = NodeManager::currentNM();
  BvLinearAttribute is_linear;
  Node coeffs[2], leafs[2];
  bool neg;
  TNode child;

  for (unsigned i = 0; i < 2; ++i)
  {
    child = children[i];
    neg = false;
    if (child.getKind() == BITVECTOR_NEG)
    {
      neg = true;
      child = child[0];
    }
    if (child.getAttribute(is_linear) || child == pv)
    {
      if (child.getKind() == BITVECTOR_PLUS)
      {
        Assert(isLinearPlus(child, pv, contains_pv));
        coeffs[i] = getPvCoeff(pv, child[0]);
        leafs[i] = child[1];
      }
      else
      {
        Assert(child.getKind() == BITVECTOR_MULT || child == pv);
        coeffs[i] = getPvCoeff(pv, child);
      }
    }
    if (neg)
    {
      if (!coeffs[i].isNull())
      {
        coeffs[i] = nm->mkNode(BITVECTOR_NEG, coeffs[i]);
      }
      if (!leafs[i].isNull())
      {
        leafs[i] = nm->mkNode(BITVECTOR_NEG, leafs[i]);
      }
    }
  }

  if (coeffs[0].isNull() || coeffs[1].isNull())
  {
    return Node::null();
  }

  Node coeff = nm->mkNode(BITVECTOR_SUB, coeffs[0], coeffs[1]);
  coeff = Rewriter::rewrite(coeff);
  std::vector<Node> mult_children = {pv, coeff};
  Node lhs = normalizePvMult(pv, mult_children, contains_pv);

  Node rhs;
  if (!leafs[0].isNull() && !leafs[1].isNull())
  {
    rhs = nm->mkNode(BITVECTOR_SUB, leafs[1], leafs[0]);
  }
  else if (!leafs[0].isNull())
  {
    rhs = nm->mkNode(BITVECTOR_NEG, leafs[0]);
  }
  else if (!leafs[1].isNull())
  {
    rhs = leafs[1];
  }
  else
  {
    rhs = bv::utils::mkZero(bv::utils::getSize(pv));
  }
  rhs = Rewriter::rewrite(rhs);

  if (lhs == rhs)
  {
    return bv::utils::mkTrue();
  }

  Node result = lhs.eqNode(rhs);
  contains_pv[result] = true;
  return result;
}

Node BvInstantiator::rewriteTermForSolvePv(
    Node pv,
    Node n,
    std::vector<Node>& children,
    std::unordered_map<TNode, bool, TNodeHashFunction>& contains_pv)
{
  NodeManager* nm = NodeManager::currentNM();

  // [1] rewrite cases of non-invertible operators

  if (n.getKind() == EQUAL)
  {
    TNode lhs = children[0];
    TNode rhs = children[1];

    /* rewrite: x * x = x -> x < 2 */
    if ((lhs == pv && rhs.getKind() == BITVECTOR_MULT && rhs[0] == pv
         && rhs[1] == pv)
        || (rhs == pv && lhs.getKind() == BITVECTOR_MULT && lhs[0] == pv
            && lhs[1] == pv))
    {
      return nm->mkNode(
          BITVECTOR_ULT,
          pv,
          bv::utils::mkConst(BitVector(bv::utils::getSize(pv), Integer(2))));
    }

    if (options::cbqiBvLinearize() && contains_pv[lhs] && contains_pv[rhs])
    {
      Node result = normalizePvEqual(pv, children, contains_pv);
      if (!result.isNull())
      {
        Trace("cegqi-bv-nl")
            << "Normalize " << n << " to " << result << std::endl;
      }
      else
      {
        Trace("cegqi-bv-nl")
            << "Nonlinear " << n.getKind() << " " << n << std::endl;
      }
      return result;
    }
  }
  else if (n.getKind() == BITVECTOR_MULT || n.getKind() == BITVECTOR_PLUS)
  {
    if (options::cbqiBvLinearize() && contains_pv[n])
    {
      Node result;
      if (n.getKind() == BITVECTOR_MULT)
      {
        result = normalizePvMult(pv, children, contains_pv);
      }
      else
      {
        result = normalizePvPlus(pv, children, contains_pv);
      }
      if (!result.isNull())
      {
        Trace("cegqi-bv-nl")
            << "Normalize " << n << " to " << result << std::endl;
        return result;
      }
      else
      {
        Trace("cegqi-bv-nl")
            << "Nonlinear " << n.getKind() << " " << n << std::endl;
      }
    }
  }

  // [2] try to rewrite non-linear literals -> linear literals

  return Node::null();
}

/** sort bv extract interval
 *
 * This sorts lists of bitvector extract terms where
 * ((_ extract i1 i2) t) < ((_ extract j1 j2) t)
 * if i1>j1 or i1=j1 and i2>j2.
 */
struct SortBvExtractInterval
{
  bool operator()(Node i, Node j)
  {
    Assert(i.getKind() == BITVECTOR_EXTRACT);
    Assert(j.getKind() == BITVECTOR_EXTRACT);
    BitVectorExtract ie = i.getOperator().getConst<BitVectorExtract>();
    BitVectorExtract je = j.getOperator().getConst<BitVectorExtract>();
    if (ie.high > je.high)
    {
      return true;
    }
    else if (ie.high == je.high)
    {
      Assert(ie.low != je.low);
      return ie.low > je.low;
    }
    return false;
  }
};

void BvInstantiatorPreprocess::registerCounterexampleLemma(
    std::vector<Node>& lems, std::vector<Node>& ce_vars)
{
  // new variables
  std::vector<Node> vars;
  // new lemmas
  std::vector<Node> new_lems;

  if (options::cbqiBvRmExtract())
  {
    NodeManager* nm = NodeManager::currentNM();
    Trace("cegqi-bv-pp") << "-----remove extracts..." << std::endl;
    // map from terms to bitvector extracts applied to that term
    std::map<Node, std::vector<Node> > extract_map;
    std::unordered_set<TNode, TNodeHashFunction> visited;
    for (unsigned i = 0, size = lems.size(); i < size; i++)
    {
      Trace("cegqi-bv-pp-debug2") << "Register ce lemma # " << i << " : "
                                  << lems[i] << std::endl;
      collectExtracts(lems[i], extract_map, visited);
    }
    for (std::pair<const Node, std::vector<Node> >& es : extract_map)
    {
      // sort based on the extract start position
      std::vector<Node>& curr_vec = es.second;

      SortBvExtractInterval sbei;
      std::sort(curr_vec.begin(), curr_vec.end(), sbei);

      unsigned width = es.first.getType().getBitVectorSize();

      // list of points b such that:
      //   b>0 and we must start a segment at (b-1)  or  b==0
      std::vector<unsigned> boundaries;
      boundaries.push_back(width);
      boundaries.push_back(0);

      Trace("cegqi-bv-pp") << "For term " << es.first << " : " << std::endl;
      for (unsigned i = 0, size = curr_vec.size(); i < size; i++)
      {
        Trace("cegqi-bv-pp") << "  " << i << " : " << curr_vec[i] << std::endl;
        BitVectorExtract e =
            curr_vec[i].getOperator().getConst<BitVectorExtract>();
        if (std::find(boundaries.begin(), boundaries.end(), e.high + 1)
            == boundaries.end())
        {
          boundaries.push_back(e.high + 1);
        }
        if (std::find(boundaries.begin(), boundaries.end(), e.low)
            == boundaries.end())
        {
          boundaries.push_back(e.low);
        }
      }
      std::sort(boundaries.rbegin(), boundaries.rend());

      // make the extract variables
      std::vector<Node> children;
      for (unsigned i = 1; i < boundaries.size(); i++)
      {
        Assert(boundaries[i - 1] > 0);
        Node ex = bv::utils::mkExtract(
            es.first, boundaries[i - 1] - 1, boundaries[i]);
        Node var =
            nm->mkSkolem("ek",
                         ex.getType(),
                         "variable to represent disjoint extract region");
        children.push_back(var);
        vars.push_back(var);
      }

      Node conc = nm->mkNode(kind::BITVECTOR_CONCAT, children);
      Assert(conc.getType() == es.first.getType());
      Node eq_lem = conc.eqNode(es.first);
      Trace("cegqi-bv-pp") << "Introduced : " << eq_lem << std::endl;
      new_lems.push_back(eq_lem);
      Trace("cegqi-bv-pp") << "...finished processing extracts for term "
                            << es.first << std::endl;
    }
    Trace("cegqi-bv-pp") << "-----done remove extracts" << std::endl;
  }

  if (!vars.empty())
  {
    // could try applying subs -> vars here
    // in practice, this led to worse performance

    Trace("cegqi-bv-pp") << "Adding " << new_lems.size() << " lemmas..."
                         << std::endl;
    lems.insert(lems.end(), new_lems.begin(), new_lems.end());
    Trace("cegqi-bv-pp") << "Adding " << vars.size() << " variables..."
                         << std::endl;
    ce_vars.insert(ce_vars.end(), vars.begin(), vars.end());
  }
}

void BvInstantiatorPreprocess::collectExtracts(
    Node lem,
    std::map<Node, std::vector<Node> >& extract_map,
    std::unordered_set<TNode, TNodeHashFunction>& visited)
{
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(lem);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.getKind() != FORALL)
      {
        if (cur.getKind() == BITVECTOR_EXTRACT)
        {
          extract_map[cur[0]].push_back(cur);
        }

        for (const Node& nc : cur)
        {
          visit.push_back(nc);
        }
      }
    }
  } while (!visit.empty());
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
