/*********************                                                        */
/*! \file ceg_instantiator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of counterexample-guided quantifier instantiation
 **/
 
#include "theory/quantifiers/ceg_instantiator.h"
#include "theory/quantifiers/ceg_t_instantiator.h"

#include "options/quantifiers_options.h"
#include "smt/ite_removal.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/trigger.h"
#include "theory/theory_engine.h"


using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

CegInstantiator::CegInstantiator( QuantifiersEngine * qe, CegqiOutput * out, bool use_vts_delta, bool use_vts_inf ) :
d_qe( qe ), d_out( out ), d_use_vts_delta( use_vts_delta ), d_use_vts_inf( use_vts_inf ){
  d_is_nested_quant = false;
}

CegInstantiator::~CegInstantiator() {
  for( std::map< Node, Instantiator * >::iterator it = d_instantiator.begin(); it != d_instantiator.end(); ++it ){
    delete it->second;
  }
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
      //selectors applied to program variables are also variables
      if( n.getKind()==APPLY_SELECTOR_TOTAL && d_prog_var[n].find( n[0] )!=d_prog_var[n].end() ){
        d_prog_var[n][n] = true;
      }
    }
  }
}

bool CegInstantiator::isEligible( Node n ) {
  //compute d_subs_fv, which program variables are contained in n, and determines if eligible
  computeProgVars( n );
  return d_inelig.find( n )==d_inelig.end();
}

bool CegInstantiator::hasVariable( Node n, Node pv ) {
  computeProgVars( n );
  return d_prog_var[n].find( pv )!=d_prog_var[n].end();
}


void CegInstantiator::registerInstantiationVariable( Node v, unsigned index ) {
  if( d_instantiator.find( v )==d_instantiator.end() ){
    TypeNode tn = v.getType();
    Instantiator * vinst;
    if( tn.isReal() ){
      vinst = new ArithInstantiator( d_qe, tn );
    }else if( tn.isSort() ){
      Assert( options::quantEpr() );
      vinst = new EprInstantiator( d_qe, tn );
    }else if( tn.isDatatype() ){
      vinst = new DtInstantiator( d_qe, tn );
    }else if( tn.isBitVector() ){
      vinst = new BvInstantiator( d_qe, tn );
    }else if( tn.isBoolean() ){
      vinst = new ModelValueInstantiator( d_qe, tn );
    }else{
      //default
      vinst = new Instantiator( d_qe, tn );
    }
    d_instantiator[v] = vinst;
  }
  d_curr_subs_proc[v].clear();
  d_curr_index[v] = index;
}

void CegInstantiator::unregisterInstantiationVariable( Node v ) {
  d_curr_subs_proc.erase( v );
  d_curr_index.erase( v );
}

bool CegInstantiator::doAddInstantiation( SolvedForm& sf, unsigned i, unsigned effort ){
  if( i==d_vars.size() ){
    //solved for all variables, now construct instantiation
    bool needsPostprocess = false;
    std::map< Instantiator *, Node > pp_inst;
    for( std::map< Node, Instantiator * >::iterator ita = d_active_instantiators.begin(); ita != d_active_instantiators.end(); ++ita ){
      if( ita->second->needsPostProcessInstantiation( this, sf, ita->first, effort ) ){
        needsPostprocess = true;
        pp_inst[ ita->second ] = ita->first;
      }
    }
    if( needsPostprocess ){
      //must make copy so that backtracking reverts sf
      SolvedForm sf_tmp;
      sf_tmp.copy( sf );
      bool postProcessSuccess = true;
      for( std::map< Instantiator *, Node >::iterator itp = pp_inst.begin(); itp != pp_inst.end(); ++itp ){
        if( !itp->first->postProcessInstantiation( this, sf_tmp, itp->second, effort ) ){
          postProcessSuccess = false;
          break;
        }
      } 
      if( postProcessSuccess ){
        return doAddInstantiation( sf_tmp.d_subs, sf_tmp.d_vars );
      }else{
        return false;
      }
    }else{
      return doAddInstantiation( sf.d_subs, sf.d_vars );
    }
  }else{
    //Node v = d_single_inv_map_to_prog[d_single_inv[0][i]];
    bool is_cv = false;
    Node pv;
    if( d_stack_vars.empty() ){
      pv = d_vars[i];
    }else{
      pv = d_stack_vars.back();
      is_cv = true;
      d_stack_vars.pop_back();
    }
    registerInstantiationVariable( pv, i );

    //get the instantiator object
    Instantiator * vinst = NULL;
    std::map< Node, Instantiator * >::iterator itin = d_instantiator.find( pv );
    if( itin!=d_instantiator.end() ){
      vinst = itin->second;
    }
    Assert( vinst!=NULL );
    d_active_instantiators[pv] = vinst;
    vinst->reset( this, sf, pv, effort );

    TypeNode pvtn = pv.getType();
    TypeNode pvtnb = pvtn.getBaseType();
    Node pvr = pv;
    if( d_qe->getMasterEqualityEngine()->hasTerm( pv ) ){
      pvr = d_qe->getMasterEqualityEngine()->getRepresentative( pv );
    }
    Trace("cbqi-inst-debug") << "[Find instantiation for " << pv << "], rep=" << pvr << ", instantiator is " << vinst->identify() << std::endl;
    Node pv_value;
    if( options::cbqiModel() ){
      pv_value = getModelValue( pv );
      Trace("cbqi-bound2") << "...M( " << pv << " ) = " << pv_value << std::endl;
    }

    //if in effort=2, we must choose at least one model value
    if( (i+1)<d_vars.size() || effort!=2 ){

      //[1] easy case : pv is in the equivalence class as another term not containing pv
      Trace("cbqi-inst-debug") << "[1] try based on equivalence class." << std::endl;
      std::map< Node, std::vector< Node > >::iterator it_eqc = d_curr_eqc.find( pvr );
      if( it_eqc!=d_curr_eqc.end() ){
        //std::vector< Node > eq_candidates;
        Trace("cbqi-inst-debug2") << "...eqc has size " << it_eqc->second.size() << std::endl;
        for( unsigned k=0; k<it_eqc->second.size(); k++ ){
          Node n = it_eqc->second[k];
          if( n!=pv ){
            Trace("cbqi-inst-debug") << "...try based on equal term " << n << std::endl;
            //must be an eligible term
            if( isEligible( n ) ){
              Node ns;
              Node pv_coeff;  //coefficient of pv in the equality we solve (null is 1)
              bool proc = false;
              if( !d_prog_var[n].empty() ){
                ns = applySubstitution( pvtn, n, sf, pv_coeff, false );
                if( !ns.isNull() ){
                  computeProgVars( ns );
                  //substituted version must be new and cannot contain pv
                  proc = d_prog_var[ns].find( pv )==d_prog_var[ns].end();
                }
              }else{
                ns = n;
                proc = true;
              }
              if( proc ){
                if( vinst->processEqualTerm( this, sf, pv, pv_coeff, ns, effort ) ){
                  return true;
                }
              }
            }
          }
        }
        if( vinst->processEqualTerms( this, sf, pv, it_eqc->second, effort ) ){
          return true;
        }
      }else{
        Trace("cbqi-inst-debug2") << "...eqc not found." << std::endl;
      }

      //[3] : we can solve an equality for pv
      ///iterate over equivalence classes to find cases where we can solve for the variable
      if( vinst->hasProcessEquality( this, sf, pv, effort ) ){
        Trace("cbqi-inst-debug") << "[3] try based on solving equalities." << std::endl;
        for( unsigned k=0; k<d_curr_type_eqc[pvtnb].size(); k++ ){
          Node r = d_curr_type_eqc[pvtnb][k];
          std::map< Node, std::vector< Node > >::iterator it_reqc = d_curr_eqc.find( r );
          std::vector< Node > lhs;
          std::vector< bool > lhs_v;
          std::vector< Node > lhs_coeff;
          Assert( it_reqc!=d_curr_eqc.end() );
          for( unsigned kk=0; kk<it_reqc->second.size(); kk++ ){
            Node n = it_reqc->second[kk];
            Trace("cbqi-inst-debug2") << "...look at term " << n << std::endl;
            //must be an eligible term
            if( isEligible( n ) ){
              Node ns;
              Node pv_coeff;
              if( !d_prog_var[n].empty() ){
                ns = applySubstitution( pvtn, n, sf, pv_coeff );
                if( !ns.isNull() ){
                  computeProgVars( ns );
                }
              }else{
                ns = n;
              }
              if( !ns.isNull() ){
                bool hasVar = d_prog_var[ns].find( pv )!=d_prog_var[ns].end();
                Trace("cbqi-inst-debug2") << "... " << ns << " has var " << pv << " : " << hasVar << std::endl;
                std::vector< Node > term_coeffs;
                std::vector< Node > terms;
                term_coeffs.push_back( pv_coeff );
                terms.push_back( ns );
                for( unsigned j=0; j<lhs.size(); j++ ){
                  //if this term or the another has pv in it, try to solve for it
                  if( hasVar || lhs_v[j] ){
                    Trace("cbqi-inst-debug") << "... " << i << "...try based on equality " << lhs[j] << " = " << ns << std::endl;
                    //processEquality( CegInstantiator * ci, SolvedForm& sf, Node pv, std::vector< Node >& term_coeffs, std::vector< Node >& terms, unsigned effort ) { return false; }
                    term_coeffs.push_back( lhs_coeff[j] );
                    terms.push_back( lhs[j] );
                    if( vinst->processEquality( this, sf, pv, term_coeffs, terms, effort ) ){
                      return true;
                    }
                    term_coeffs.pop_back();
                    terms.pop_back();
                  }
                }
                lhs.push_back( ns );
                lhs_v.push_back( hasVar );
                lhs_coeff.push_back( pv_coeff );
              }else{
                Trace("cbqi-inst-debug2") << "... term " << n << " is ineligible after substitution." << std::endl;
              }
            }else{
              Trace("cbqi-inst-debug2") << "... term " << n << " is ineligible." << std::endl;
            }
          }
        }
      }

      //[4] directly look at assertions
      if( vinst->hasProcessAssertion( this, sf, pv, effort ) ){
        Trace("cbqi-inst-debug") << "[4] try based on assertions." << std::endl;
        std::vector< Node > lits;
        //unsigned rmax = Theory::theoryOf( pv )==Theory::theoryOf( pv.getType() ) ? 1 : 2;
        for( unsigned r=0; r<2; r++ ){
          TheoryId tid = r==0 ? Theory::theoryOf( pvtn ) : THEORY_UF;
          Trace("cbqi-inst-debug2") << "  look at assertions of " << tid << std::endl;
          std::map< TheoryId, std::vector< Node > >::iterator ita = d_curr_asserts.find( tid );
          if( ita!=d_curr_asserts.end() ){
            for (unsigned j = 0; j<ita->second.size(); j++) {
              Node lit = ita->second[j];
              if( std::find( lits.begin(), lits.end(), lit )==lits.end() ){
                lits.push_back( lit );
                if( vinst->processAssertion( this, sf, pv, lit, effort ) ){
                  return true;
                }
              }
            }
          }
        }
        if( vinst->processAssertions( this, sf, pv, lits, effort ) ){
          return true;
        }
      }
    }

    //[5] resort to using value in model
    // do so if we are in effort=1, or if the variable is boolean, or if we are solving for a subfield of a datatype
    bool use_model_value = vinst->useModelValue( this, sf, pv, effort );
    if( ( effort>0 || use_model_value || is_cv ) && vinst->allowModelValue( this, sf, pv, effort ) ){
#ifdef CVC4_ASSERTIONS
      if( pvtn.isReal() && options::cbqiNestedQE() && !options::cbqiAll() ){
        Trace("cbqi-warn") << "Had to resort to model value." << std::endl;
        Assert( false );
      }
#endif
      Node mv = getModelValue( pv );
      Node pv_coeff_m;
      Trace("cbqi-inst-debug") << "[5] " << i << "...try model value " << mv << std::endl;
      int new_effort = use_model_value ? effort : 1;
      if( doAddInstantiationInc( pv, mv, pv_coeff_m, 0, sf, new_effort ) ){
        return true;
      }
    }
    Trace("cbqi-inst-debug") << "[No instantiation found for " << pv << "]" << std::endl;
    if( is_cv ){  
      d_stack_vars.push_back( pv );
    }
    d_active_instantiators.erase( pv );
    unregisterInstantiationVariable( pv );
    return false;
  }
}

void CegInstantiator::pushStackVariable( Node v ) {
  d_stack_vars.push_back( v );
}

void CegInstantiator::popStackVariable() {
  Assert( !d_stack_vars.empty() );
  d_stack_vars.pop_back();
}

bool CegInstantiator::doAddInstantiationInc( Node pv, Node n, Node pv_coeff, int bt, SolvedForm& sf, unsigned effort ) {
  if( d_curr_subs_proc[pv][n].find( pv_coeff )==d_curr_subs_proc[pv][n].end() ){
    d_curr_subs_proc[pv][n][pv_coeff] = true;
    if( Trace.isOn("cbqi-inst") ){
      for( unsigned j=0; j<sf.d_subs.size(); j++ ){
        Trace("cbqi-inst") << " ";
      }
      Trace("cbqi-inst") << sf.d_subs.size() << ": ";
      if( !pv_coeff.isNull() ){
        Trace("cbqi-inst") << pv_coeff << " * ";
      }
      Trace("cbqi-inst") << pv << " -> " << n << std::endl;
      Assert( n.getType().isSubtypeOf( pv.getType() ) );
    }
    //must ensure variables have been computed for n
    computeProgVars( n );
    Assert( d_inelig.find( n )==d_inelig.end() );

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
    std::map< int, Node > prev_sym_subs;
    std::vector< Node > new_has_coeff;
    Trace("cbqi-inst-debug2") << "Applying substitutions..." << std::endl;
    for( unsigned j=0; j<sf.d_subs.size(); j++ ){
      Trace("cbqi-inst-debug2") << "  Apply for " << sf.d_subs[j]  << std::endl;
      Assert( d_prog_var.find( sf.d_subs[j] )!=d_prog_var.end() );
      if( d_prog_var[sf.d_subs[j]].find( pv )!=d_prog_var[sf.d_subs[j]].end() ){
        prev_subs[j] = sf.d_subs[j];
        TNode tv = pv;
        TNode ts = n;
        Node a_pv_coeff;
        Node new_subs = applySubstitution( sf.d_vars[j].getType(), sf.d_subs[j], a_subs, a_coeff, a_has_coeff, a_var, a_pv_coeff, true );
        if( !new_subs.isNull() ){
          sf.d_subs[j] = new_subs;
          if( !a_pv_coeff.isNull() ){
            prev_coeff[j] = sf.d_coeff[j];
            if( sf.d_coeff[j].isNull() ){
              Assert( std::find( sf.d_has_coeff.begin(), sf.d_has_coeff.end(), sf.d_vars[j] )==sf.d_has_coeff.end() );
              //now has coefficient
              new_has_coeff.push_back( sf.d_vars[j] );
              sf.d_has_coeff.push_back( sf.d_vars[j] );
              sf.d_coeff[j] = a_pv_coeff;
            }else{
              sf.d_coeff[j] = Rewriter::rewrite( NodeManager::currentNM()->mkNode( MULT, sf.d_coeff[j], a_pv_coeff ) );
            }
          }
          if( sf.d_subs[j]!=prev_subs[j] ){
            computeProgVars( sf.d_subs[j] );
            Assert( d_inelig.find( sf.d_subs[j] )==d_inelig.end() );
          }
          Trace("cbqi-inst-debug2") << "Subs " << j << " " << sf.d_subs[j] << std::endl;
        }else{
          Trace("cbqi-inst-debug2") << "...failed to apply substitution to " << sf.d_subs[j] << std::endl;
          success = false;
          break;
        }
      }else{
        Trace("cbqi-inst-debug2") << "Skip " << j << " " << sf.d_subs[j] << std::endl;
      }
    }
    if( success ){
      Trace("cbqi-inst-debug2") << "Adding to vectors..." << std::endl;
      sf.push_back( pv, n, pv_coeff, bt );
      Node prev_theta = sf.d_theta;
      Node new_theta = sf.d_theta;
      if( !pv_coeff.isNull() ){
        if( new_theta.isNull() ){
          new_theta = pv_coeff;
        }else{
          new_theta = NodeManager::currentNM()->mkNode( MULT, new_theta, pv_coeff );
          new_theta = Rewriter::rewrite( new_theta );
        }
      }
      sf.d_theta = new_theta;
      Trace("cbqi-inst-debug2") << "Recurse..." << std::endl;
      unsigned i = d_curr_index[pv];
      success = doAddInstantiation( sf, d_stack_vars.empty() ? i+1 : i, effort );
      sf.d_theta = prev_theta;
      if( !success ){
        Trace("cbqi-inst-debug2") << "Removing from vectors..." << std::endl;
        sf.pop_back( pv, n, pv_coeff, bt );
      }
    }
    if( success ){
      return true;
    }else{
      Trace("cbqi-inst-debug2") << "Revert substitutions..." << std::endl;
      //revert substitution information
      for( std::map< int, Node >::iterator it = prev_subs.begin(); it != prev_subs.end(); it++ ){
        sf.d_subs[it->first] = it->second;
      }
      for( std::map< int, Node >::iterator it = prev_coeff.begin(); it != prev_coeff.end(); it++ ){
        sf.d_coeff[it->first] = it->second;
      }
      for( unsigned i=0; i<new_has_coeff.size(); i++ ){
        sf.d_has_coeff.pop_back();
      }
      return false;
    }
  }else{
    //already tried this substitution
    return false;
  }
}

bool CegInstantiator::doAddInstantiation( std::vector< Node >& subs, std::vector< Node >& vars ) {
  if( vars.size()>d_vars.size() ){
    Trace("cbqi-inst-debug") << "Reconstructing instantiations...." << std::endl;
    std::map< Node, Node > subs_map;
    for( unsigned i=0; i<subs.size(); i++ ){
      subs_map[vars[i]] = subs[i];
    }
    subs.clear();
    for( unsigned i=0; i<d_vars.size(); i++ ){
      std::map< Node, Node >::iterator it = subs_map.find( d_vars[i] );
      Assert( it!=subs_map.end() );
      Node n = it->second;
      Trace("cbqi-inst-debug") << "  " << d_vars[i] << " -> " << n << std::endl;
      subs.push_back( n );
    }
  }
  if( !d_var_order_index.empty() ){
    std::vector< Node > subs_orig;
    subs_orig.insert( subs_orig.end(), subs.begin(), subs.end() );
    subs.clear();
    for( unsigned i=0; i<subs_orig.size(); i++ ){
      subs.push_back( subs_orig[d_var_order_index[i]] );
    }
  }
  bool ret = d_out->doAddInstantiation( subs );
  return ret;
}

Node CegInstantiator::applySubstitution( TypeNode tn, Node n, std::vector< Node >& subs, std::vector< Node >& coeff, std::vector< Node >& has_coeff,
                                         std::vector< Node >& vars, Node& pv_coeff, bool try_coeff ) {
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
    return nret;
  }else{
    if( !tn.isInteger() ){
      //can do basic substitution instead with divisions
      std::vector< Node > nvars;
      std::vector< Node > nsubs;
      for( unsigned i=0; i<vars.size(); i++ ){
        if( !coeff[i].isNull() ){
          Assert( coeff[i].isConst() );
          nsubs.push_back( Rewriter::rewrite( NodeManager::currentNM()->mkNode( MULT, subs[i], NodeManager::currentNM()->mkConst( Rational(1)/coeff[i].getConst<Rational>() ) ) ));
        }else{
          nsubs.push_back( subs[i] );
        }
      }
      Node nret = n.substitute( vars.begin(), vars.end(), nsubs.begin(), nsubs.end() );
      if( n!=nret ){
        nret = Rewriter::rewrite( nret );
      }
      return nret;
    }else if( try_coeff ){
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
          Assert( !c_coeff.isNull() );
          Node c;
          if( msum_term[it->first].isNull() ){
            c = c_coeff;
          }else{
            c = NodeManager::currentNM()->mkNode( MULT, c_coeff, msum_term[it->first] );
          }
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

bool CegInstantiator::check() {
  if( d_qe->getTheoryEngine()->needCheck() ){
    Trace("cbqi-engine") << "  CEGQI instantiator : wait until all ground theories are finished." << std::endl;
    return false;
  }
  processAssertions();
  for( unsigned r=0; r<2; r++ ){
    SolvedForm sf;
    d_stack_vars.clear();
    //try to add an instantiation
    if( doAddInstantiation( sf, 0, r==0 ? 0 : 2 ) ){
      return true;
    }
  }
  Trace("cbqi-engine") << "  WARNING : unable to find CEGQI single invocation instantiation." << std::endl;
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
  //at preregister time, add proxy of obvious instantiations up front, which helps learning during preprocessing
  //only if no nested quantifiers
  if( !QuantifiersRewriter::containsQuantifiers( q[1] ) ){
    std::vector< Node > ps_vars;
    std::map< Node, std::vector< Node > > teq;
    for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
      ps_vars.push_back( q[0][i] );
      teq[q[0][i]].clear();
    }
    collectPresolveEqTerms( q[1], teq );
    std::vector< Node > terms;
    std::vector< Node > conj;
    getPresolveEqConjuncts( ps_vars, terms, teq, q, conj );

    if( !conj.empty() ){
      Node lem = conj.size()==1 ? conj[0] : NodeManager::currentNM()->mkNode( AND, conj );
      Node g = NodeManager::currentNM()->mkSkolem( "g", NodeManager::currentNM()->booleanType() );
      lem = NodeManager::currentNM()->mkNode( OR, g, lem );
      Trace("cbqi-presolve-debug") << "Presolve lemma : " << lem << std::endl;
      d_qe->getOutputChannel().lemma( lem, false, true );
    }
  }
}

void collectTheoryIds( TypeNode tn, std::map< TypeNode, bool >& visited, std::vector< TheoryId >& tids ){
  std::map< TypeNode, bool >::iterator itt = visited.find( tn );
  if( itt==visited.end() ){
    visited[tn] = true;
    TheoryId tid = Theory::theoryOf( tn );
    if( std::find( tids.begin(), tids.end(), tid )==tids.end() ){
      tids.push_back( tid );
    }
    if( tn.isDatatype() ){
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
        for( unsigned j=0; j<dt[i].getNumArgs(); j++ ){
          collectTheoryIds( TypeNode::fromType( ((SelectorType)dt[i][j].getType()).getRangeType() ), visited, tids );
        }
      }
    }
  }
}

void CegInstantiator::processAssertions() {
  Trace("cbqi-proc") << "--- Process assertions, #var = " << d_vars.size() << ", #aux-var = " << d_aux_vars.size() << std::endl;
  d_curr_asserts.clear();
  d_curr_eqc.clear();
  d_curr_type_eqc.clear();

  eq::EqualityEngine* ee = d_qe->getMasterEqualityEngine();
  //to eliminate identified illegal terms
  std::map< Node, Node > aux_subs;

  //for each variable
  std::vector< TheoryId > tids;
  tids.push_back(THEORY_UF);
  for( unsigned i=0; i<d_vars.size(); i++ ){
    Node pv = d_vars[i];
    TypeNode pvtn = pv.getType();
    //collect relevant theories
    std::map< TypeNode, bool > visited;
    collectTheoryIds( pvtn, visited, tids );
    //collect information about eqc
    if( ee->hasTerm( pv ) ){
      Node pvr = ee->getRepresentative( pv );
      if( d_curr_eqc.find( pvr )==d_curr_eqc.end() ){
        Trace("cbqi-proc") << "Collect equivalence class " << pvr << std::endl;
        eq::EqClassIterator eqc_i = eq::EqClassIterator( pvr, ee );
        while( !eqc_i.isFinished() ){
          d_curr_eqc[pvr].push_back( *eqc_i );
          ++eqc_i;
        }
      }
    }
  }
  //collect assertions for relevant theories
  for( unsigned i=0; i<tids.size(); i++ ){
    TheoryId tid = tids[i];
    Theory* theory = d_qe->getTheoryEngine()->theoryOf( tid );
    if( theory && d_qe->getTheoryEngine()->isTheoryEnabled(tid) ){
      Trace("cbqi-proc") << "Collect assertions from theory " << tid << std::endl;
      d_curr_asserts[tid].clear();
      //collect all assertions from theory
      for( context::CDList<Assertion>::const_iterator it = theory->facts_begin(); it != theory->facts_end(); ++ it) {
        Node lit = (*it).assertion;
        Node atom = lit.getKind()==NOT ? lit[0] : lit;
        if( d_is_nested_quant || std::find( d_ce_atoms.begin(), d_ce_atoms.end(), atom )!=d_ce_atoms.end() ){
          d_curr_asserts[tid].push_back( lit );
          Trace("cbqi-proc-debug") << "...add : " << lit << std::endl;
        }else{
          Trace("cbqi-proc") << "...do not consider literal " << tid << " : " << lit << " since it is not part of CE body." << std::endl;
        }
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
  //collect equivalence classes that correspond to relevant theories
  Trace("cbqi-proc-debug") << "...collect typed equivalence classes" << std::endl;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
  while( !eqcs_i.isFinished() ){
    Node r = *eqcs_i;
    TypeNode rtn = r.getType();
    TheoryId tid = Theory::theoryOf( rtn );
    //if we care about the theory of this eqc
    if( std::find( tids.begin(), tids.end(), tid )!=tids.end() ){
      if( rtn.isInteger() || rtn.isReal() ){
        rtn = rtn.getBaseType();
      }
      Trace("cbqi-proc-debug") << "...type eqc: " << r << std::endl;
      d_curr_type_eqc[rtn].push_back( r );
      if( d_curr_eqc.find( r )==d_curr_eqc.end() ){
        Trace("cbqi-proc") << "Collect equivalence class " << r << std::endl;
        Trace("cbqi-proc-debug") << "  ";
        eq::EqClassIterator eqc_i = eq::EqClassIterator( r, ee );
        while( !eqc_i.isFinished() ){
          Trace("cbqi-proc-debug") << *eqc_i << " ";
          d_curr_eqc[r].push_back( *eqc_i );
          ++eqc_i;
        }
        Trace("cbqi-proc-debug") << std::endl;
      }
    }
    ++eqcs_i;
  }
  //construct substitution from auxiliary variable equalities (if e.g. ITE removal was applied to CE body of quantified formula)
  std::vector< Node > subs_lhs;
  std::vector< Node > subs_rhs;
  for( unsigned i=0; i<d_aux_vars.size(); i++ ){
    Node r = d_aux_vars[i];
    std::map< Node, Node >::iterator it = aux_subs.find( r );
    if( it!=aux_subs.end() ){
      addToAuxVarSubstitution( subs_lhs, subs_rhs, r, it->second );
    }else{
      Trace("cbqi-proc") << "....no substitution found for auxiliary variable " << r << "!!!" << std::endl;
      Assert( false );
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
      //must be an eligible term
      if( isEligible( n ) ){
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

Node CegInstantiator::getModelValue( Node n ) {
  return d_qe->getModel()->getValue( n );
}

void CegInstantiator::collectCeAtoms( Node n, std::map< Node, bool >& visited ) {
  if( n.getKind()==FORALL ){
    d_is_nested_quant = true;
  }else if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( TermDb::isBoolConnective( n.getKind() ) ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        collectCeAtoms( n[i], visited );
      }
    }else{
      if( std::find( d_ce_atoms.begin(), d_ce_atoms.end(), n )==d_ce_atoms.end() ){
        Trace("cbqi-ce-atoms") << "CE atoms : " << n << std::endl;
        d_ce_atoms.push_back( n );
      }
    }
  }
}

struct sortCegVarOrder {
  bool operator() (Node i, Node j) {
    TypeNode it = i.getType();
    TypeNode jt = j.getType();
    return ( it!=jt && jt.isSubtypeOf( it ) ) || ( it==jt && i<j );
  }
};


void CegInstantiator::registerCounterexampleLemma( std::vector< Node >& lems, std::vector< Node >& ce_vars ) {
  //Assert( d_vars.empty() );
  d_vars.clear();
  d_vars.insert( d_vars.end(), ce_vars.begin(), ce_vars.end() );

  //determine variable order: must do Reals before Ints
  if( !d_vars.empty() ){
    TypeNode tn0 = d_vars[0].getType();
    bool doSort = false;
    std::map< Node, unsigned > voo;
    for( unsigned i=0; i<d_vars.size(); i++ ){
      voo[d_vars[i]] = i;
      d_var_order_index.push_back( 0 );
      if( d_vars[i].getType()!=tn0 ){
        doSort = true;
      }
    }
    if( doSort ){
      Trace("cbqi-debug") << "Sort variables based on ordering." << std::endl;
      sortCegVarOrder scvo;
      std::sort( d_vars.begin(), d_vars.end(), scvo );
      Trace("cbqi-debug") << "Consider variables in this order : " << std::endl;
      for( unsigned i=0; i<d_vars.size(); i++ ){
        d_var_order_index[voo[d_vars[i]]] = i;
        Trace("cbqi-debug") << "  " << d_vars[i] << " : " << d_vars[i].getType() << ", index was : " << voo[d_vars[i]] << std::endl;
      }
      Trace("cbqi-debug") << std::endl;
    }else{
      d_var_order_index.clear();
    }
  }

  //remove ITEs
  IteSkolemMap iteSkolemMap;
  d_qe->getTheoryEngine()->getIteRemover()->run(lems, iteSkolemMap);
  //Assert( d_aux_vars.empty() );
  d_aux_vars.clear();
  d_aux_eq.clear();
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
  //collect atoms from all lemmas: we will only do bounds coming from original body
  d_is_nested_quant = false;
  std::map< Node, bool > visited;
  for( unsigned i=0; i<lems.size(); i++ ){
    collectCeAtoms( lems[i], visited );
  }
}


Instantiator::Instantiator( QuantifiersEngine * qe, TypeNode tn ) : d_type( tn ){
  d_closed_enum_type = qe->getTermDatabase()->isClosedEnumerableType( tn );
}


bool Instantiator::processEqualTerm( CegInstantiator * ci, SolvedForm& sf, Node pv, Node pv_coeff, Node n, unsigned effort ) {
  return ci->doAddInstantiationInc( pv, n, pv_coeff, 0, sf, effort );
}


