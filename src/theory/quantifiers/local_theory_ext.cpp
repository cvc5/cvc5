/*********************                                                        */
/*! \file local_theory_ext.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of local theory ext utilities
 **/

#include "theory/quantifiers/local_theory_ext.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/first_order_model.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;


LtePartialInst::LtePartialInst( QuantifiersEngine * qe, context::Context* c ) : 
QuantifiersModule( qe ), d_wasInvoked( false ), d_needsCheck( false ){

}

/** add quantifier */
void LtePartialInst::preRegisterQuantifier( Node q ) {
  if( !q.getAttribute(LtePartialInstAttribute()) ){
    if( d_do_inst.find( q )!=d_do_inst.end() ){
      if( d_do_inst[q] ){
        d_lte_asserts.push_back( q );
        d_quantEngine->setOwner( q, this );
      }
    }else{
      d_vars[q].clear();
      d_pat_var_order[q].clear();
      //check if this quantified formula is eligible for partial instantiation
      std::map< Node, bool > vars;
      for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
        vars[q[0][i]] = false;
      }
      getEligibleInstVars( q[1], vars );

      //instantiate only if we would force ground instances
      std::map< Node, int > var_order;
      bool doInst = true;
      for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
        if( vars[q[0][i]] ){
          d_vars[q].push_back( q[0][i] );
          var_order[q[0][i]] = i;
        }else{
          Trace("lte-partial-inst-debug") << "...do not consider, variable " << q[0][i] << " was not found in correct position in body." << std::endl;
          doInst = false;
          break;
        }
      }
      if( doInst ){
        //also needs patterns
        if( q.getNumChildren()==3 && q[2].getNumChildren()==1 ){
          for( unsigned i=0; i<q[2][0].getNumChildren(); i++ ){
            Node pat = q[2][0][i];
            if( pat.getKind()==APPLY_UF ){
              for( unsigned j=0; j<pat.getNumChildren(); j++ ){
                if( !addVariableToPatternList( pat[j], d_pat_var_order[q], var_order ) ){
                  doInst = false;
                }
              }
            }else if( !addVariableToPatternList( pat, d_pat_var_order[q], var_order ) ){
              doInst = false;
            }
            if( !doInst ){
              Trace("lte-partial-inst-debug") << "...do not consider, cannot resolve pattern : " << pat << std::endl;
              break;
            }
          }
        }else{
          Trace("lte-partial-inst-debug") << "...do not consider (must have exactly one pattern)." << std::endl;
        }
      }
      
      
      Trace("lte-partial-inst") << "LTE: ...will " << ( doInst ? "" : "not ") << "instantiate " << q << std::endl;
      d_do_inst[q] = doInst;
      if( doInst ){
        d_lte_asserts.push_back( q );
        d_needsCheck = true;
        d_quantEngine->setOwner( q, this );
      }
    }
  }
}

bool LtePartialInst::addVariableToPatternList( Node v, std::vector< int >& pat_var_order, std::map< Node, int >& var_order ) {
  std::map< Node, int >::iterator it = var_order.find( v );
  if( it==var_order.end() ){
    return false;
  }else if( std::find( pat_var_order.begin(), pat_var_order.end(), it->second )!=pat_var_order.end() ){
    return false;
  }else{
    pat_var_order.push_back( it->second );
    return true;
  }
}

void LtePartialInst::getEligibleInstVars( Node n, std::map< Node, bool >& vars ) {
  if( n.getKind()==APPLY_UF && !n.getType().isBoolean() ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( vars.find( n[i] )!=vars.end() ){
        vars[n[i]] = true;
      }
    }
  }
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    getEligibleInstVars( n[i], vars );
  }
}

/* whether this module needs to check this round */
bool LtePartialInst::needsCheck( Theory::Effort e ) {
  return e>=Theory::EFFORT_FULL && d_needsCheck;
}
/* Call during quantifier engine's check */
void LtePartialInst::check( Theory::Effort e, unsigned quant_e ) {
  //flush lemmas ASAP (they are a reduction)
  if( quant_e==QuantifiersEngine::QEFFORT_CONFLICT && d_needsCheck ){
    std::vector< Node > lemmas;
    getInstantiations( lemmas );
    //add lemmas to quantifiers engine
    for( unsigned i=0; i<lemmas.size(); i++ ){
      d_quantEngine->addLemma( lemmas[i], false );
    }
    d_needsCheck = false;
  }
}


void LtePartialInst::reset() {
  d_reps.clear();
  eq::EqualityEngine* ee = d_quantEngine->getActiveEqualityEngine();
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
  while( !eqcs_i.isFinished() ){
    TNode r = (*eqcs_i);
    TypeNode tn = r.getType();
    d_reps[tn].push_back( r );
    ++eqcs_i;
  }
}


/** get instantiations */
void LtePartialInst::getInstantiations( std::vector< Node >& lemmas ) {
  Trace("lte-partial-inst") << "LTE : get instantiations, # quant = " << d_lte_asserts.size() << std::endl;
  reset();
  for( unsigned i=0; i<d_lte_asserts.size(); i++ ){
    Node q = d_lte_asserts[i];
    Assert( d_do_inst.find( q )!=d_do_inst.end() && d_do_inst[q] );
    if( d_inst.find( q )==d_inst.end() ){
      Trace("lte-partial-inst") << "LTE : Get partial instantiations for " << q << "..." << std::endl;
      d_inst[q] = true;
      Assert( !d_vars[q].empty() );
      //make bound list
      Node bvl;
      std::vector< Node > bvs;
      for( unsigned j=0; j<q[0].getNumChildren(); j++ ){
        if( std::find( d_vars[q].begin(), d_vars[q].end(), q[0][j] )==d_vars[q].end() ){
          bvs.push_back( q[0][j] );
        }
      }
      if( !bvs.empty() ){
        bvl = NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, bvs );
      }
      std::vector< Node > conj;
      std::vector< Node > terms;
      std::vector< TypeNode > types;
      for( unsigned j=0; j<d_vars[q].size(); j++ ){
        types.push_back( d_vars[q][j].getType() );
        terms.push_back( Node::null() );
      }

      getPartialInstantiations( conj, q, bvl, d_vars[q], terms, types, NULL, 0, 0, 0 );
      Assert( !conj.empty() );
      lemmas.push_back( NodeManager::currentNM()->mkNode( OR, q.negate(), conj.size()==1 ? conj[0] : NodeManager::currentNM()->mkNode( AND, conj ) ) );
      d_wasInvoked = true;
    }
  }
}

void LtePartialInst::getPartialInstantiations( std::vector< Node >& conj, Node q, Node bvl,
                                               std::vector< Node >& vars, std::vector< Node >& terms, std::vector< TypeNode >& types, TermArgTrie * curr,
                                               unsigned pindex, unsigned paindex, unsigned iindex ){
  if( iindex==vars.size() ){
    Node body = q[1].substitute( vars.begin(), vars.end(), terms.begin(), terms.end() );
    if( bvl.isNull() ){
      conj.push_back( body );
      Trace("lte-partial-inst") << " - ground conjunct : " << body << std::endl;
    }else{
      Node nq;
      if( q.getNumChildren()==3 ){
        Node ipl = q[2].substitute( vars.begin(), vars.end(), terms.begin(), terms.end() );
        nq = NodeManager::currentNM()->mkNode( FORALL, bvl, body, ipl );
      }else{
        nq = NodeManager::currentNM()->mkNode( FORALL, bvl, body );
      }
      Trace("lte-partial-inst") << " - quantified conjunct : " << nq << std::endl;
      LtePartialInstAttribute ltpia;
      nq.setAttribute(ltpia,true);
      conj.push_back( nq );
    }
  }else{
    Assert( pindex<q[2][0].getNumChildren() );
    Node pat = q[2][0][pindex];
    Assert( pat.getNumChildren()==0 || paindex<=pat.getNumChildren() );
    if( pat.getKind()==APPLY_UF ){
      Assert( paindex<=pat.getNumChildren() );
      if( paindex==pat.getNumChildren() ){
        getPartialInstantiations( conj, q, bvl, vars, terms, types, NULL, pindex+1, 0, iindex );
      }else{
        if( !curr ){
          Assert( paindex==0 );
          //start traversing term index for the operator
          curr = d_quantEngine->getTermDatabase()->getTermArgTrie( pat.getOperator() );
        }
        for( std::map< TNode, TermArgTrie >::iterator it = curr->d_data.begin(); it != curr->d_data.end(); ++it ){
          terms[d_pat_var_order[q][iindex]] = it->first;
          getPartialInstantiations( conj, q, bvl, vars, terms, types, &it->second, pindex, paindex+1, iindex+1 );
        }
      }
    }else{
      std::map< TypeNode, std::vector< Node > >::iterator it = d_reps.find( types[iindex] );
      if( it!=d_reps.end() ){
        Trace("lte-partial-inst-debug") << it->second.size() << " reps of type " << types[iindex] << std::endl;
        for( unsigned i=0; i<it->second.size(); i++ ){
          terms[d_pat_var_order[q][iindex]] = it->second[i];
          getPartialInstantiations( conj, q, bvl, vars, terms, types, NULL, pindex+1, 0, iindex+1 );
        }
      }else{
        Trace("lte-partial-inst-debug") << "No reps found of type " << types[iindex] << std::endl;
      }
    }
  }
}
