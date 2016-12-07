/*********************                                                        */
/*! \file quant_split.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of dynamic quantifiers splitting
 **/

#include "theory/quantifiers/quant_split.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/first_order_model.h"
#include "options/quantifiers_options.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;


QuantDSplit::QuantDSplit( QuantifiersEngine * qe, context::Context* c ) :
QuantifiersModule( qe ), d_added_split( qe->getUserContext() ){

}

/** pre register quantifier */
void QuantDSplit::preRegisterQuantifier( Node q ) {
  int max_index = -1;
  int max_score = -1;
  if( q.getNumChildren()==3 ){
    return;
  }
  Trace("quant-dsplit-debug") << "Check split quantified formula : " << q << std::endl;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    TypeNode tn = q[0][i].getType();
    if( tn.isDatatype() ){
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      if( dt.isRecursiveSingleton( tn.toType() ) ){
        Trace("quant-dsplit-debug") << "Datatype " << dt.getName() << " is recursive singleton." << std::endl;
      }else{
        int score = -1;
        if( options::quantDynamicSplit()==quantifiers::QUANT_DSPLIT_MODE_AGG ){
          score = dt.isInterpretedFinite( tn.toType() ) ? 1 : 0;
        }else if( options::quantDynamicSplit()==quantifiers::QUANT_DSPLIT_MODE_DEFAULT ){
          //only split if goes from being unhandled -> handled by finite instantiation
          //  an example is datatypes with uninterpreted sort fields, which are "interpreted finite" but not "finite"
          if( !d_quantEngine->isFiniteBound( q, q[0][i] ) ){
            score = dt.isInterpretedFinite( tn.toType() ) ? 1 : -1;
          }
        }
        Trace("quant-dsplit-debug") << "Datatype " << dt.getName() << " is score " << score << " (" << dt.isInterpretedFinite( tn.toType() ) << " " << dt.isFinite( tn.toType() ) << ")" << std::endl;
        if( score>max_score ){
          max_index = i;
          max_score = score;
        }
      }
    }
  }

  if( max_index!=-1 ){
    Trace("quant-dsplit-debug") << "Will split at index " << max_index << "." << std::endl;
    d_quant_to_reduce[q] = max_index;
    d_quantEngine->setOwner( q, this );
  }
}

/* whether this module needs to check this round */
bool QuantDSplit::needsCheck( Theory::Effort e ) {
  return e>=Theory::EFFORT_FULL && !d_quant_to_reduce.empty();
}

bool QuantDSplit::checkCompleteFor( Node q ) {
  // true if we split q
  return d_added_split.find( q )!=d_added_split.end();
}

/* Call during quantifier engine's check */
void QuantDSplit::check( Theory::Effort e, unsigned quant_e ) {
  //add lemmas ASAP (they are a reduction)
  if( quant_e==QuantifiersEngine::QEFFORT_CONFLICT ){
    std::vector< Node > lemmas;
    for(std::map< Node, int >::iterator it = d_quant_to_reduce.begin(); it != d_quant_to_reduce.end(); ++it) {
      Node q = it->first;
      if( d_quantEngine->getModel()->isQuantifierActive( q ) ){
        if( d_added_split.find( q )==d_added_split.end() ){
          d_added_split.insert( q );
          std::vector< Node > bvs;
          for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
            if( (int)i!=it->second ){
              bvs.push_back( q[0][i] );
            }
          }
          std::vector< Node > disj;
          disj.push_back( q.negate() );
          TNode svar = q[0][it->second];
          TypeNode tn = svar.getType();
          if( tn.isDatatype() ){
            std::vector< Node > cons;
            const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
            for( unsigned j=0; j<dt.getNumConstructors(); j++ ){
              std::vector< Node > vars;
              for( unsigned k=0; k<dt[j].getNumArgs(); k++ ){
                TypeNode tns = TypeNode::fromType( dt[j][k].getRangeType() );
                Node v = NodeManager::currentNM()->mkBoundVar( tns );
                vars.push_back( v );
              }
              std::vector< Node > bvs_cmb;
              bvs_cmb.insert( bvs_cmb.end(), bvs.begin(), bvs.end() );
              bvs_cmb.insert( bvs_cmb.end(), vars.begin(), vars.end() );
              vars.insert( vars.begin(), Node::fromExpr( dt[j].getConstructor() ) );
              Node c = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, vars );
              TNode ct = c;
              Node body = q[1].substitute( svar, ct );
              if( !bvs_cmb.empty() ){
                body = NodeManager::currentNM()->mkNode( kind::FORALL, NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, bvs_cmb ), body );
              }
              cons.push_back( body );
            }
            Node conc = cons.size()==1 ? cons[0] : NodeManager::currentNM()->mkNode( kind::AND, cons );
            disj.push_back( conc );
          }else{
            Assert( false );
          }
          lemmas.push_back( disj.size()==1 ? disj[0] : NodeManager::currentNM()->mkNode( kind::OR, disj ) );
        }
      }
    }

    //add lemmas to quantifiers engine
    for( unsigned i=0; i<lemmas.size(); i++ ){
      Trace("quant-dsplit") << "QuantDSplit lemma : " << lemmas[i] << std::endl;
      d_quantEngine->addLemma( lemmas[i], false );
    }
    //d_quant_to_reduce.clear();
  }
}

