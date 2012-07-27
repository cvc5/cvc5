/*********************                                                        */
/*! \file relevant_domain.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of relevant domain class
 **/

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/first_order_model.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

RelevantDomain::RelevantDomain( FirstOrderModel* m ) : d_model( m ){

}

void RelevantDomain::compute(){
  d_quant_inst_domain.clear();
  for( int i=0; i<(int)d_model->getNumAssertedQuantifiers(); i++ ){
    Node f = d_model->getAssertedQuantifier( i );
    d_quant_inst_domain[f].resize( f[0].getNumChildren() );
  }
  //add ground terms to domain (rule 1 of complete instantiation essentially uf fragment)
  for( std::map< Node, uf::UfModelTree >::iterator it = d_model->d_uf_model_tree.begin();
       it != d_model->d_uf_model_tree.end(); ++it ){
    Node op = it->first;
    for( size_t i=0; i<d_model->d_uf_terms[op].size(); i++ ){
      Node n = d_model->d_uf_terms[op][i];
      //add arguments to domain
      for( int j=0; j<(int)n.getNumChildren(); j++ ){
        if( d_model->d_rep_set.hasType( n[j].getType() ) ){
          Node ra = d_model->getRepresentative( n[j] );
          int raIndex = d_model->d_rep_set.getIndexFor( ra );
          Assert( raIndex!=-1 );
          if( std::find( d_active_domain[op][j].begin(), d_active_domain[op][j].end(), raIndex )==d_active_domain[op][j].end() ){
            d_active_domain[op][j].push_back( raIndex );
          }
        }
      }
      //add to range
      Node r = d_model->getRepresentative( n );
      int raIndex = d_model->d_rep_set.getIndexFor( r );
      Assert( raIndex!=-1 );
      if( std::find( d_active_range[op].begin(), d_active_range[op].end(), raIndex )==d_active_range[op].end() ){
        d_active_range[op].push_back( raIndex );
      }
    }
  }
  //find fixed point for relevant domain computation
  bool success;
  do{
    success = true;
    for( int i=0; i<(int)d_model->getNumAssertedQuantifiers(); i++ ){
      Node f = d_model->getAssertedQuantifier( i );
      //compute the domain of relevant instantiations (rule 3 of complete instantiation, essentially uf fragment)
      if( computeRelevantInstantiationDomain( d_model->getTermDatabase()->getCounterexampleBody( f ), Node::null(), -1, d_quant_inst_domain[f] ) ){
        success = false;
      }
      //extend the possible domain for functions (rule 2 of complete instantiation, essentially uf fragment)
      RepDomain range;
      if( extendFunctionDomains( d_model->getTermDatabase()->getCounterexampleBody( f ), range ) ){
        success = false;
      }
    }
  }while( !success );
}

bool RelevantDomain::computeRelevantInstantiationDomain( Node n, Node parent, int arg, std::vector< RepDomain >& rd ){
  bool domainChanged = false;
  if( n.getKind()==INST_CONSTANT ){
    bool domainSet = false;
    int vi = n.getAttribute(InstVarNumAttribute());
    Assert( !parent.isNull() );
    if( parent.getKind()==APPLY_UF ){
      //if the child of APPLY_UF term f( ... ), only consider the active domain of f at given argument
      Node op = parent.getOperator();
      if( d_active_domain.find( op )!=d_active_domain.end() ){
        for( size_t i=0; i<d_active_domain[op][arg].size(); i++ ){
          int d = d_active_domain[op][arg][i];
          if( std::find( rd[vi].begin(), rd[vi].end(), d )==rd[vi].end() ){
            rd[vi].push_back( d );
            domainChanged = true;
          }
        }
        domainSet = true;
      }
    }
    if( !domainSet ){
      //otherwise, we must consider the entire domain
      TypeNode tn = n.getType();
      if( d_model->d_rep_set.hasType( tn ) ){
        if( rd[vi].size()!=d_model->d_rep_set.d_type_reps[tn].size() ){
          rd[vi].clear();
          for( size_t i=0; i<d_model->d_rep_set.d_type_reps[tn].size(); i++ ){
            rd[vi].push_back( i );
            domainChanged = true;
          }
        }
      }else{
        //infinite domain?
      }
    }
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( computeRelevantInstantiationDomain( n[i], n, i, rd ) ){
        domainChanged = true;
      }
    }
  }
  return domainChanged;
}

bool RelevantDomain::extendFunctionDomains( Node n, RepDomain& range ){
  if( n.getKind()==INST_CONSTANT ){
    Node f = n.getAttribute(InstConstantAttribute());
    int var = n.getAttribute(InstVarNumAttribute());
    range.insert( range.begin(), d_quant_inst_domain[f][var].begin(), d_quant_inst_domain[f][var].end() );
    return false;
  }else{
    Node op;
    if( n.getKind()==APPLY_UF ){
      op = n.getOperator();
    }
    bool domainChanged = false;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      RepDomain childRange;
      if( extendFunctionDomains( n[i], childRange ) ){
        domainChanged = true;
      }
      if( n.getKind()==APPLY_UF ){
        if( d_active_domain.find( op )!=d_active_domain.end() ){
          for( int j=0; j<(int)childRange.size(); j++ ){
            int v = childRange[j];
            if( std::find( d_active_domain[op][i].begin(), d_active_domain[op][i].end(), v )==d_active_domain[op][i].end() ){
              d_active_domain[op][i].push_back( v );
              domainChanged = true;
            }
          }
        }else{
          //do this?
        }
      }
    }
    //get the range
    if( n.hasAttribute(InstConstantAttribute()) ){
      if( n.getKind()==APPLY_UF && d_active_range.find( op )!=d_active_range.end() ){
        range.insert( range.end(), d_active_range[op].begin(), d_active_range[op].end() );
      }else{
        //infinite range?
      }
    }else{
      Node r = d_model->getRepresentative( n );
      range.push_back( d_model->d_rep_set.getIndexFor( r ) );
    }
    return domainChanged;
  }
}