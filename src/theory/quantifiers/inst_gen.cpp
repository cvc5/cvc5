/*********************                                                        */
/*! \file inst_gen.cpp
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
 ** \brief Implementation of inst gen classes
 **/

#include "theory/quantifiers/inst_gen.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/model_builder.h"
#include "theory/quantifiers/first_order_model.h"

#define RECONSIDER_FUNC_CONSTANT

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;



InstGenProcess::InstGenProcess( Node n ) : d_node( n ){
  Assert( n.hasAttribute(InstConstantAttribute()) );
  int count = 0;
  for( size_t i=0; i<n.getNumChildren(); i++ ){
    if( n[i].getKind()!=INST_CONSTANT && n[i].hasAttribute(InstConstantAttribute()) ){
      d_children.push_back( InstGenProcess( n[i] ) );
      d_children_index.push_back( i );
      d_children_map[ i ] = count;
      count++;
    }
  }
}

void InstGenProcess::addMatchValue( QuantifiersEngine* qe, Node f, Node val, InstMatch& m ){
  if( !qe->existsInstantiation( f, m, true ) ){
    //if( d_inst_trie[val].addInstMatch( qe, f, m, true ) ){
      d_match_values.push_back( val );
      d_matches.push_back( InstMatch( &m ) );
    //}
  }
}

void InstGenProcess::calculateMatches( QuantifiersEngine* qe, Node f ){
  //calculate all matches for children
  for( int i=0; i<(int)d_children.size(); i++ ){
    d_children[i].calculateMatches( qe, f );
    if( d_children[i].getNumMatches()==0 ){
      return;
    }
  }
  Trace("cm") << "calculate matches " << d_node << std::endl;
  //get the model
  FirstOrderModel* fm = qe->getModel();
  if( d_node.getKind()==APPLY_UF ){
    //if this is an uninterpreted function
    Node op = d_node.getOperator();
    //process all values
    for( size_t i=0; i<fm->d_uf_terms[op].size(); i++ ){
      Node n = fm->d_uf_terms[op][i];
      bool isSelected = qe->getModelEngine()->getModelBuilder()->isTermSelected( n );
      for( int t=(isSelected ? 0 : 1); t<2; t++ ){
        //do not consider ground case if it is already congruent to another ground term
        if( t==0 || !n.getAttribute(NoMatchAttribute()) ){
          Trace("cm") << "calculate for " << n << ", selected = " << (t==0) << std::endl;
          bool success = true;
          InstMatch curr;
          for( size_t j=0; j<d_node.getNumChildren(); j++ ){
            if( d_children_map.find( j )==d_children_map.end() ){
              if( t!=0 || !n[j].getAttribute(ModelBasisAttribute()) ){
                if( d_node[j].getKind()==INST_CONSTANT ){
                  //FIXME: is this correct?
                  if( !curr.setMatch( qe->getEqualityQuery(), d_node[j], n[j] ) ){
                    Trace("cm") << "fail match: " << n[j] << " is not equal to " << curr.get( d_node[j] ) << std::endl;
                    Trace("cm") << "  are equal : " << qe->getEqualityQuery()->areEqual( n[j], curr.get( d_node[j] ) ) << std::endl;
                    success = false;
                    break;
                  }
                }else if( !qe->getEqualityQuery()->areEqual( d_node[j], n[j] ) ){
                  Trace("cm") << "fail arg: " << n[j] << " is not equal to " << d_node[j] << std::endl;
                  success = false;
                  break;
                }
              }
            }
          }
          if( success ){
            //try to find unifier for d_node = n
            calculateMatchesUninterpreted( qe, f, curr, n, 0, t==0 );
          }
        }
      }
    }

  }else{
    InstMatch curr;
    //if this is an interpreted function
    std::vector< Node > terms;
    calculateMatchesInterpreted( qe, f, curr, terms, 0 );
  }
  Trace("cm") << "done calculate matches" << std::endl;
}

bool InstGenProcess::getMatch( EqualityQuery* q, int i, InstMatch& m ){
  //FIXME: is this correct? (query may not be accurate)
  return m.merge( q, d_matches[i] );
}

void InstGenProcess::calculateMatchesUninterpreted( QuantifiersEngine* qe, Node f, InstMatch& curr, Node n, int childIndex, bool isSelected ){
  if( childIndex==(int)d_children.size() ){
    Node val = qe->getModel()->getRepresentative( n );  //FIXME: is this correct?
    Trace("cm") << "  - u-match : " << val << std::endl;
    Trace("cm") << "            : " << curr << std::endl;
    addMatchValue( qe, f, val, curr );
  }else{
    Trace("cm") << "Consider child index = " << childIndex << ", against ground term argument " << d_children_index[childIndex] << " ... " << n[d_children_index[childIndex]] << std::endl;
    bool sel = ( isSelected && n[d_children_index[childIndex]].getAttribute(ModelBasisAttribute()) );
    for( int i=0; i<(int)d_children[ childIndex ].getNumMatches(); i++ ){
      //FIXME: is this correct?
      if( sel || qe->getEqualityQuery()->areEqual( d_children[ childIndex ].getMatchValue( i ), n[d_children_index[childIndex]] ) ){
        InstMatch next( &curr );
        if( d_children[ childIndex ].getMatch( qe->getEqualityQuery(), i, next ) ){
          calculateMatchesUninterpreted( qe, f, next, n, childIndex+1, isSelected );
        }else{
          Trace("cm") << curr << " not equal to " << d_children[ childIndex ].d_matches[i] << std::endl;
          Trace("cm") << childIndex << " match " << i << " not equal subs." << std::endl;
        }
      }else{
        Trace("cm") << childIndex << " match " << i << " not equal value." << std::endl;
      }
    }
  }
}

void InstGenProcess::calculateMatchesInterpreted( QuantifiersEngine* qe, Node f, InstMatch& curr, std::vector< Node >& terms, int argIndex ){
  FirstOrderModel* fm = qe->getModel();
  if( argIndex==(int)d_node.getNumChildren() ){
    Node val;
    if( d_node.getNumChildren()==0 ){
      val = d_node;
    }else if( d_node.getKind()==EQUAL ){
      val = qe->getEqualityQuery()->areEqual( terms[0], terms[1] ) ? fm->d_true : fm->d_false;
    }else{
      val = NodeManager::currentNM()->mkNode( d_node.getKind(), terms );
      val = Rewriter::rewrite( val );
    }
    Trace("cm") << "  - i-match : " << val << std::endl;
    Trace("cm") << "            : " << curr << std::endl;
    addMatchValue( qe, f, val, curr );
  }else{
    if( d_children_map.find( argIndex )==d_children_map.end() ){
      terms.push_back( fm->getRepresentative( d_node[argIndex] ) );
      calculateMatchesInterpreted( qe, f, curr, terms, argIndex+1 );
      terms.pop_back();
    }else{
      for( int i=0; i<(int)d_children[ d_children_map[argIndex] ].getNumMatches(); i++ ){
        InstMatch next( &curr );
        if( d_children[ d_children_map[argIndex] ].getMatch( qe->getEqualityQuery(), i, next ) ){
          terms.push_back( d_children[ d_children_map[argIndex] ].getMatchValue( i ) );
          calculateMatchesInterpreted( qe, f, next, terms, argIndex+1 );
          terms.pop_back();
        }
      }
    }
  }
}
