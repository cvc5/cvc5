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
    //make sure no duplicates are produced
    if( d_inst_trie[val].addInstMatch( qe, f, m, true ) ){
      d_match_values.push_back( val );
      d_matches.push_back( InstMatch( &m ) );
      qe->getModelEngine()->getModelBuilder()->d_instGenMatches++;
    }
  }
}

void InstGenProcess::calculateMatches( QuantifiersEngine* qe, Node f, std::vector< Node >& considerVal, bool useConsider ){
  //whether we are doing a product or sum or matches
  bool doProduct = true;
  //get the model
  FirstOrderModel* fm = qe->getModel();

  //calculate terms we will consider
  std::vector< Node > considerTerms;
  std::vector< std::vector< Node > > newConsiderVal;
  std::vector< bool > newUseConsider;
  newConsiderVal.resize( d_children.size() );
  newUseConsider.resize( d_children.size(), false );
  if( d_node.getKind()==APPLY_UF ){
    Node op = d_node.getOperator();
    if( useConsider ){
      for( size_t i=0; i<considerVal.size(); i++ ){
        eq::EqClassIterator eqc( qe->getEqualityQuery()->getEngine()->getRepresentative( considerVal[i] ),
                                 qe->getEqualityQuery()->getEngine() );
        while( !eqc.isFinished() ){
          Node en = (*eqc);
          if( en.getKind()==APPLY_UF && en.getOperator()==op ){
            bool isSelected = qe->getModelEngine()->getModelBuilder()->isTermSelected( en );
            bool isActive = !en.getAttribute(NoMatchAttribute());
            //check if we need to consider it
            if( isSelected || isActive ){
              considerTerms.push_back( en );
#if 0
              for( int i=0; i<(int)d_children.size(); i++ ){
                int childIndex = d_children_index[i];
                Node n = qe->getModel()->getRepresentative( n );
                if( std::find( newConsiderVal[i].begin(), newConsiderVal[i].end(), n )==newConsiderVal[i].end() ){
                  newConsiderVal[i].push_back( n );
                }
              }
#endif
            }
          }
          ++eqc;
        }
      }
    }else{
      considerTerms.insert( considerTerms.begin(), fm->d_uf_terms[op].begin(), fm->d_uf_terms[op].end() );
    }
  }else if( d_node.getType().isBoolean() ){
    if( useConsider ){
      Assert( considerVal.size()==1 );
      bool reqPol = considerVal[0]==fm->d_true;
      if( d_node.getKind()==NOT ){
        if( !newConsiderVal.empty() ){
          newConsiderVal[0].push_back( reqPol ? fm->d_false : fm->d_true );
          newUseConsider[0] = true;
        }
      }else if( d_node.getKind()==AND || d_node.getKind()==OR ){
        for( size_t i=0; i<newConsiderVal.size(); i++ ){
          newConsiderVal[i].push_back( considerVal[0] );
          newUseConsider[i] = true;
        }
        //instead we will do a sum
        if( ( d_node.getKind()==AND && !reqPol ) || ( d_node.getKind()==OR && reqPol )  ){
          doProduct = false;
        }
      }
    }
  }

  //calculate all matches for children
  for( int i=0; i<(int)d_children.size(); i++ ){
    d_children[i].calculateMatches( qe, f, newConsiderVal[i], newUseConsider[i] );
    if( doProduct && d_children[i].getNumMatches()==0 ){
      return;
    }
  }
  Trace("inst-gen-cm") << "* Calculate matches " << d_node << std::endl;
  if( d_node.getKind()==APPLY_UF ){
    //if this is an uninterpreted function
    Node op = d_node.getOperator();
    //process all values
    for( size_t i=0; i<considerTerms.size(); i++ ){
      Node n = considerTerms[i];
      bool isSelected = qe->getModelEngine()->getModelBuilder()->isTermSelected( n );
      for( int t=(isSelected ? 0 : 1); t<2; t++ ){
        //do not consider ground case if it is already congruent to another ground term
        if( t==0 || !n.getAttribute(NoMatchAttribute()) ){
          Trace("inst-gen-cm") << "calculate for " << n << ", selected = " << (t==0) << std::endl;
          bool success = true;
          InstMatch curr;
          for( size_t j=0; j<d_node.getNumChildren(); j++ ){
            if( d_children_map.find( j )==d_children_map.end() ){
              if( t!=0 || !n[j].getAttribute(ModelBasisAttribute()) ){
                if( d_node[j].getKind()==INST_CONSTANT ){
                  //FIXME: is this correct?
                  if( !curr.setMatch( qe->getEqualityQuery(), d_node[j], n[j] ) ){
                    Trace("inst-gen-cm") << "fail match: " << n[j] << " is not equal to " << curr.get( d_node[j] ) << std::endl;
                    Trace("inst-gen-cm") << "  are equal : " << qe->getEqualityQuery()->areEqual( n[j], curr.get( d_node[j] ) ) << std::endl;
                    success = false;
                    break;
                  }
                }else if( !qe->getEqualityQuery()->areEqual( d_node[j], n[j] ) ){
                  Trace("inst-gen-cm") << "fail arg: " << n[j] << " is not equal to " << d_node[j] << std::endl;
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
    //if this is an interpreted function
    if( doProduct ){
      //combining children matches
      InstMatch curr;
      std::vector< Node > terms;
      calculateMatchesInterpreted( qe, f, curr, terms, 0 );
    }else{
      //summing children matches
      Assert( considerVal.size()==1 );
      for( int i=0; i<(int)d_children.size(); i++ ){
        for( int j=0; j<(int)d_children[ i ].getNumMatches(); j++ ){
          InstMatch m;
          if( d_children[ i ].getMatch( qe->getEqualityQuery(), j, m ) ){
            addMatchValue( qe, f, considerVal[0], m );
          }
        }
      }
    }
  }
  Trace("inst-gen-cm") << "done calculate matches" << std::endl;
  //can clear information used for finding duplicates
  d_inst_trie.clear();
}

bool InstGenProcess::getMatch( EqualityQuery* q, int i, InstMatch& m ){
  //FIXME: is this correct? (query may not be accurate)
  return m.merge( q, d_matches[i] );
}

void InstGenProcess::calculateMatchesUninterpreted( QuantifiersEngine* qe, Node f, InstMatch& curr, Node n, int childIndex, bool isSelected ){
  if( childIndex==(int)d_children.size() ){
    Node val = qe->getModel()->getRepresentative( n );  //FIXME: is this correct?
    Trace("inst-gen-cm") << "  - u-match : " << val << std::endl;
    Trace("inst-gen-cm") << "            : " << curr << std::endl;
    addMatchValue( qe, f, val, curr );
  }else{
    Trace("inst-gen-cm") << "Consider child index = " << childIndex << ", against ground term argument " << d_children_index[childIndex] << " ... " << n[d_children_index[childIndex]] << std::endl;
    bool sel = ( isSelected && n[d_children_index[childIndex]].getAttribute(ModelBasisAttribute()) );
    for( int i=0; i<(int)d_children[ childIndex ].getNumMatches(); i++ ){
      //FIXME: is this correct?
      if( sel || qe->getEqualityQuery()->areEqual( d_children[ childIndex ].getMatchValue( i ), n[d_children_index[childIndex]] ) ){
        InstMatch next( &curr );
        if( d_children[ childIndex ].getMatch( qe->getEqualityQuery(), i, next ) ){
          calculateMatchesUninterpreted( qe, f, next, n, childIndex+1, isSelected );
        }else{
          Trace("inst-gen-cm") << curr << " not equal to " << d_children[ childIndex ].d_matches[i] << std::endl;
          Trace("inst-gen-cm") << childIndex << " match " << i << " not equal subs." << std::endl;
        }
      }else{
        Trace("inst-gen-cm") << childIndex << " match " << i << " not equal value." << std::endl;
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
    Trace("inst-gen-cm") << "  - i-match : " << d_node << std::endl;
    Trace("inst-gen-cm") << "            : " << val << std::endl;
    Trace("inst-gen-cm") << "            : " << curr << std::endl;
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
