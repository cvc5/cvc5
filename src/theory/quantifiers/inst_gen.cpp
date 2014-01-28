/*********************                                                        */
/*! \file inst_gen.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of inst gen classes
 **/

#include "theory/quantifiers/inst_gen.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/model_builder.h"
#include "theory/quantifiers/first_order_model.h"

//#define CHILD_USE_CONSIDER

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;



InstGenProcess::InstGenProcess( Node n ) : d_node( n ){
  Assert( TermDb::hasInstConstAttr(n) );
  int count = 0;
  for( size_t i=0; i<n.getNumChildren(); i++ ){
    if( n[i].getKind()!=INST_CONSTANT && TermDb::hasInstConstAttr(n[i]) ){
      d_children.push_back( InstGenProcess( n[i] ) );
      d_children_index.push_back( i );
      d_children_map[ i ] = count;
      count++;
    }
    if( n[i].getKind()==INST_CONSTANT ){
      d_var_num[i] = n[i].getAttribute(InstVarNumAttribute());
    }
  }
}

void InstGenProcess::addMatchValue( QuantifiersEngine* qe, Node f, Node val, InstMatch& m ){
  if( !qe->existsInstantiation( f, m, true ) ){
    //make sure no duplicates are produced
    if( d_inst_trie[val].addInstMatch( qe, f, m, true ) ){
      d_match_values.push_back( val );
      d_matches.push_back( InstMatch( &m ) );
      ((QModelBuilderIG*)qe->getModelEngine()->getModelBuilder())->d_instGenMatches++;
    }
  }
}

void InstGenProcess::calculateMatches( QuantifiersEngine* qe, Node f, std::vector< Node >& considerVal, bool useConsider ){
  Trace("inst-gen-cm") << "* Calculate matches " << d_node << std::endl;
  //whether we are doing a product or sum or matches
  bool doProduct = true;
  //get the model
  FirstOrderModel* fm = qe->getModel();

  //calculate terms we will consider
  std::vector< Node > considerTerms;
  std::vector< std::vector< Node > > newConsiderVal;
  std::vector< bool > newUseConsider;
  std::map< Node, InstMatch > considerTermsMatch[2];
  std::map< Node, bool > considerTermsSuccess[2];
  newConsiderVal.resize( d_children.size() );
  newUseConsider.resize( d_children.size(), useConsider );
  if( d_node.getKind()==APPLY_UF ){
    Node op = d_node.getOperator();
    if( useConsider ){
#ifndef CHILD_USE_CONSIDER
      for( size_t i=0; i<newUseConsider.size(); i++ ){
        newUseConsider[i] = false;
      }
#endif
      for( size_t i=0; i<considerVal.size(); i++ ){
        eq::EqClassIterator eqc( qe->getEqualityQuery()->getEngine()->getRepresentative( considerVal[i] ),
                                 qe->getEqualityQuery()->getEngine() );
        while( !eqc.isFinished() ){
          Node en = (*eqc);
          if( en.getKind()==APPLY_UF && en.getOperator()==op ){
              considerTerms.push_back( en );
          }
          ++eqc;
        }
      }
    }else{
      considerTerms.insert( considerTerms.begin(), fm->d_uf_terms[op].begin(), fm->d_uf_terms[op].end() );
    }
    //for each term we consider, calculate a current match
    for( size_t i=0; i<considerTerms.size(); i++ ){
      Node n = considerTerms[i];
      bool isSelected = ((QModelBuilderIG*)qe->getModelEngine()->getModelBuilder())->isTermSelected( n );
      bool hadSuccess CVC4_UNUSED = false;
      for( int t=(isSelected ? 0 : 1); t<2; t++ ){
        if( t==0 || !n.getAttribute(NoMatchAttribute()) ){
          considerTermsMatch[t][n] = InstMatch( f );
          considerTermsSuccess[t][n] = true;
          for( size_t j=0; j<d_node.getNumChildren(); j++ ){
            if( d_children_map.find( j )==d_children_map.end() ){
              if( t!=0 || !n[j].getAttribute(ModelBasisAttribute()) ){
                if( d_node[j].getKind()==INST_CONSTANT ){
                  if( !considerTermsMatch[t][n].set( qe, d_var_num[j], n[j] ) ){
                    Trace("inst-gen-cm") << "fail match: " << n[j] << " is not equal to ";
                    Trace("inst-gen-cm") << considerTermsMatch[t][n].get( d_var_num[j] ) << std::endl;
                    considerTermsSuccess[t][n] = false;
                    break;
                  }
                }else if( !qe->getEqualityQuery()->areEqual( d_node[j], n[j] ) ){
                  Trace("inst-gen-cm") << "fail arg: " << n[j] << " is not equal to " << d_node[j] << std::endl;
                  considerTermsSuccess[t][n] = false;
                  break;
                }
              }
            }
          }
          //if successful, store it
          if( considerTermsSuccess[t][n] ){
#ifdef CHILD_USE_CONSIDER
            if( !hadSuccess ){
              hadSuccess = true;
              for( size_t k=0; k<d_children.size(); k++ ){
                if( newUseConsider[k] ){
                  int childIndex = d_children_index[k];
                  //determine if we are restricted or not
                  if( t!=0 || !n[childIndex].getAttribute(ModelBasisAttribute()) ){
                    Node r = qe->getModel()->getRepresentative( n[childIndex] );
                    if( std::find( newConsiderVal[k].begin(), newConsiderVal[k].end(), r )==newConsiderVal[k].end() ){
                      newConsiderVal[k].push_back( r );
                      //check if we now need to consider the entire domain
                      TypeNode tn = r.getType();
                      if( qe->getModel()->d_rep_set.hasType( tn ) ){
                        if( (int)newConsiderVal[k].size()>=qe->getModel()->d_rep_set.getNumRepresentatives( tn ) ){
                          newConsiderVal[k].clear();
                          newUseConsider[k] = false;
                        }
                      }
                    }
                  }else{
                    //matching against selected term, will need to consider all values
                    newConsiderVal[k].clear();
                    newUseConsider[k] = false;
                  }
                }
              }
            }
#endif
          }
        }
      }
    }
  }else{
    //the interpretted case
    if( d_node.getType().isBoolean() ){
      if( useConsider ){
        //if( considerVal.size()!=1 ) { std::cout << "consider val = " << considerVal.size() << std::endl; }
        Assert( considerVal.size()==1 );
        bool reqPol = considerVal[0]==fm->d_true;
        Node ncv = considerVal[0];
        if( d_node.getKind()==NOT ){
          ncv = reqPol ? fm->d_false : fm->d_true;
        }
        if( d_node.getKind()==NOT || d_node.getKind()==AND || d_node.getKind()==OR ){
          for( size_t i=0; i<newConsiderVal.size(); i++ ){
            newConsiderVal[i].push_back( ncv );
          }
          //instead we will do a sum
          if( ( d_node.getKind()==AND && !reqPol ) || ( d_node.getKind()==OR && reqPol )  ){
            doProduct = false;
          }
        }else{
          //do not use consider
          for( size_t i=0; i<newUseConsider.size(); i++ ){
            newUseConsider[i] = false;
          }
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
  if( d_node.getKind()==APPLY_UF ){
    //if this is an uninterpreted function
    Node op = d_node.getOperator();
    //process all values
    for( size_t i=0; i<considerTerms.size(); i++ ){
      Node n = considerTerms[i];
      bool isSelected = ((QModelBuilderIG*)qe->getModelEngine()->getModelBuilder())->isTermSelected( n );
      for( int t=(isSelected ? 0 : 1); t<2; t++ ){
        //do not consider ground case if it is already congruent to another ground term
        if( t==0 || !n.getAttribute(NoMatchAttribute()) ){
          Trace("inst-gen-cm") << "calculate for " << n << ", selected = " << (t==0) << std::endl;
          if( considerTermsSuccess[t][n] ){
            //try to find unifier for d_node = n
            calculateMatchesUninterpreted( qe, f, considerTermsMatch[t][n], n, 0, t==0 );
          }
        }
      }
    }
  }else{
    //if this is an interpreted function
    if( doProduct ){
      //combining children matches
      InstMatch curr( f );
      std::vector< Node > terms;
      calculateMatchesInterpreted( qe, f, curr, terms, 0 );
    }else{
      //summing children matches
      Assert( considerVal.size()==1 );
      for( int i=0; i<(int)d_children.size(); i++ ){
        for( int j=0; j<(int)d_children[ i ].getNumMatches(); j++ ){
          InstMatch m( f );
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
