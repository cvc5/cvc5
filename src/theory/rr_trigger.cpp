/*********************                                                        */
/*! \file trigger.cpp
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
 ** \brief Implementation of trigger class
 **/

#include "theory/rr_trigger.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers_engine.h"
#include "theory/uf/theory_uf_instantiator.h"
#include "theory/rr_candidate_generator.h"
#include "theory/uf/equality_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::rrinst;

//#define NESTED_PATTERN_SELECTION

Trigger* Trigger::TrTrie::getTrigger2( std::vector< Node >& nodes ){
  if( nodes.empty() ){
    return d_tr;
  }else{
    Node n = nodes.back();
    nodes.pop_back();
    if( d_children.find( n )!=d_children.end() ){
      return d_children[n]->getTrigger2( nodes );
    }else{
      return NULL;
    }
  }
}
void Trigger::TrTrie::addTrigger2( std::vector< Node >& nodes, Trigger* t ){
  if( nodes.empty() ){
    d_tr = t;
  }else{
    Node n = nodes.back();
    nodes.pop_back();
    if( d_children.find( n )==d_children.end() ){
      d_children[n] = new TrTrie;
    }
    d_children[n]->addTrigger2( nodes, t );
  }
}

/** trigger static members */
std::map< Node, std::vector< Node > > Trigger::d_var_contains;
int Trigger::trCount = 0;
Trigger::TrTrie Trigger::d_tr_trie;

/** trigger class constructor */
Trigger::Trigger( QuantifiersEngine* qe, Node f, std::vector< Node >& nodes, int matchOption, bool smartTriggers ) :
d_quantEngine( qe ), d_f( f ){
  trCount++;
  d_nodes.insert( d_nodes.begin(), nodes.begin(), nodes.end() );
  Debug("trigger") << "Trigger for " << f << ": " << d_nodes << std::endl;
  if(matchOption == MATCH_GEN_DEFAULT) d_mg = mkPatterns( d_nodes, qe );
  else d_mg = mkPatternsEfficient( d_nodes, qe );
  if( d_nodes.size()==1 ){
    if( isSimpleTrigger( d_nodes[0] ) ){
      ++(qe->d_statistics.d_triggers);
    }else{
      ++(qe->d_statistics.d_simple_triggers);
    }
  }else{
    Debug("multi-trigger") << "Multi-trigger " << (*this) << std::endl;
    //std::cout << "Multi-trigger for " << f << " : " << std::endl;
    //std::cout << "   " << (*this) << std::endl;
    ++(qe->d_statistics.d_multi_triggers);
  }
}
void Trigger::computeVarContains( Node n ) {
  if( d_var_contains.find( n )==d_var_contains.end() ){
    d_var_contains[n].clear();
    computeVarContains2( n, n );
  }
}

void Trigger::computeVarContains2( Node n, Node parent ){
  if( n.getKind()==INST_CONSTANT ){
    if( std::find( d_var_contains[parent].begin(), d_var_contains[parent].end(), n )==d_var_contains[parent].end() ){
      d_var_contains[parent].push_back( n );
    }
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      computeVarContains2( n[i], parent );
    }
  }
}

void Trigger::resetInstantiationRound(){
  d_mg->resetInstantiationRound( d_quantEngine );
}


bool Trigger::getNextMatch(){
  bool retVal = d_mg->getNextMatch( d_quantEngine );
  //m.makeInternal( d_quantEngine->getEqualityQuery() );
  return retVal;
}

// bool Trigger::getMatch( Node t, InstMatch& m ){
//   //FIXME: this assumes d_mg is an inst match generator
//   return ((InstMatchGenerator*)d_mg)->getMatch( t, m, d_quantEngine );
// }


int Trigger::addInstantiations( InstMatch& baseMatch ){
  int addedLemmas = d_mg->addInstantiations( baseMatch,
                                             d_nodes[0].getAttribute(InstConstantAttribute()),
                                             d_quantEngine);
  if( addedLemmas>0 ){
    Debug("inst-trigger") << "Added " << addedLemmas << " lemmas, trigger was ";
    for( int i=0; i<(int)d_nodes.size(); i++ ){
      Debug("inst-trigger") << d_nodes[i] << " ";
    }
    Debug("inst-trigger") << std::endl;
  }
  return addedLemmas;
}

Trigger* Trigger::mkTrigger( QuantifiersEngine* qe, Node f, std::vector< Node >& nodes, int matchOption, bool keepAll, int trOption,
                             bool smartTriggers ){
  std::vector< Node > trNodes;
  if( !keepAll ){
    //only take nodes that contribute variables to the trigger when added
    std::vector< Node > temp;
    temp.insert( temp.begin(), nodes.begin(), nodes.end() );
    std::map< Node, bool > vars;
    std::map< Node, std::vector< Node > > patterns;
    for( int i=0; i<(int)temp.size(); i++ ){
      bool foundVar = false;
      computeVarContains( temp[i] );
      for( int j=0; j<(int)d_var_contains[ temp[i] ].size(); j++ ){
        Node v = d_var_contains[ temp[i] ][j];
        if( v.getAttribute(InstConstantAttribute())==f ){
          if( vars.find( v )==vars.end() ){
            vars[ v ] = true;
            foundVar = true;
          }
        }
      }
      if( foundVar ){
        trNodes.push_back( temp[i] );
        for( int j=0; j<(int)d_var_contains[ temp[i] ].size(); j++ ){
          Node v = d_var_contains[ temp[i] ][j];
          patterns[ v ].push_back( temp[i] );
        }
      }
    }
    //now, minimalize the trigger
    for( int i=0; i<(int)trNodes.size(); i++ ){
      bool keepPattern = false;
      Node n = trNodes[i];
      for( int j=0; j<(int)d_var_contains[ n ].size(); j++ ){
        Node v = d_var_contains[ n ][j];
        if( patterns[v].size()==1 ){
          keepPattern = true;
          break;
        }
      }
      if( !keepPattern ){
        //remove from pattern vector
        for( int j=0; j<(int)d_var_contains[ n ].size(); j++ ){
          Node v = d_var_contains[ n ][j];
          for( int k=0; k<(int)patterns[v].size(); k++ ){
            if( patterns[v][k]==n ){
              patterns[v].erase( patterns[v].begin() + k, patterns[v].begin() + k + 1 );
              break;
            }
          }
        }
        //remove from trigger nodes
        trNodes.erase( trNodes.begin() + i, trNodes.begin() + i + 1 );
        i--;
      }
    }
  }else{
    trNodes.insert( trNodes.begin(), nodes.begin(), nodes.end() );
  }

  //check for duplicate?
  if( trOption==TR_MAKE_NEW ){
    //static int trNew = 0;
    //static int trOld = 0;
    //Trigger* t = d_tr_trie.getTrigger( trNodes );
    //if( t ){
    //  trOld++;
    //}else{
    //  trNew++;
    //}
    //if( (trNew+trOld)%100==0 ){
    //  std::cout << "Trigger new old = " << trNew << " " << trOld << std::endl;
    //}
  }else{
    Trigger* t = d_tr_trie.getTrigger( trNodes );
    if( t ){
      if( trOption==TR_GET_OLD ){
        //just return old trigger
        return t;
      }else{
        return NULL;
      }
    }
  }
  Trigger* t = new Trigger( qe, f, trNodes, matchOption, smartTriggers );
  d_tr_trie.addTrigger( trNodes, t );
  return t;
}
Trigger* Trigger::mkTrigger( QuantifiersEngine* qe, Node f, Node n, int matchOption, bool keepAll, int trOption, bool smartTriggers ){
  std::vector< Node > nodes;
  nodes.push_back( n );
  return mkTrigger( qe, f, nodes, matchOption, keepAll, trOption, smartTriggers );
}

bool Trigger::isUsableTrigger( std::vector< Node >& nodes, Node f ){
  for( int i=0; i<(int)nodes.size(); i++ ){
    if( !isUsableTrigger( nodes[i], f ) ){
      return false;
    }
  }
  return true;
}

bool Trigger::isUsable( Node n, Node f ){
  if( n.getAttribute(InstConstantAttribute())==f ){
    if( !isAtomicTrigger( n ) && n.getKind()!=INST_CONSTANT ){
      std::map< Node, Node > coeffs;
      return getPatternArithmetic( f, n, coeffs );
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        if( !isUsable( n[i], f ) ){
          return false;
        }
      }
      return true;
    }
  }else{
    return true;
  }
}

bool Trigger::isSimpleTrigger( Node n ){
  if( isAtomicTrigger( n ) ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( n[i].getKind()!=INST_CONSTANT && n[i].hasAttribute(InstConstantAttribute()) ){
        return false;
      }
    }
    return true;
  }else{
    return false;
  }
}

/** filter all nodes that have instances */
void Trigger::filterInstances( std::vector< Node >& nodes ){
  std::vector< bool > active;
  active.resize( nodes.size(), true );
  for( int i=0; i<(int)nodes.size(); i++ ){
    for( int j=i+1; j<(int)nodes.size(); j++ ){
      if( active[i] && active[j] ){
        int result = isInstanceOf( nodes[i], nodes[j] );
        if( result==1 ){
          active[j] = false;
        }else if( result==-1 ){
          active[i] = false;
        }
      }
    }
  }
  std::vector< Node > temp;
  for( int i=0; i<(int)nodes.size(); i++ ){
    if( active[i] ){
      temp.push_back( nodes[i] );
    }
  }
  nodes.clear();
  nodes.insert( nodes.begin(), temp.begin(), temp.end() );
}


bool Trigger::collectPatTerms2( QuantifiersEngine* qe, Node f, Node n, std::map< Node, bool >& patMap, int tstrt ){
  if( patMap.find( n )==patMap.end() ){
    patMap[ n ] = false;
    if( tstrt==TS_MIN_TRIGGER ){
      if( n.getKind()==FORALL ){
#ifdef NESTED_PATTERN_SELECTION
        //return collectPatTerms2( qe, f, qe->getOrCreateCounterexampleBody( n ), patMap, tstrt );
        return collectPatTerms2( qe, f, qe->getBoundBody( n ), patMap, tstrt );
#else
        return false;
#endif
      }else{
        bool retVal = false;
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          if( collectPatTerms2( qe, f, n[i], patMap, tstrt ) ){
            retVal = true;
          }
        }
        if( retVal ){
          return true;
        }else if( isUsableTrigger( n, f ) ){
          patMap[ n ] = true;
          return true;
        }else{
          return false;
        }
      }
    }else{
      bool retVal = false;
      if( isUsableTrigger( n, f ) ){
        patMap[ n ] = true;
        if( tstrt==TS_MAX_TRIGGER ){
          return true;
        }else{
          retVal = true;
        }
      }
      if( n.getKind()==FORALL ){
#ifdef NESTED_PATTERN_SELECTION
        //if( collectPatTerms2( qe, f, qe->getOrCreateCounterexampleBody( n ), patMap, tstrt ) ){
        //  retVal = true;
        //}
        if( collectPatTerms2( qe, f, qe->getBoundBody( n ), patMap, tstrt ) ){
          retVal = true;
        }
#endif
      }else{
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          if( collectPatTerms2( qe, f, n[i], patMap, tstrt ) ){
            retVal = true;
          }
        }
      }
      return retVal;
    }
  }else{
    return patMap[ n ];
  }
}

void Trigger::collectPatTerms( QuantifiersEngine* qe, Node f, Node n, std::vector< Node >& patTerms, int tstrt, bool filterInst ){
  std::map< Node, bool > patMap;
  if( filterInst ){
    //immediately do not consider any term t for which another term is an instance of t
    std::vector< Node > patTerms2;
    collectPatTerms( qe, f, n, patTerms2, TS_ALL, false );
    std::vector< Node > temp;
    temp.insert( temp.begin(), patTerms2.begin(), patTerms2.end() );
    filterInstances( temp );
    if( temp.size()!=patTerms2.size() ){
      Debug("trigger-filter-instance") << "Filtered an instance: " << std::endl;
      Debug("trigger-filter-instance") << "Old: ";
      for( int i=0; i<(int)patTerms2.size(); i++ ){
        Debug("trigger-filter-instance") << patTerms2[i] << " ";
      }
      Debug("trigger-filter-instance") << std::endl << "New: ";
      for( int i=0; i<(int)temp.size(); i++ ){
        Debug("trigger-filter-instance") << temp[i] << " ";
      }
      Debug("trigger-filter-instance") << std::endl;
    }
    if( tstrt==TS_ALL ){
      patTerms.insert( patTerms.begin(), temp.begin(), temp.end() );
      return;
    }else{
      //do not consider terms that have instances
      for( int i=0; i<(int)patTerms2.size(); i++ ){
        if( std::find( temp.begin(), temp.end(), patTerms2[i] )==temp.end() ){
          patMap[ patTerms2[i] ] = false;
        }
      }
    }
  }
  collectPatTerms2( qe, f, n, patMap, tstrt );
  for( std::map< Node, bool >::iterator it = patMap.begin(); it != patMap.end(); ++it ){
    if( it->second ){
      patTerms.push_back( it->first );
    }
  }
}

/** is n1 an instance of n2 or vice versa? */
int Trigger::isInstanceOf( Node n1, Node n2 ){
  if( n1==n2 ){
    return 1;
  }else if( n1.getKind()==n2.getKind() ){
    if( n1.getKind()==APPLY_UF ){
      if( n1.getOperator()==n2.getOperator() ){
        int result = 0;
        for( int i=0; i<(int)n1.getNumChildren(); i++ ){
          if( n1[i]!=n2[i] ){
            int cResult = isInstanceOf( n1[i], n2[i] );
            if( cResult==0 ){
              return 0;
            }else if( cResult!=result ){
              if( result!=0 ){
                return 0;
              }else{
                result = cResult;
              }
            }
          }
        }
        return result;
      }
    }
    return 0;
  }else if( n2.getKind()==INST_CONSTANT ){
    computeVarContains( n1 );
    //if( std::find( d_var_contains[ n1 ].begin(), d_var_contains[ n1 ].end(), n2 )!=d_var_contains[ n1 ].end() ){
    //  return 1;
    //}
    if( d_var_contains[ n1 ].size()==1 && d_var_contains[ n1 ][ 0 ]==n2 ){
      return 1;
    }
  }else if( n1.getKind()==INST_CONSTANT ){
    computeVarContains( n2 );
    //if( std::find( d_var_contains[ n2 ].begin(), d_var_contains[ n2 ].end(), n1 )!=d_var_contains[ n2 ].end() ){
    //  return -1;
    //}
    if( d_var_contains[ n2 ].size()==1 && d_var_contains[ n2 ][ 0 ]==n1 ){
      return 1;
    }
  }
  return 0;
}

bool Trigger::isVariableSubsume( Node n1, Node n2 ){
  if( n1==n2 ){
    return true;
  }else{
    //std::cout << "is variable subsume ? " << n1 << " " << n2 << std::endl;
    computeVarContains( n1 );
    computeVarContains( n2 );
    for( int i=0; i<(int)d_var_contains[n2].size(); i++ ){
      if( std::find( d_var_contains[n1].begin(), d_var_contains[n1].end(), d_var_contains[n2][i] )==d_var_contains[n1].end() ){
        //std::cout << "no" << std::endl;
        return false;
      }
    }
    //std::cout << "yes" << std::endl;
    return true;
  }
}

void Trigger::getVarContains( Node f, std::vector< Node >& pats, std::map< Node, std::vector< Node > >& varContains ){
  for( int i=0; i<(int)pats.size(); i++ ){
    computeVarContains( pats[i] );
    varContains[ pats[i] ].clear();
    for( int j=0; j<(int)d_var_contains[pats[i]].size(); j++ ){
      if( d_var_contains[pats[i]][j].getAttribute(InstConstantAttribute())==f ){
        varContains[ pats[i] ].push_back( d_var_contains[pats[i]][j] );
      }
    }
  }
}

void Trigger::getVarContainsNode( Node f, Node n, std::vector< Node >& varContains ){
  computeVarContains( n );
  for( int j=0; j<(int)d_var_contains[n].size(); j++ ){
    if( d_var_contains[n][j].getAttribute(InstConstantAttribute())==f ){
      varContains.push_back( d_var_contains[n][j] );
    }
  }
}

bool Trigger::getPatternArithmetic( Node f, Node n, std::map< Node, Node >& coeffs ){
  if( n.getKind()==PLUS ){
    Assert( coeffs.empty() );
    NodeBuilder<> t(kind::PLUS);
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( n[i].hasAttribute(InstConstantAttribute()) ){
        if( n[i].getKind()==INST_CONSTANT ){
          if( n[i].getAttribute(InstConstantAttribute())==f ){
            coeffs[ n[i] ] = Node::null();
          }else{
            coeffs.clear();
            return false;
          }
        }else if( !getPatternArithmetic( f, n[i], coeffs ) ){
          coeffs.clear();
          return false;
        }
      }else{
        t << n[i];
      }
    }
    if( t.getNumChildren()==0 ){
      coeffs[ Node::null() ] = NodeManager::currentNM()->mkConst( Rational(0) );
    }else if( t.getNumChildren()==1 ){
      coeffs[ Node::null() ]  = t.getChild( 0 );
    }else{
      coeffs[ Node::null() ]  = t;
    }
    return true;
  }else if( n.getKind()==MULT ){
    if( n[0].getKind()==INST_CONSTANT && n[0].getAttribute(InstConstantAttribute())==f ){
      Assert( !n[1].hasAttribute(InstConstantAttribute()) );
      coeffs[ n[0] ] = n[1];
      return true;
    }else if( n[1].getKind()==INST_CONSTANT && n[1].getAttribute(InstConstantAttribute())==f ){
      Assert( !n[0].hasAttribute(InstConstantAttribute()) );
      coeffs[ n[1] ] = n[0];
      return true;
    }
  }
  return false;
}
