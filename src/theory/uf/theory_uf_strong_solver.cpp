/*********************                                                        */
/*! \file theory_uf_strong_solver.cpp
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
 ** \brief Implementation of theory uf strong solver class
 **/

#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf_instantiator.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers/term_database.h"

//#define USE_SMART_SPLITS
//#define ONE_SPLIT_REGION
//#define DISABLE_QUICK_CLIQUE_CHECKS
//#define COMBINE_REGIONS_SMALL_INTO_LARGE

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

void StrongSolverTheoryUf::ConflictFind::Region::addRep( Node n ) {
  setRep( n, true );
}

void StrongSolverTheoryUf::ConflictFind::Region::takeNode( StrongSolverTheoryUf::ConflictFind::Region* r, Node n ){
  //Debug("uf-ss") << "takeNode " << r << " " << n << std::endl;
  //Debug("uf-ss") << "r : " << std::endl;
  //r->debugPrint("uf-ss");
  //Debug("uf-ss") << "this : " << std::endl;
  //debugPrint("uf-ss");
  Assert( !hasRep( n ) );
  Assert( r->hasRep( n ) );
  //add representative
  setRep( n, true );
  //take disequalities from r
  RegionNodeInfo* rni = r->d_nodes[n];
  for( int t=0; t<2; t++ ){
    RegionNodeInfo::DiseqList* del = rni->d_disequalities[t];
    for( NodeBoolMap::iterator it = del->d_disequalities.begin(); it != del->d_disequalities.end(); ++it ){
      if( (*it).second ){
        r->setDisequal( n, (*it).first, t, false );
        if( t==0 ){
          if( hasRep( (*it).first ) ){
            setDisequal( (*it).first, n, 0, false );
            setDisequal( (*it).first, n, 1, true );
            setDisequal( n, (*it).first, 1, true );
          }else{
            setDisequal( n, (*it).first, 0, true );
          }
        }else{
          r->setDisequal( (*it).first, n, 1, false );
          r->setDisequal( (*it).first, n, 0, true );
          setDisequal( n, (*it).first, 0, true );
        }
      }
    }
  }
  //remove representative
  r->setRep( n, false );
}

void StrongSolverTheoryUf::ConflictFind::Region::combine( StrongSolverTheoryUf::ConflictFind::Region* r ){
  //take all nodes from r
  for( std::map< Node, RegionNodeInfo* >::iterator it = r->d_nodes.begin(); it != r->d_nodes.end(); ++it ){
    if( it->second->d_valid ){
      setRep( it->first, true );
    }
  }
  for( std::map< Node, RegionNodeInfo* >::iterator it = r->d_nodes.begin(); it != r->d_nodes.end(); ++it ){
    if( it->second->d_valid ){
      //take disequalities from r
      Node n = it->first;
      RegionNodeInfo* rni = it->second;
      for( int t=0; t<2; t++ ){
        RegionNodeInfo::DiseqList* del = rni->d_disequalities[t];
        for( NodeBoolMap::iterator it2 = del->d_disequalities.begin(); it2 != del->d_disequalities.end(); ++it2 ){
          if( (*it2).second ){
            if( t==0 && hasRep( (*it2).first ) ){
              setDisequal( (*it2).first, n, 0, false );
              setDisequal( (*it2).first, n, 1, true );
              setDisequal( n, (*it2).first, 1, true );
            }else{
              setDisequal( n, (*it2).first, t, true );
            }
          }
        }
      }
    }
  }
  r->d_valid = false;
}

/** setEqual */
void StrongSolverTheoryUf::ConflictFind::Region::setEqual( Node a, Node b ){
  Assert( hasRep( a ) && hasRep( b ) );
  //move disequalities of b over to a
  for( int t=0; t<2; t++ ){
    RegionNodeInfo::DiseqList* del = d_nodes[b]->d_disequalities[t];
    for( NodeBoolMap::iterator it = del->d_disequalities.begin(); it != del->d_disequalities.end(); ++it ){
      if( (*it).second ){
        Node n = (*it).first;
        Region* nr = d_cf->d_regions[ d_cf->d_regions_map[ n ] ];
        if( !isDisequal( a, n, t ) ){
          setDisequal( a, n, t, true );
          nr->setDisequal( n, a, t, true );
        }
        setDisequal( b, n, t, false );
        nr->setDisequal( n, b, t, false );
      }
    }
  }
  //remove b from representatives
  setRep( b, false );
}

void StrongSolverTheoryUf::ConflictFind::Region::setDisequal( Node n1, Node n2, int type, bool valid ){
  //Debug("uf-ss-region-debug") << "set disequal " << n1 << " " << n2 << " " << type << " " << valid << std::endl;
  //debugPrint("uf-ss-region-debug");
  //Assert( isDisequal( n1, n2, type )!=valid );
  if( isDisequal( n1, n2, type )!=valid ){    //DO_THIS: make assertion
    d_nodes[ n1 ]->d_disequalities[type]->setDisequal( n2, valid );
    if( type==0 ){
      d_total_diseq_external = d_total_diseq_external + ( valid ? 1 : -1 );
    }else{
      d_total_diseq_internal = d_total_diseq_internal + ( valid ? 1 : -1 );
      if( valid ){
        //if they are both a part of testClique, then remove split
        if( d_testClique.find( n1 )!=d_testClique.end() && d_testClique[n1] &&
            d_testClique.find( n2 )!=d_testClique.end() && d_testClique[n2] ){
          Node eq = NodeManager::currentNM()->mkNode( EQUAL, n1, n2 );
          if( d_splits.find( eq )!=d_splits.end() && d_splits[ eq ] ){
            Debug("uf-ss-debug") << "removing split for " << n1 << " " << n2 << std::endl;
            d_splits[ eq ] = false;
            d_splitsSize = d_splitsSize - 1;
          }
        }
      }
    }
  }
}

void StrongSolverTheoryUf::ConflictFind::Region::setRep( Node n, bool valid ){
  Assert( hasRep( n )!=valid );
  if( valid && d_nodes.find( n )==d_nodes.end() ){
    d_nodes[n] = new RegionNodeInfo( d_cf->d_th->getSatContext() );
  }
  d_nodes[n]->d_valid = valid;
  d_reps_size = d_reps_size + ( valid ? 1 : -1 );
  //removing a member of the test clique from this region
  if( d_testClique.find( n )!=d_testClique.end() && d_testClique[n] ){
    Assert( !valid );
    d_testClique[n] = false;
    d_testCliqueSize = d_testCliqueSize - 1;
    //remove all splits involving n
    for( NodeBoolMap::iterator it = d_splits.begin(); it != d_splits.end(); ++it ){
      if( (*it).second ){
        if( (*it).first[0]==n || (*it).first[1]==n ){
          d_splits[ (*it).first ] = false;
          d_splitsSize = d_splitsSize - 1;
        }
      }
    }
  }
}

bool StrongSolverTheoryUf::ConflictFind::Region::isDisequal( Node n1, Node n2, int type ){
  RegionNodeInfo::DiseqList* del = d_nodes[ n1 ]->d_disequalities[type];
  return del->d_disequalities.find( n2 )!=del->d_disequalities.end() && del->d_disequalities[n2];
}

struct sortInternalDegree {
  StrongSolverTheoryUf::ConflictFind::Region* r;
  bool operator() (Node i,Node j) { return (r->d_nodes[i]->getNumInternalDisequalities()>r->d_nodes[j]->getNumInternalDisequalities());}
};

struct sortExternalDegree {
  StrongSolverTheoryUf::ConflictFind::Region* r;
  bool operator() (Node i,Node j) { return (r->d_nodes[i]->getNumExternalDisequalities()>r->d_nodes[j]->getNumExternalDisequalities());}
};

bool StrongSolverTheoryUf::ConflictFind::Region::getMustCombine( int cardinality ){
  if( Options::current()->ufssRegions && d_total_diseq_external>=long(cardinality) ){
    //The number of external disequalities is greater than or equal to cardinality.
    //Thus, a clique of size cardinality+1 may exist between nodes in d_regions[i] and other regions
    //Check if this is actually the case:  must have n nodes with outgoing degree (cardinality+1-n) for some n>0
    std::vector< int > degrees;
    for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
      RegionNodeInfo* rni = it->second;
      if( rni->d_valid ){
        if( rni->getNumDisequalities()>=cardinality ){
          int outDeg = rni->getNumExternalDisequalities();
          if( outDeg>=cardinality ){
            //we have 1 node of degree greater than (cardinality)
            return true;
          }else if( outDeg>=1 ){
            degrees.push_back( outDeg );
            if( (int)degrees.size()>=cardinality ){
              //we have (cardinality) nodes of degree 1
              return true;
            }
          }
        }
      }
    }
    //static int gmcCount = 0;
    //gmcCount++;
    //if( gmcCount%100==0 ){
    //  std::cout << gmcCount << " " << cardinality << std::endl;
    //}
    //this should happen relatively infrequently....
    std::sort( degrees.begin(), degrees.end() );
    for( int i=0; i<(int)degrees.size(); i++ ){
      if( degrees[i]>=cardinality+1-((int)degrees.size()-i) ){
        return true;
      }
    }
  }
  return false;
}

bool StrongSolverTheoryUf::ConflictFind::Region::check( Theory::Effort level, int cardinality, std::vector< Node >& clique ){
  if( d_reps_size>long(cardinality) ){
    if( d_total_diseq_internal==d_reps_size*( d_reps_size - 1 ) ){
      //quick clique check, all reps form a clique
      for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
        if( it->second->d_valid ){
          clique.push_back( it->first );
        }
      }
      return true;
    }else if( Options::current()->ufssRegions || Options::current()->ufssEagerSplits || level==Theory::EFFORT_FULL ){
      //build test clique, up to size cardinality+1
      if( d_testCliqueSize<=long(cardinality) ){
        std::vector< Node > newClique;
        if( d_testCliqueSize<long(cardinality) ){
          for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
            //if not in the test clique, add it to the set of new members
            if( it->second->d_valid && ( d_testClique.find( it->first )==d_testClique.end() || !d_testClique[ it->first ] ) ){
              //if( it->second->getNumInternalDisequalities()>cardinality || level==Theory::EFFORT_FULL ){
              newClique.push_back( it->first );
              //}
            }
          }
          //choose remaining nodes with the highest degrees
          sortInternalDegree sidObj;
          sidObj.r = this;
          std::sort( newClique.begin(), newClique.end(), sidObj );
          newClique.erase( newClique.begin() + ( cardinality - d_testCliqueSize ) + 1, newClique.end() );
        }else{
          //scan for the highest degree
          int maxDeg = -1;
          Node maxNode;
          for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
            //if not in the test clique, add it to the set of new members
            if( it->second->d_valid && ( d_testClique.find( it->first )==d_testClique.end() || !d_testClique[ it->first ] ) ){
              if( it->second->getNumInternalDisequalities()>maxDeg ){
                maxDeg = it->second->getNumInternalDisequalities();
                maxNode = it->first;
              }
            }
          }
          Assert( maxNode!=Node::null() );
          newClique.push_back( maxNode );
        }
        //check splits internal to new members
        for( int j=0; j<(int)newClique.size(); j++ ){
          Debug("uf-ss-debug") << "Choose to add clique member " << newClique[j] << std::endl;
          for( int k=(j+1); k<(int)newClique.size(); k++ ){
            if( !isDisequal( newClique[j], newClique[k], 1 ) ){
              d_splits[ NodeManager::currentNM()->mkNode( EQUAL, newClique[j], newClique[k] ) ] = true;
              d_splitsSize = d_splitsSize + 1;
            }
          }
          //check disequalities with old members
          for( NodeBoolMap::iterator it = d_testClique.begin(); it != d_testClique.end(); ++it ){
            if( (*it).second ){
              if( !isDisequal( (*it).first, newClique[j], 1 ) ){
                d_splits[ NodeManager::currentNM()->mkNode( EQUAL, (*it).first, newClique[j] ) ] = true;
                d_splitsSize = d_splitsSize + 1;
              }
            }
          }
        }
        //add new clique members to test clique
        for( int j=0; j<(int)newClique.size(); j++ ){
          d_testClique[ newClique[j] ] = true;
          d_testCliqueSize = d_testCliqueSize + 1;
        }
      }
      //check if test clique has larger size than cardinality, and forms a clique
      if( d_testCliqueSize>=long(cardinality+1) && d_splitsSize==0 ){
        //test clique is a clique
        for( NodeBoolMap::iterator it = d_testClique.begin(); it != d_testClique.end(); ++it ){
          if( (*it).second ){
            clique.push_back( (*it).first );
          }
        }
        return true;
      }
    }
  }
  return false;
}

void StrongSolverTheoryUf::ConflictFind::Region::getRepresentatives( std::vector< Node >& reps ){
  for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
    RegionNodeInfo* rni = it->second;
    if( rni->d_valid ){
      reps.push_back( it->first );
    }
  }
}

void StrongSolverTheoryUf::ConflictFind::Region::getNumExternalDisequalities( std::map< Node, int >& num_ext_disequalities ){
  for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
    RegionNodeInfo* rni = it->second;
    if( rni->d_valid ){
      RegionNodeInfo::DiseqList* del = rni->d_disequalities[0];
      for( NodeBoolMap::iterator it2 = del->d_disequalities.begin(); it2 != del->d_disequalities.end(); ++it2 ){
        if( (*it2).second ){
          num_ext_disequalities[ (*it2).first ]++;
        }
      }
    }
  }
}

Node StrongSolverTheoryUf::ConflictFind::Region::getBestSplit(){
#ifndef USE_SMART_SPLITS
  //take the first split you find
  for( NodeBoolMap::iterator it = d_splits.begin(); it != d_splits.end(); ++it ){
    if( (*it).second ){
      return (*it).first;
    }
  }
  return Node::null();
#else
  std::vector< Node > splits;
  for( NodeBoolMap::iterator it = d_splits.begin(); it != d_splits.end(); ++it ){
    if( (*it).second ){
      splits.push_back( (*it).first );
    }
  }
  if( splits.size()>1 ){
    std::map< Node, std::map< Node, bool > > ops;
    Debug("uf-ss-split") << "Choice for splits: " << std::endl;
    double maxScore = -1;
    int maxIndex;
    for( int i=0; i<(int)splits.size(); i++ ){
      Debug("uf-ss-split") << "   " << splits[i] << std::endl;
      for( int j=0; j<2; j++ ){
        if( ops.find( splits[i][j] )==ops.end() ){
          EqClassIterator eqc( splits[i][j], ((uf::TheoryUF*)d_cf->d_th)->getEqualityEngine() );
          while( !eqc.isFinished() ){
            Node n = (*eqc);
            if( n.getKind()==APPLY_UF ){
              ops[ splits[i][j] ][ n.getOperator() ] = true;
            }
            ++eqc;
          }
        }
      }
      //now, compute score
      int common[2] = { 0, 0 };
      for( int j=0; j<2; j++ ){
        int j2 = j==0 ? 1 : 0;
        for( std::map< Node, bool >::iterator it = ops[ splits[i][j] ].begin(); it != ops[ splits[i][j] ].end(); ++it ){
          if( ops[ splits[i][j2] ].find( it->first )!=ops[ splits[i][j2] ].end() ){
            common[0]++;
          }else{
            common[1]++;
          }
        }
      }
      double score = ( 1.0 + (double)common[0] )/( 1.0 + (double)common[1] );
      if( score>maxScore ){
        maxScore = score;
        maxIndex = i;
      }
    }
    //if( maxIndex!=0 ){
    //  std::cout << "Chose maxIndex = " << maxIndex << std::endl;
    //}
    return splits[maxIndex];
  }else if( !splits.empty() ){
    return splits[0];
  }else{
    return Node::null();
  }
#endif
}

void StrongSolverTheoryUf::ConflictFind::Region::addSplit( OutputChannel* out ){
  Node s = getBestSplit();
  //add lemma to output channel
  Assert( s!=Node::null() && s.getKind()==EQUAL );
  s = Rewriter::rewrite( s );
  Debug("uf-ss-lemma") << "*** Split on " << s << std::endl;
  //Debug("uf-ss-lemma") << d_th->getEqualityEngine()->areEqual( s[0], s[1] ) << " ";
  //Debug("uf-ss-lemma") << d_th->getEqualityEngine()->areDisequal( s[0], s[1] ) << std::endl;
  //Debug("uf-ss-lemma") << s[0].getType() << " " << s[1].getType() << std::endl;
  debugPrint("uf-ss-temp");
  //Notice() << "*** Split on " << s << std::endl;
  //split on the equality s
  out->split( s );
  //tell the sat solver to explore the equals branch first
  out->requirePhase( s, true );
}

bool StrongSolverTheoryUf::ConflictFind::Region::minimize( OutputChannel* out ){
  if( hasSplits() ){
    addSplit( out );
    return false;
  }else{
    return true;
  }
}

void StrongSolverTheoryUf::ConflictFind::Region::debugPrint( const char* c, bool incClique ){
  Debug( c ) << "Num reps: " << d_reps_size << std::endl;
  for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
    RegionNodeInfo* rni = it->second;
    if( rni->d_valid ){
      Node n = it->first;
      Debug( c ) << "   " << n << std::endl;
      for( int i=0; i<2; i++ ){
        Debug( c ) << "      " << ( i==0 ? "Ext" : "Int" ) << " disequal:";
        RegionNodeInfo::DiseqList* del = rni->d_disequalities[i];
        for( NodeBoolMap::iterator it2 = del->d_disequalities.begin(); it2 != del->d_disequalities.end(); ++it2 ){
          if( (*it2).second ){
            Debug( c ) << " " << (*it2).first;
          }
        }
        Debug( c ) << ", total = " << del->d_size << std::endl;
      }
    }
  }
  Debug( c ) << "Total disequal: " << d_total_diseq_external << " external," << std::endl;
  Debug( c ) << "                " << d_total_diseq_internal<< " internal." << std::endl;

  if( incClique ){
    Debug( c ) << "Candidate clique members: " << std::endl;
    Debug( c ) << "   ";
    for( NodeBoolMap::iterator it = d_testClique.begin(); it != d_testClique.end(); ++ it ){
      if( (*it).second ){
        Debug( c ) << (*it).first << " ";
      }
    }
    Debug( c ) << ", size = " << d_testCliqueSize << std::endl;
    Debug( c ) << "Required splits: " << std::endl;
    Debug( c ) << "   ";
    for( NodeBoolMap::iterator it = d_splits.begin(); it != d_splits.end(); ++ it ){
      if( (*it).second ){
        Debug( c ) << (*it).first << " ";
      }
    }
    Debug( c ) << ", size = " << d_splitsSize << std::endl;
  }
}

int StrongSolverTheoryUf::ConflictFind::getNumDisequalitiesToRegion( Node n, int ri ){
  int ni = d_regions_map[n];
  int counter = 0;
  Region::RegionNodeInfo::DiseqList* del = d_regions[ni]->d_nodes[n]->d_disequalities[0];
  for( NodeBoolMap::iterator it = del->d_disequalities.begin(); it != del->d_disequalities.end(); ++it ){
    if( (*it).second ){
      if( d_regions_map[ (*it).first ]==ri ){
        counter++;
      }
    }
  }
  return counter;
}

void StrongSolverTheoryUf::ConflictFind::getDisequalitiesToRegions( int ri, std::map< int, int >& regions_diseq ){
  for( std::map< Node, Region::RegionNodeInfo* >::iterator it = d_regions[ri]->d_nodes.begin();
       it != d_regions[ri]->d_nodes.end(); ++it ){
    if( it->second->d_valid ){
      Region::RegionNodeInfo::DiseqList* del = it->second->d_disequalities[0];
      for( NodeBoolMap::iterator it2 = del->d_disequalities.begin(); it2 != del->d_disequalities.end(); ++it2 ){
        if( (*it2).second ){
          Assert( isValid( d_regions_map[ (*it2).first ] ) );
          //Notice() << "Found disequality with " << (*it2).first << ", region = " << d_regions_map[ (*it2).first ] << std::endl;
          regions_diseq[ d_regions_map[ (*it2).first ] ]++;
        }
      }
    }
  }
}

void StrongSolverTheoryUf::ConflictFind::explainClique( std::vector< Node >& clique, OutputChannel* out ){
  Assert( d_cardinality>0 );
  while( clique.size()>size_t(d_cardinality+1) ){
    clique.pop_back();
  }
  //found a clique
  Debug("uf-ss") << "Found a clique (cardinality=" << d_cardinality << ") :" << std::endl;
  Debug("uf-ss") << "   ";
  for( int i=0; i<(int)clique.size(); i++ ){
    Debug("uf-ss") << clique[i] << " ";
  }
  Debug("uf-ss") << std::endl;
  Debug("uf-ss") << "Finding clique disequalities..." << std::endl;
  std::vector< Node > conflict;
  //collect disequalities, and nodes that must be equal within representatives
  std::map< Node, std::map< Node, bool > > explained;
  std::map< Node, std::map< Node, bool > > nodesWithinRep;
  for( int i=0; i<(int)d_disequalities_index; i++ ){
    //if both sides of disequality exist in clique
    Node r1 = d_th->d_equalityEngine.getRepresentative( d_disequalities[i][0][0] );
    Node r2 = d_th->d_equalityEngine.getRepresentative( d_disequalities[i][0][1] );
    if( r1!=r2 && ( explained.find( r1 )==explained.end() || explained[r1].find( r2 )==explained[r1].end() ) &&
        std::find( clique.begin(), clique.end(), r1 )!=clique.end() &&
        std::find( clique.begin(), clique.end(), r2 )!=clique.end() ){
      explained[r1][r2] = true;
      explained[r2][r1] = true;
      conflict.push_back( d_disequalities[i] );
      nodesWithinRep[r1][ d_disequalities[i][0][0] ] = true;
      nodesWithinRep[r2][ d_disequalities[i][0][1] ] = true;
      if( conflict.size()==(clique.size()*( clique.size()-1 )/2) ){
        break;
      }
    }
  }
  //Debug("uf-ss") << conflict.size() << " " << clique.size() << std::endl;
  Assert( (int)conflict.size()==((int)clique.size()*( (int)clique.size()-1 )/2) );
  //Assert( (int)conflict.size()==(int)clique.size()*( (int)clique.size()-1 )/2 );
  Debug("uf-ss") << "Finding clique equalities internal to eq classes..." << std::endl;
  //now, we must explain equalities within each equivalence class
  for( std::map< Node, std::map< Node, bool > >::iterator it = nodesWithinRep.begin(); it != nodesWithinRep.end(); ++it ){
    if( it->second.size()>1 ){
      Node prev;
      //add explanation of t1 = t2 = ... = tn
      for( std::map< Node, bool >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
        if( prev!=Node::null() ){
          //explain it2->first and prev
          std::vector< TNode > expl;
          d_th->d_equalityEngine.explainEquality( it2->first, prev, true, expl );
          for( int i=0; i<(int)expl.size(); i++ ){
            if( std::find( conflict.begin(), conflict.end(), expl[i] )==conflict.end() ){
              conflict.push_back( expl[i] );
            }
          }
        }
        prev = it2->first;
      }
    }
  }
  Debug("uf-ss") << "Explanation of clique (size=" << conflict.size() << ") = " << std::endl;
  for( int i=0; i<(int)conflict.size(); i++ ){
    Debug("uf-ss") << conflict[i] << " ";
  }
  Debug("uf-ss") << std::endl;
  //now, make the conflict
  Node conflictNode = conflict.size()==1 ? conflict[0] : NodeManager::currentNM()->mkNode( AND, conflict );
  //add cardinality constraint
  //Node cardNode = NodeManager::currentNM()->mkNode( CARDINALITY_CONSTRAINT, d_cardinality_lemma_term,
  //                                                  NodeManager::currentNM()->mkConst( Rational(d_cardinality) ) );
  Node cardNode = d_cardinality_literal[ d_cardinality ];
  conflictNode = NodeManager::currentNM()->mkNode( IMPLIES, conflictNode, cardNode.notNode() );
  Debug("uf-ss-lemma") << "*** Add clique conflict " << conflictNode << std::endl;
  //Notice() << "*** Add clique conflict " << conflictNode << std::endl;
  out->lemma( conflictNode );
  ++( d_th->getStrongSolver()->d_statistics.d_clique_lemmas );

  //DO_THIS: ensure that the same clique is not reported???  Check standard effort after assertDisequal can produce same clique.
}

/** new node */
void StrongSolverTheoryUf::ConflictFind::newEqClass( Node n ){
  if( d_regions_map.find( n )==d_regions_map.end() ){
    if( !Options::current()->ufssRegions ){
      //if not using regions, always add new equivalence classes to region index = 0
      d_regions_index = 0;
    }
    d_regions_map[n] = d_regions_index;
    Debug("uf-ss") << "StrongSolverTheoryUf: New Eq Class " << n << std::endl;
    Debug("uf-ss-debug") << d_regions_index << " " << (int)d_regions.size() << std::endl;
    if( d_regions_index<d_regions.size() ){
      d_regions[ d_regions_index ]->debugPrint("uf-ss-debug",true);
      d_regions[ d_regions_index ]->d_valid = true;
      Assert( !Options::current()->ufssRegions || d_regions[ d_regions_index ]->getNumReps()==0 );
    }else{
      d_regions.push_back( new Region( this, d_th->getSatContext() ) );
    }
    d_regions[ d_regions_index ]->addRep( n );
    d_regions_index = d_regions_index + 1;
    d_reps = d_reps + 1;
  }
}

/** merge */
void StrongSolverTheoryUf::ConflictFind::merge( Node a, Node b ){
  //Assert( a==d_th->d_equalityEngine.getRepresentative( a ) );
  //Assert( b==d_th->d_equalityEngine.getRepresentative( b ) );
  Debug("uf-ss") << "StrongSolverTheoryUf: Merging " << a << " = " << b << "..." << std::endl;
  if( a!=b ){
    Assert( d_regions_map.find( a )!=d_regions_map.end() );
    Assert( d_regions_map.find( b )!=d_regions_map.end() );
    int ai = d_regions_map[a];
    int bi = d_regions_map[b];
    Debug("uf-ss") << "   regions: " << ai << " " << bi << std::endl;
    if( ai!=bi ){
      if( d_regions[ai]->getNumReps()==1  ){
        int ri = combineRegions( bi, ai );
        d_regions[ri]->setEqual( a, b );
        checkRegion( ri );
      }else if( d_regions[bi]->getNumReps()==1 ){
        int ri = combineRegions( ai, bi );
        d_regions[ri]->setEqual( a, b );
        checkRegion( ri );
      }else{
        // either move a to d_regions[bi], or b to d_regions[ai]
        int aex = d_regions[ai]->d_nodes[a]->getNumInternalDisequalities() - getNumDisequalitiesToRegion( a, bi );
        int bex = d_regions[bi]->d_nodes[b]->getNumInternalDisequalities() - getNumDisequalitiesToRegion( b, ai );
        //based on which would produce the fewest number of external disequalities
        if( aex<bex ){
          moveNode( a, bi );
          d_regions[bi]->setEqual( a, b );
        }else{
          moveNode( b, ai );
          d_regions[ai]->setEqual( a, b );
        }
        checkRegion( ai );
        checkRegion( bi );
      }
    }else{
      d_regions[ai]->setEqual( a, b );
      checkRegion( ai );
    }
    d_reps = d_reps - 1;
    d_regions_map[b] = -1;
  }
  Debug("uf-ss") << "Done merge." << std::endl;
}

/** assert terms are disequal */
void StrongSolverTheoryUf::ConflictFind::assertDisequal( Node a, Node b, Node reason ){
  //if they are not already disequal
  a = d_th->d_equalityEngine.getRepresentative( a );
  b = d_th->d_equalityEngine.getRepresentative( b );
  if( !d_th->d_equalityEngine.areDisequal( a, b, true ) ){
    Debug("uf-ss") << "Assert disequal " << a << " != " << b << "..." << std::endl;
    //if( reason.getKind()!=NOT || ( reason[0].getKind()!=EQUAL && reason[0].getKind()!=IFF ) ||
    //    a!=reason[0][0] || b!=reason[0][1] ){
    //  Notice() << "Assert disequal " << a << " != " << b << ", reason = " << reason << "..." << std::endl;
    //}
    Debug("uf-ss-disequal") << "Assert disequal " << a << " != " << b << "..." << std::endl;
    //add to list of disequalities
    if( d_disequalities_index<d_disequalities.size() ){
      d_disequalities[d_disequalities_index] = reason;
    }else{
      d_disequalities.push_back( reason );
    }
    d_disequalities_index = d_disequalities_index + 1;
    //now, add disequalities to regions
    Assert( d_regions_map.find( a )!=d_regions_map.end() );
    Assert( d_regions_map.find( b )!=d_regions_map.end() );
    int ai = d_regions_map[a];
    int bi = d_regions_map[b];
    Debug("uf-ss") << "   regions: " << ai << " " << bi << std::endl;
    if( ai==bi ){
      //internal disequality
      d_regions[ai]->setDisequal( a, b, 1, true );
      d_regions[ai]->setDisequal( b, a, 1, true );
    }else{
      //external disequality
      d_regions[ai]->setDisequal( a, b, 0, true );
      d_regions[bi]->setDisequal( b, a, 0, true );
      checkRegion( ai );
      checkRegion( bi );
    }
    //Notice() << "done" << std::endl;
  }
}

void StrongSolverTheoryUf::ConflictFind::assertCardinality( int c, bool val ){
  Assert( d_cardinality_literal.find( c )!=d_cardinality_literal.end() );
  d_cardinality_assertions[ d_cardinality_literal[c] ] = val;
  if( val ){
    d_hasCard = true;
  }
}

void StrongSolverTheoryUf::ConflictFind::checkRegion( int ri, bool rec ){
  if( isValid(ri) ){
    Assert( d_cardinality>0 );
    //first check if region is in conflict
    std::vector< Node > clique;
    if( d_regions[ri]->check( Theory::EFFORT_STANDARD, d_cardinality, clique ) ){
      //explain clique
      explainClique( clique, &d_th->getOutputChannel() );
    }else if( d_regions[ri]->getMustCombine( d_cardinality ) ){
      ////alternatively, check if we can reduce the number of external disequalities by moving single nodes
      //for( std::map< Node, bool >::iterator it = d_regions[i]->d_reps.begin(); it != d_regions[i]->d_reps.end(); ++it ){
      //  if( it->second ){
      //    int inDeg = d_regions[i]->d_disequalities_size[1][ it-> first ];
      //    int outDeg = d_regions[i]->d_disequalities_size[0][ it-> first ];
      //    if( inDeg<outDeg ){
      //    }
      //  }
      //}
      int riNew = forceCombineRegion( ri, true );
      if( riNew>=0 && rec ){
        checkRegion( riNew, rec );
      }
    }
  }
}

int StrongSolverTheoryUf::ConflictFind::forceCombineRegion( int ri, bool useDensity ){
  if( !useDensity ){
    for( int i=0; i<(int)d_regions_index; i++ ){
      if( ri!=i && d_regions[i]->d_valid ){
        return combineRegions( ri, i );
      }
    }
    return -1;
  }else{
    //this region must merge with another
    Debug("uf-ss-check-region") << "We must combine Region #" << ri << ". " << std::endl;
    d_regions[ri]->debugPrint("uf-ss-check-region");
    //take region with maximum disequality density
    double maxScore = 0;
    int maxRegion = -1;
    std::map< int, int > regions_diseq;
    getDisequalitiesToRegions( ri, regions_diseq );
    for( std::map< int, int >::iterator it = regions_diseq.begin(); it != regions_diseq.end(); ++it ){
      Debug("uf-ss-check-region") << it->first << " : " << it->second << std::endl;
    }
    for( std::map< int, int >::iterator it = regions_diseq.begin(); it != regions_diseq.end(); ++it ){
      Assert( it->first!=ri );
      Assert( isValid( it->first ) );
      Assert( d_regions[ it->first ]->getNumReps()>0 );
      double tempScore = double(it->second)/double(d_regions[it->first]->getNumReps() );
      if( tempScore>maxScore ){
        maxRegion = it->first;
        maxScore = tempScore;
      }
    }
    if( maxRegion!=-1 ){
      Debug("uf-ss-check-region") << "Combine with region #" << maxRegion << ":" << std::endl;
      d_regions[maxRegion]->debugPrint("uf-ss-check-region");
      return combineRegions( ri, maxRegion );
    }
    return -1;
  }
}


int StrongSolverTheoryUf::ConflictFind::combineRegions( int ai, int bi ){
#ifdef COMBINE_REGIONS_SMALL_INTO_LARGE
  if( d_regions[ai]->getNumReps()<d_regions[bi]->getNumReps() ){
    return combineRegions( bi, ai );
  }
#endif
  Debug("uf-ss-region") << "uf-ss: Combine Region #" << bi << " with Region #" << ai << std::endl;
  Assert( isValid( ai ) && isValid( bi ) );
  for( std::map< Node, Region::RegionNodeInfo* >::iterator it = d_regions[bi]->d_nodes.begin(); it != d_regions[bi]->d_nodes.end(); ++it ){
    Region::RegionNodeInfo* rni = it->second;
    if( rni->d_valid ){
      d_regions_map[ it->first ] = ai;
    }
  }
  //update regions disequal DO_THIS?
  d_regions[ai]->combine( d_regions[bi] );
  d_regions[bi]->d_valid = false;
  return ai;
}

void StrongSolverTheoryUf::ConflictFind::moveNode( Node n, int ri ){
  Debug("uf-ss-region") << "uf-ss: Move node " << n << " to Region #" << ri << std::endl;
  Assert( isValid( d_regions_map[ n ] ) );
  Assert( isValid( ri ) );
  //move node to region ri
  d_regions[ri]->takeNode( d_regions[ d_regions_map[n] ], n );
  d_regions_map[n] = ri;
}

bool StrongSolverTheoryUf::ConflictFind::disambiguateTerms( OutputChannel* out ){
  Debug("uf-ss-disamb") << "Disambiguate terms." << std::endl;
  bool lemmaAdded = false;
  //otherwise, determine ambiguous pairs of ground terms for relevant sorts
  quantifiers::TermDb* db = d_th->getQuantifiersEngine()->getTermDatabase();
  for( std::map< Node, std::vector< Node > >::iterator it = db->d_op_map.begin(); it != db->d_op_map.end(); ++it ){
    Debug("uf-ss-disamb") << "Check " << it->first << std::endl;
    if( it->second.size()>1 ){
      if( StrongSolverTheoryUf::involvesRelevantType( it->second[0] ) ){
        for( int i=0; i<(int)it->second.size(); i++ ){
          for( int j=(i+1); j<(int)it->second.size(); j++ ){
            Kind knd = it->second[i].getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
            Node eq = NodeManager::currentNM()->mkNode( knd, it->second[i], it->second[j] );
            eq = Rewriter::rewrite(eq);
            //determine if they are ambiguous
            if( d_term_amb.find( eq )==d_term_amb.end() ){
              Debug("uf-ss-disamb") << "Check disambiguate " << it->second[i] << " " << it->second[j] << std::endl;
              d_term_amb[ eq ] = true;
              //if they are equal
              if( d_th->d_equalityEngine.areEqual( it->second[i], it->second[j] ) ){
                d_term_amb[ eq ] = false;
              }else{
                //if an argument is disequal, then they are not ambiguous
                for( int k=0; k<(int)it->second[i].getNumChildren(); k++ ){
                  if( d_th->d_equalityEngine.areDisequal( it->second[i][k], it->second[j][k], true ) ){
                    d_term_amb[ eq ] = false;
                    break;
                  }
                }
              }
              if( d_term_amb[ eq ] ){
                Debug("uf-ss-disamb") << "Disambiguate " << it->second[i] << " " << it->second[j] << std::endl;
                //must add lemma
                std::vector< Node > children;
                children.push_back( eq );
                for( int k=0; k<(int)it->second[i].getNumChildren(); k++ ){
                  Kind knd2 = it->second[i][k].getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
                  Node eqc = NodeManager::currentNM()->mkNode( knd2, it->second[i][k], it->second[j][k] );
                  children.push_back( eqc.notNode() );
                }
                Assert( children.size()>1 );
                Node lem = NodeManager::currentNM()->mkNode( OR, children );
                Debug( "uf-ss-lemma" ) << "*** Disambiguate lemma : " << lem << std::endl;
                //Notice() << "*** Disambiguate lemma : " << lem << std::endl;
                out->lemma( lem );
                d_term_amb[ eq ] = false;
                lemmaAdded = true;
                ++( d_th->getStrongSolver()->d_statistics.d_disamb_term_lemmas );
              }
            }
          }
        }
      }
    }
  }
  Debug("uf-ss-disamb") << "Done disambiguate terms. " << lemmaAdded << std::endl;
  return lemmaAdded;
}

/** check */
void StrongSolverTheoryUf::ConflictFind::check( Theory::Effort level, OutputChannel* out ){
  if( level>=Theory::EFFORT_STANDARD ){
    Assert( d_cardinality>0 );
    Debug("uf-ss") << "StrongSolverTheoryUf: Check " << level << " " << d_type << std::endl;
    //Notice() << "StrongSolverTheoryUf: Check " << level << std::endl;
    if( d_reps<=(unsigned)d_cardinality ){
      Debug("uf-ss-debug") << "We have " << d_reps << " representatives for type " << d_type << ", <= " << d_cardinality << std::endl;
      if( level==Theory::EFFORT_FULL ){
        Debug("uf-ss-sat") << "We have " << d_reps << " representatives for type " << d_type << ", <= " << d_cardinality << std::endl;
        //Notice() << "We have " << d_reps << " representatives for type " << d_type << ", <= " << cardinality << std::endl;
        //Notice() << "Model size for " << d_type << " is " << cardinality << std::endl;
        //Notice() << cardinality << " ";
      }
      return;
    }else{
      //do a check within each region
      for( int i=0; i<(int)d_regions_index; i++ ){
        if( d_regions[i]->d_valid ){
          std::vector< Node > clique;
          if( d_regions[i]->check( level, d_cardinality, clique ) ){
            //explain clique
            explainClique( clique, out );
            return;
          }else{
            Debug("uf-ss-debug") << "No clique in Region #" << i << std::endl;
          }
        }
      }
      bool addedLemma = false;
      //do splitting on demand
      if( level==Theory::EFFORT_FULL || Options::current()->ufssEagerSplits ){
        Debug("uf-ss-debug") << "Add splits?" << std::endl;
        //see if we have any recommended splits from large regions
        for( int i=0; i<(int)d_regions_index; i++ ){
          if( d_regions[i]->d_valid && d_regions[i]->getNumReps()>d_cardinality ){
            if( d_regions[i]->hasSplits() ){
              d_regions[i]->addSplit( out );
              addedLemma = true;
              ++( d_th->getStrongSolver()->d_statistics.d_split_lemmas );
#ifdef ONE_SPLIT_REGION
              break;
#endif
            }
          }
        }
      }
      //force continuation via term disambiguation or combination of regions
      if( level==Theory::EFFORT_FULL ){
        if( !addedLemma ){
          Debug("uf-ss") << "No splits added." << std::endl;
          if( Options::current()->ufssColoringSat ){
            //otherwise, try to disambiguate individual terms
            if( !disambiguateTerms( out ) ){
              //no disequalities can be propagated
              //we are in a situation where it suffices to apply a coloring to equivalence classes
              //due to our invariants, we know no coloring conflicts will occur between regions, and thus
              //  we are SAT in this case.
              Debug("uf-ss-sat") << "SAT: regions = " << getNumRegions() << std::endl;
              //Notice() << "Model size for " << d_type << " is " << cardinality << ", regions = " << getNumRegions() << std::endl;
              debugPrint("uf-ss-sat");
            }
          }else{
            bool recheck = false;
            //naive strategy, force region combination involving the first valid region
            for( int i=0; i<(int)d_regions_index; i++ ){
              if( d_regions[i]->d_valid ){
                forceCombineRegion( i, false );
                recheck = true;
                break;
              }
            }
            if( recheck ){
              check( level, out );
            }
          }
        }
      }
    }
  }
}

void StrongSolverTheoryUf::ConflictFind::propagate( Theory::Effort level, OutputChannel* out ){
  Assert( d_cardinality>0 );
  //propagate the current cardinality as a decision literal, if not already asserted
  Node cn = d_cardinality_literal[ d_cardinality ];
  Debug("uf-ss-prop-as-dec") << "Propagate as decision " << d_type << ", cardinality = " << d_cardinality << std::endl;
  Assert( !cn.isNull() );
  if( d_cardinality_assertions.find( cn )==d_cardinality_assertions.end() ){
    out->propagateAsDecision( d_cardinality_literal[ d_cardinality ] );
    Debug("uf-ss-prop-as-dec") << "Propagate as decision " << d_cardinality_literal[ d_cardinality ];
    Debug("uf-ss-prop-as-dec") << " " << d_cardinality_literal[ d_cardinality ][0].getType() << std::endl;
  }
}

void StrongSolverTheoryUf::ConflictFind::debugPrint( const char* c ){
  Debug( c ) << "--  Conflict Find:" << std::endl;
  Debug( c ) << "Number of reps = " << d_reps << std::endl;
  Debug( c ) << "Cardinality req = " << d_cardinality << std::endl;
  unsigned debugReps = 0;
  for( int i=0; i<(int)d_regions_index; i++ ){
    if( d_regions[i]->d_valid ){
      Debug( c ) << "Region #" << i << ": " << std::endl;
      d_regions[i]->debugPrint( c, true );
      Debug( c ) << std::endl;
      for( std::map< Node, Region::RegionNodeInfo* >::iterator it = d_regions[i]->d_nodes.begin(); it != d_regions[i]->d_nodes.end(); ++it ){
        if( it->second->d_valid ){
          if( d_regions_map[ it->first ]!=i ){
            Debug( c ) << "***Bad regions map : " << it->first << " " << d_regions_map[ it->first ].get() << std::endl;
          }
        }
      }
      debugReps += d_regions[i]->getNumReps();
    }
  }
  if( debugReps!=d_reps ){
    Debug( c ) << "***Bad reps: " << d_reps << ", actual = " << debugReps << std::endl;
  }
}

int StrongSolverTheoryUf::ConflictFind::getNumRegions(){
  int count = 0;
  for( int i=0; i<(int)d_regions_index; i++ ){
    if( d_regions[i]->d_valid ){
      count++;
    }
  }
  return count;
}

void StrongSolverTheoryUf::ConflictFind::setCardinality( int c, OutputChannel* out ){
  d_cardinality = c;
  //add appropriate lemma
  Node lem = getCardinalityLemma();
  out->lemma( lem );
  //add the appropriate lemma
  Debug("uf-ss-fmf") << "Set cardinality " << d_type << " = " << c << std::endl;
  Debug("uf-ss-prop-as-dec") << "Propagate as decision " << lem[0] << std::endl;
  out->propagateAsDecision( lem[0] );
  d_is_cardinality_requested = true;
  d_is_cardinality_requested_c = true;
  //now, require old literal to be decided false
  //if( d_cardinality_literal.find( c-1 )!=d_cardinality_literal.end() ){
  //  Debug("uf-ss-req-phase") << "Require phase " << d_cardinality_literal[c-1] << " = false " << std::endl;
  //  out->requirePhase( d_cardinality_literal[c-1], false );
  //}
}

void StrongSolverTheoryUf::ConflictFind::getRepresentatives( std::vector< Node >& reps ){
  if( !Options::current()->ufssColoringSat ){
    bool foundRegion = false;
    for( int i=0; i<(int)d_regions_index; i++ ){
      //should not have multiple regions at this point
      if( foundRegion ){
        Assert( !d_regions[i]->d_valid );
      }
      if( d_regions[i]->d_valid ){
        //this is the only valid region
        d_regions[i]->getRepresentatives( reps );
        foundRegion = true;
      }
    }
  }else{
    Unimplemented("Build representatives for fmf region sat is not implemented");
  }
}

bool StrongSolverTheoryUf::ConflictFind::minimize( OutputChannel* out ){
  //ensure that model forms a clique:
  // if two equivalence classes are neither equal nor disequal, add a split
  int validRegionIndex = -1;
  for( int i=0; i<(int)d_regions_index; i++ ){
    if( d_regions[i]->d_valid ){
      if( validRegionIndex!=-1 ){
        combineRegions( validRegionIndex, i );
        if( !d_regions[validRegionIndex]->minimize( out ) ){
          return false;
        }
      }else{
        validRegionIndex = i;
      }
    }
  }
  if( !d_regions[validRegionIndex]->minimize( out ) ){
    return false;
  }
  return true;
}


Node StrongSolverTheoryUf::ConflictFind::getCardinalityLemma(){
  if( d_cardinality_lemma.find( d_cardinality )==d_cardinality_lemma.end() ){
    if( d_cardinality_lemma_term.isNull() ){
      std::stringstream ss;
      ss << Expr::setlanguage(Options::current()->outputLanguage);
      ss << "t_" << d_type;
      d_cardinality_lemma_term = NodeManager::currentNM()->mkVar( ss.str(), d_type );
    }
    Node lem = NodeManager::currentNM()->mkNode( CARDINALITY_CONSTRAINT, d_cardinality_lemma_term,
                                  NodeManager::currentNM()->mkConst( Rational( d_cardinality ) ) );
    lem = Rewriter::rewrite(lem);
    d_cardinality_literal[ d_cardinality ] = lem;
    lem = NodeManager::currentNM()->mkNode( OR, lem, lem.notNode() );
    d_cardinality_lemma[ d_cardinality ] = lem;
  }
  return d_cardinality_lemma[ d_cardinality ];
}

StrongSolverTheoryUf::StrongSolverTheoryUf(context::Context* c, context::UserContext* u, OutputChannel& out, TheoryUF* th) :
d_out( &out ),
d_th( th ),
d_conf_find(),
d_conf_types(),
d_conf_find_init( c )
{

}

/** new node */
void StrongSolverTheoryUf::newEqClass( Node n ){
  TypeNode tn = n.getType();
  ConflictFind* c = getConflictFind( tn );
  if( c ){
    Debug("uf-ss-solver") << "StrongSolverTheoryUf: New eq class " << n << " " << tn << std::endl;
    c->newEqClass( n );
  }
  //else if( isRelevantType( tn ) ){
  //  //Debug("uf-ss-solver") << "WAIT: StrongSolverTheoryUf: New eq class " << n << " " << tn << std::endl;
  //  //d_new_eq_class_waiting[tn].push_back( n );
  //}
}

/** merge */
void StrongSolverTheoryUf::merge( Node a, Node b ){
  TypeNode tn = a.getType();
  ConflictFind* c = getConflictFind( tn );
  if( c ){
    Debug("uf-ss-solver") << "StrongSolverTheoryUf: Merge " << a << " " << b << " " << tn << std::endl;
    c->merge( a, b );
  }
}

/** assert terms are disequal */
void StrongSolverTheoryUf::assertDisequal( Node a, Node b, Node reason ){
  TypeNode tn = a.getType();
  ConflictFind* c = getConflictFind( tn );
  if( c ){
    Debug("uf-ss-solver") << "StrongSolverTheoryUf: Assert disequal " << a << " " << b << " " << tn << std::endl;
    //Assert( d_th->d_equalityEngine.getRepresentative( a )==a );
    //Assert( d_th->d_equalityEngine.getRepresentative( b )==b );
    c->assertDisequal( a, b, reason );
  }
}

/** assert a node */
void StrongSolverTheoryUf::assertNode( Node n, bool isDecision ){
  Debug("uf-ss-assert") << "Assert " << n << " " << isDecision << std::endl;
  if( n.getKind()==CARDINALITY_CONSTRAINT ){
    TypeNode tn = n[0].getType();
    Assert( d_conf_find[tn]->getCardinality()>0 );
    Assert( isRelevantType( tn ) );
    Assert( d_conf_find[tn] );
    long nCard = n[1].getConst<Rational>().getNumerator().getLong();
    d_conf_find[tn]->assertCardinality( nCard, true );
    if( nCard==d_conf_find[tn]->getCardinality() ){
      d_conf_find[tn]->d_is_cardinality_set = true;
      d_conf_find[tn]->d_is_cardinality_requested = false;
      d_conf_find[tn]->d_is_cardinality_requested_c = false;
    }
  }else if( n.getKind()==NOT && n[0].getKind()==CARDINALITY_CONSTRAINT ){
    //must add new lemma
    Node nn = n[0];
    TypeNode tn = nn[0].getType();
    Assert( isRelevantType( tn ) );
    Assert( d_conf_find[tn] );
    long nCard = nn[1].getConst<Rational>().getNumerator().getLong();
    d_conf_find[tn]->assertCardinality( nCard, false );
    if( nCard==d_conf_find[tn]->getCardinality() ){
      AlwaysAssert(!isDecision, "Error: Negative cardinality node decided upon");
      Debug("uf-ss-fmf") << "No model of size " << d_conf_find[tn]->getCardinality() << " exists for type " << tn << std::endl;
      //Notice() << "No model of size " << d_conf_find[tn]->getCardinality() << " exists for type " << tn << std::endl;
      //increment to next cardinality
      d_statistics.d_max_model_size.maxAssign( d_conf_find[tn]->getCardinality() + 1 );
      d_conf_find[tn]->setCardinality( d_conf_find[tn]->getCardinality() + 1, d_out );
      //Notice() << d_conf_find[tn]->getCardinality() << " ";
      ////give up permanently on this cardinality
      //d_out->lemma( n );
    }
  }else{
    ////FIXME: this is too strict: theory propagations are showing up as isDecision=true, but
    ////       a theory propagation is not a decision.
    //if( isDecision ){
    //  for( std::map< TypeNode, ConflictFind* >::iterator it = d_conf_find.begin(); it != d_conf_find.end(); ++it ){
    //    if( !it->second->hasCardinalityAsserted() ){
    //      Notice() << "Assert " << n << " " << isDecision << std::endl;
    //      Notice() << "Error: constraint asserted before cardinality for " << it->first << std::endl;
    //      Unimplemented();
    //    }
    //  }
    //}
  }
}


/** check */
void StrongSolverTheoryUf::check( Theory::Effort level ){
  Debug("uf-ss-solver") << "StrongSolverTheoryUf: check " << level << std::endl;
  if( level==Theory::EFFORT_FULL ){
    debugPrint( "uf-ss-debug" );
  }
  for( std::map< TypeNode, ConflictFind* >::iterator it = d_conf_find.begin(); it != d_conf_find.end(); ++it ){
    it->second->check( level, d_out );
  }
  Debug("uf-ss-solver") << "Done StrongSolverTheoryUf: check " << level << std::endl;
}

/** propagate */
void StrongSolverTheoryUf::propagate( Theory::Effort level ){
  for( std::map< TypeNode, ConflictFind* >::iterator it = d_conf_find.begin(); it != d_conf_find.end(); ++it ){
    it->second->propagate( level, d_out );
  }
}

void StrongSolverTheoryUf::preRegisterTerm( TNode n ){
  //shouldn't have to preregister this type (it may be that there are no quantifiers over tn)  FIXME
  TypeNode tn = n.getType();
  if( isRelevantType( tn ) ){
    preRegisterType( tn );
  }
}

void StrongSolverTheoryUf::registerQuantifier( Node f ){
  Debug("uf-ss-register") << "Register quantifier " << f << std::endl;
  //must ensure the quantifier does not quantify over arithmetic
  for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
    TypeNode tn = f[0][i].getType();
    if( isRelevantType( tn ) ){
      preRegisterType( tn );
    }else{
      if( tn==NodeManager::currentNM()->integerType() || tn==NodeManager::currentNM()->realType() ){
        Debug("uf-ss-na") << "Error: Cannot perform finite model finding on arithmetic quantifier";
        Debug("uf-ss-na") << " (" << f << ")";
        Debug("uf-ss-na") << std::endl;
        Unimplemented("Cannot perform finite model finding on arithmetic quantifier");
      }else if( tn.isDatatype() ){
        Debug("uf-ss-na") << "Error: Cannot perform finite model finding on datatype quantifier";
        Debug("uf-ss-na") << " (" << f << ")";
        Debug("uf-ss-na") << std::endl;
        Unimplemented("Cannot perform finite model finding on datatype quantifier");
      }
    }
  }
}

void StrongSolverTheoryUf::preRegisterType( TypeNode tn ){
  if( d_conf_find.find( tn )==d_conf_find.end() ){
    Debug("uf-ss-register") << "Preregister " << tn << "." << std::endl;
    //enter into incremental finite model finding mode: try cardinality = 1 first
    //if( !d_conf_types.empty() ){
    //  Debug("uf-ss-na") << "Strong solver unimplemented for multiple sorts." << std::endl;
    //  Unimplemented();
    //}
    d_conf_find[tn] = new ConflictFind( tn, d_th->getSatContext(), d_th );
    //assign cardinality restriction
    d_statistics.d_max_model_size.maxAssign( 1 );
    d_conf_find[tn]->setCardinality( 1, d_out );
    ////add waiting equivalence classes now
    //if( !d_new_eq_class_waiting[tn].empty() ){
    //  Debug("uf-ss-register") << "Add " << (int)d_new_eq_class_waiting[tn].size() << " new eq classes." << std::endl;
    //  for( int i=0; i<(int)d_new_eq_class_waiting[tn].size(); i++ ){
    //    newEqClass( d_new_eq_class_waiting[tn][i] );
    //  }
    //  d_new_eq_class_waiting[tn].clear();
    //}
    d_conf_types.push_back( tn );
  }
}

StrongSolverTheoryUf::ConflictFind* StrongSolverTheoryUf::getConflictFind( TypeNode tn ){
  std::map< TypeNode, ConflictFind* >::iterator it = d_conf_find.find( tn );
  //pre-register the type if not done already
  if( it==d_conf_find.end() ){
    if( isRelevantType( tn ) ){
      preRegisterType( tn );
      it = d_conf_find.find( tn );
    }
  }
  if( it!=d_conf_find.end() ){
    //initialize the type if necessary
    if( d_conf_find_init.find( tn )==d_conf_find_init.end() ){
      //assign cardinality restriction
      d_statistics.d_max_model_size.maxAssign( 1 );
      it->second->setCardinality( 1, d_out );
      d_conf_find_init[tn] = true;
    }
    return it->second;
  }else{
    return NULL;
  }
}

void StrongSolverTheoryUf::notifyRestart(){
  Debug("uf-ss-prop-as-dec") << "Restart?" << std::endl;
}

/** get cardinality for sort */
int StrongSolverTheoryUf::getCardinality( TypeNode t ) {
  ConflictFind* c = getConflictFind( t );
  if( c ){
    return c->getCardinality();
  }else{
    return -1;
  }
}

void StrongSolverTheoryUf::getRepresentatives( TypeNode t, std::vector< Node >& reps ){
  ConflictFind* c = getConflictFind( t );
  if( c ){
    c->getRepresentatives( reps );
  }
}

//Node StrongSolverTheoryUf::getCardinalityTerm( TypeNode t ){
//  ConflictFind* c = getConflictFind( t );
//  if( c ){
//    return c->getCardinalityTerm();
//  }else{
//    return Node::null();
//  }
//}

bool StrongSolverTheoryUf::minimize(){
  for( std::map< TypeNode, ConflictFind* >::iterator it = d_conf_find.begin(); it != d_conf_find.end(); ++it ){
    if( !it->second->minimize( d_out ) ){
      return false;
    }
  }
  return true;
}

//print debug
void StrongSolverTheoryUf::debugPrint( const char* c ){
  //EqClassesIterator< TheoryUF::NotifyClass > eqc_iter( &((TheoryUF*)d_th)->d_equalityEngine );
  //while( !eqc_iter.isFinished() ){
  //  Debug( c ) << "Eq class [[" << (*eqc_iter) << "]]" << std::endl;
  //  EqClassIterator< TheoryUF::NotifyClass > eqc_iter2( *eqc_iter, &((TheoryUF*)d_th)->d_equalityEngine );
  //  Debug( c ) << "   ";
  //  while( !eqc_iter2.isFinished() ){
  //    Debug( c ) << "[" << (*eqc_iter2) << "] ";
  //    eqc_iter2++;
  //  }
  //  Debug( c ) << std::endl;
  //  eqc_iter++;
  //}

  for( std::map< TypeNode, ConflictFind* >::iterator it = d_conf_find.begin(); it != d_conf_find.end(); ++it ){
    Debug( c ) << "Conflict find structure for " << it->first << ": " << std::endl;
    it->second->debugPrint( c );
    Debug( c ) << std::endl;
  }
}

StrongSolverTheoryUf::Statistics::Statistics():
  d_clique_lemmas("StrongSolverTheoryUf::Clique_Lemmas", 0),
  d_split_lemmas("StrongSolverTheoryUf::Split_Lemmas", 0),
  d_disamb_term_lemmas("StrongSolverTheoryUf::Disambiguate_Term_Lemmas", 0),
  d_max_model_size("StrongSolverTheoryUf::Max_Model_Size", 0)
{
  StatisticsRegistry::registerStat(&d_clique_lemmas);
  StatisticsRegistry::registerStat(&d_split_lemmas);
  StatisticsRegistry::registerStat(&d_disamb_term_lemmas);
  StatisticsRegistry::registerStat(&d_max_model_size);
}

StrongSolverTheoryUf::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_clique_lemmas);
  StatisticsRegistry::unregisterStat(&d_split_lemmas);
  StatisticsRegistry::unregisterStat(&d_disamb_term_lemmas);
  StatisticsRegistry::unregisterStat(&d_max_model_size);
}

bool StrongSolverTheoryUf::isRelevantType( TypeNode t ){
  return t!=NodeManager::currentNM()->booleanType() &&
         t!=NodeManager::currentNM()->integerType() &&
         t!=NodeManager::currentNM()->realType() &&
         t!=NodeManager::currentNM()->builtinOperatorType() &&
         !t.isFunction() &&
         !t.isDatatype() &&
         !t.isArray();
}

bool StrongSolverTheoryUf::involvesRelevantType( Node n ){
  if( n.getKind()==APPLY_UF ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( isRelevantType( n[i].getType() ) ){
        return true;
      }
    }
  }
  return false;
}
