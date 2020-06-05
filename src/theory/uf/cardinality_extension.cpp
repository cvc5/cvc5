/*********************                                                        */
/*! \file cardinality_extension.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of theory of UF with cardinality.
 **/

#include "theory/uf/cardinality_extension.h"

#include "options/uf_options.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/term_database.h"
#include "theory/theory_model.h"

//#define ONE_SPLIT_REGION
//#define COMBINE_REGIONS_SMALL_INTO_LARGE
//#define LAZY_REL_EQC

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;


namespace CVC4 {
namespace theory {
namespace uf {

/* These are names are unambigious are we use abbreviations. */
typedef CardinalityExtension::SortModel SortModel;
typedef SortModel::Region Region;
typedef Region::RegionNodeInfo RegionNodeInfo;
typedef RegionNodeInfo::DiseqList DiseqList;

Region::Region(SortModel* cf, context::Context* c)
  : d_cf( cf )
  , d_testCliqueSize( c, 0 )
  , d_splitsSize( c, 0 )
  , d_testClique( c )
  , d_splits( c )
  , d_reps_size( c, 0 )
  , d_total_diseq_external( c, 0 )
  , d_total_diseq_internal( c, 0 )
  , d_valid( c, true ) {}

Region::~Region() {
  for(iterator i = begin(), iend = end(); i != iend; ++i) {
    RegionNodeInfo* regionNodeInfo = (*i).second;
    delete regionNodeInfo;
  }
  d_nodes.clear();
}

void Region::addRep( Node n ) {
  setRep( n, true );
}

void Region::takeNode( Region* r, Node n ){
  Assert(!hasRep(n));
  Assert(r->hasRep(n));
  //add representative
  setRep( n, true );
  //take disequalities from r
  RegionNodeInfo* rni = r->d_nodes[n];
  for( int t=0; t<2; t++ ){
    DiseqList* del = rni->get(t);
    for(DiseqList::iterator it = del->begin(); it != del->end(); ++it ){
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

void Region::combine( Region* r ){
  //take all nodes from r
  for(Region::iterator it = r->d_nodes.begin(); it != r->d_nodes.end(); ++it) {
    if( it->second->valid() ){
      setRep( it->first, true );
    }
  }
  for(Region::iterator it = r->d_nodes.begin(); it != r->d_nodes.end(); ++it){
    if( it->second->valid() ){
      //take disequalities from r
      Node n = it->first;
      RegionNodeInfo* rni = it->second;
      for( int t=0; t<2; t++ ){
        RegionNodeInfo::DiseqList* del = rni->get(t);
        for( RegionNodeInfo::DiseqList::iterator it2 = del->begin(),
               it2end = del->end(); it2 != it2end; ++it2 ){
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
void Region::setEqual( Node a, Node b ){
  Assert(hasRep(a) && hasRep(b));
  //move disequalities of b over to a
  for( int t=0; t<2; t++ ){
    DiseqList* del = d_nodes[b]->get(t);
    for( DiseqList::iterator it = del->begin(); it != del->end(); ++it ){
      if( (*it).second ){
        Node n = (*it).first;
        //get the region that contains the endpoint of the disequality b != ...
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

void Region::setDisequal( Node n1, Node n2, int type, bool valid ){
  //Debug("uf-ss-region-debug") << "set disequal " << n1 << " " << n2 << " "
  //                            << type << " " << valid << std::endl;
  //debugPrint("uf-ss-region-debug");
  //Assert( isDisequal( n1, n2, type )!=valid );
  if( isDisequal( n1, n2, type )!=valid ){    //DO_THIS: make assertion
    d_nodes[ n1 ]->get(type)->setDisequal( n2, valid );
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
            Debug("uf-ss-debug") << "removing split for " << n1 << " " << n2
                                 << std::endl;
            d_splits[ eq ] = false;
            d_splitsSize = d_splitsSize - 1;
          }
        }
      }
    }
  }
}

void Region::setRep( Node n, bool valid ) {
  Assert(hasRep(n) != valid);
  if( valid && d_nodes.find( n )==d_nodes.end() ){
    d_nodes[n] = new RegionNodeInfo( d_cf->d_thss->getSatContext() );
  }
  d_nodes[n]->setValid(valid);
  d_reps_size = d_reps_size + ( valid ? 1 : -1 );
  //removing a member of the test clique from this region
  if( d_testClique.find( n ) != d_testClique.end() && d_testClique[n] ){
    Assert(!valid);
    d_testClique[n] = false;
    d_testCliqueSize = d_testCliqueSize - 1;
    //remove all splits involving n
    for( split_iterator it = begin_splits(); it != end_splits(); ++it ){
      if( (*it).second ){
        if( (*it).first[0]==n || (*it).first[1]==n ){
          d_splits[ (*it).first ] = false;
          d_splitsSize = d_splitsSize - 1;
        }
      }
    }
  }
}

bool Region::isDisequal( Node n1, Node n2, int type ) {
  RegionNodeInfo::DiseqList* del = d_nodes[ n1 ]->get(type);
  return del->isSet(n2) && del->getDisequalityValue(n2);
}

struct sortInternalDegree {
  Region* r;
  bool operator() (Node i, Node j) {
    return (r->getRegionInfo(i)->getNumInternalDisequalities() >
            r->getRegionInfo(j)->getNumInternalDisequalities());
  }
};

struct sortExternalDegree {
  Region* r;
  bool operator() (Node i,Node j) {
    return (r->getRegionInfo(i)->getNumExternalDisequalities() >
            r->getRegionInfo(j)->getNumExternalDisequalities());
  }
};

int gmcCount = 0;

bool Region::getMustCombine( int cardinality ){
  if (d_total_diseq_external >= static_cast<unsigned>(cardinality))
  {
    //The number of external disequalities is greater than or equal to
    //cardinality.  Thus, a clique of size cardinality+1 may exist
    //between nodes in d_regions[i] and other regions Check if this is
    //actually the case: must have n nodes with outgoing degree
    //(cardinality+1-n) for some n>0
    std::vector< int > degrees;
    for( Region::iterator it = begin(); it != end(); ++it ){
      RegionNodeInfo* rni = it->second;
      if( rni->valid() ){
        if( rni->getNumDisequalities() >= cardinality ){
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
    gmcCount++;
    if( gmcCount%100==0 ){
      Trace("gmc-count") << gmcCount << " " << cardinality
                         << " sample : " << degrees.size() << std::endl;
    }
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

bool Region::check( Theory::Effort level, int cardinality,
                    std::vector< Node >& clique ) {
  if( d_reps_size>unsigned(cardinality) ){
    if( d_total_diseq_internal==d_reps_size*( d_reps_size - 1 ) ){
      if( d_reps_size>1 ){
        //quick clique check, all reps form a clique
        for( iterator it = begin(); it != end(); ++it ){
          if( it->second->valid() ){
            clique.push_back( it->first );
          }
        }
        Trace("quick-clique") << "Found quick clique" << std::endl;
        return true;
      }else{
        return false;
      }
    }
    else if (level==Theory::EFFORT_FULL) 
    {
      //build test clique, up to size cardinality+1
      if( d_testCliqueSize<=unsigned(cardinality) ){
        std::vector< Node > newClique;
        if( d_testCliqueSize<unsigned(cardinality) ){
          for( iterator it = begin(); it != end(); ++it ){
            //if not in the test clique, add it to the set of new members
            if( it->second->valid() &&
                ( d_testClique.find( it->first ) == d_testClique.end() ||
                  !d_testClique[ it->first ] ) ){
              //if( it->second->getNumInternalDisequalities()>cardinality ||
              //    level==Theory::EFFORT_FULL ){
              newClique.push_back( it->first );
              //}
            }
          }
          //choose remaining nodes with the highest degrees
          sortInternalDegree sidObj;
          sidObj.r = this;
          std::sort( newClique.begin(), newClique.end(), sidObj );
          int offset = ( cardinality - d_testCliqueSize ) + 1;
          newClique.erase( newClique.begin() + offset, newClique.end() );
        }else{
          //scan for the highest degree
          int maxDeg = -1;
          Node maxNode;
          for( std::map< Node, RegionNodeInfo* >::iterator
                 it = d_nodes.begin(); it != d_nodes.end(); ++it ){
            //if not in the test clique, add it to the set of new members
            if( it->second->valid() &&
                ( d_testClique.find( it->first )==d_testClique.end() ||
                  !d_testClique[ it->first ] ) ){
              if( it->second->getNumInternalDisequalities()>maxDeg ){
                maxDeg = it->second->getNumInternalDisequalities();
                maxNode = it->first;
              }
            }
          }
          Assert(maxNode != Node::null());
          newClique.push_back( maxNode );
        }
        //check splits internal to new members
        for( int j=0; j<(int)newClique.size(); j++ ){
          Debug("uf-ss-debug") << "Choose to add clique member "
                               << newClique[j] << std::endl;
          for( int k=(j+1); k<(int)newClique.size(); k++ ){
            if( !isDisequal( newClique[j], newClique[k], 1 ) ){
              Node at_j = newClique[j];
              Node at_k = newClique[k];              
              Node j_eq_k =
                NodeManager::currentNM()->mkNode( EQUAL, at_j, at_k );
              d_splits[ j_eq_k ] = true;
              d_splitsSize = d_splitsSize + 1;
            }
          }
          //check disequalities with old members
          for( NodeBoolMap::iterator it = d_testClique.begin();
               it != d_testClique.end(); ++it ){
            if( (*it).second ){
              if( !isDisequal( (*it).first, newClique[j], 1 ) ){
                Node at_it = (*it).first;
                Node at_j = newClique[j];
                Node it_eq_j = at_it.eqNode(at_j);
                d_splits[ it_eq_j ] = true;
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
      // Check if test clique has larger size than cardinality, and
      // forms a clique.
      if( d_testCliqueSize >= unsigned(cardinality+1) && d_splitsSize==0 ){
        //test clique is a clique
        for( NodeBoolMap::iterator it = d_testClique.begin();
             it != d_testClique.end(); ++it ){
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

void Region::getNumExternalDisequalities(
    std::map< Node, int >& num_ext_disequalities ){
  for( Region::iterator it = begin(); it != end(); ++it ){
    RegionNodeInfo* rni = it->second;
    if( rni->valid() ){
      DiseqList* del = rni->get(0);
      for( DiseqList::iterator it2 = del->begin(); it2 != del->end(); ++it2 ){
        if( (*it2).second ){
          num_ext_disequalities[ (*it2).first ]++;
        }
      }
    }
  }
}

void Region::debugPrint( const char* c, bool incClique ) {
  Debug( c ) << "Num reps: " << d_reps_size << std::endl;
  for( Region::iterator it = begin(); it != end(); ++it ){
    RegionNodeInfo* rni = it->second;
    if( rni->valid() ){
      Node n = it->first;
      Debug( c ) << "   " << n << std::endl;
      for( int i=0; i<2; i++ ){
        Debug( c ) << "      " << ( i==0 ? "Ext" : "Int" ) << " disequal:";
        DiseqList* del = rni->get(i);
        for( DiseqList::iterator it2 = del->begin(); it2 != del->end(); ++it2 ){
          if( (*it2).second ){
            Debug( c ) << " " << (*it2).first;
          }
        }
        Debug( c ) << ", total = " << del->size() << std::endl;
      }
    }
  }
  Debug( c ) << "Total disequal: " << d_total_diseq_external << " external,";
  Debug( c ) << " " << d_total_diseq_internal << " internal." << std::endl;

  if( incClique ){
    if( !d_testClique.empty() ){
      Debug( c ) << "Candidate clique members: " << std::endl;
      Debug( c ) << "   ";
      for( NodeBoolMap::iterator it = d_testClique.begin();
           it != d_testClique.end(); ++ it ){
        if( (*it).second ){
          Debug( c ) << (*it).first << " ";
        }
      }
      Debug( c ) << ", size = " << d_testCliqueSize << std::endl;
    }
    if( !d_splits.empty() ){
      Debug( c ) << "Required splits: " << std::endl;
      Debug( c ) << "   ";
      for( NodeBoolMap::iterator it = d_splits.begin(); it != d_splits.end();
           ++ it ){
        if( (*it).second ){
          Debug( c ) << (*it).first << " ";
        }
      }
      Debug( c ) << ", size = " << d_splitsSize << std::endl;
    }
  }
}

SortModel::CardinalityDecisionStrategy::CardinalityDecisionStrategy(
    Node t, context::Context* satContext, Valuation valuation)
    : DecisionStrategyFmf(satContext, valuation), d_cardinality_term(t)
{
}
Node SortModel::CardinalityDecisionStrategy::mkLiteral(unsigned i)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(
      CARDINALITY_CONSTRAINT, d_cardinality_term, nm->mkConst(Rational(i + 1)));
}
std::string SortModel::CardinalityDecisionStrategy::identify() const
{
  return std::string("uf_card");
}

SortModel::SortModel(Node n,
                     context::Context* c,
                     context::UserContext* u,
                     CardinalityExtension* thss)
    : d_type(n.getType()),
      d_thss(thss),
      d_regions_index(c, 0),
      d_regions_map(c),
      d_split_score(c),
      d_disequalities_index(c, 0),
      d_reps(c, 0),
      d_conflict(c, false),
      d_cardinality(c, 1),
      d_hasCard(c, false),
      d_maxNegCard(c, 0),
      d_initialized(u, false),
      d_lemma_cache(u),
      d_c_dec_strat(nullptr)
{
  d_cardinality_term = n;

  if (options::ufssMode() == options::UfssMode::FULL)
  {
    // Register the strategy with the decision manager of the theory.
    // We are guaranteed that the decision manager is ready since we
    // construct this module during TheoryUF::finishInit.
    d_c_dec_strat.reset(new CardinalityDecisionStrategy(
        n, c, thss->getTheory()->getValuation()));
  }
}

SortModel::~SortModel() {
  for(std::vector<Region*>::iterator i = d_regions.begin();
      i != d_regions.end(); ++i) {
    Region* region = *i;
    delete region;
  }
  d_regions.clear();
}

/** initialize */
void SortModel::initialize( OutputChannel* out ){
  if (d_c_dec_strat.get() != nullptr && !d_initialized)
  {
    d_initialized = true;
    // Strategy is user-context-dependent, since it is in sync with
    // user-context-dependent flag d_initialized.
    d_thss->getTheory()->getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_UF_CARD, d_c_dec_strat.get());
  }
}

/** new node */
void SortModel::newEqClass( Node n ){
  if( !d_conflict ){
    if( d_regions_map.find( n )==d_regions_map.end() ){
      // Must generate totality axioms for every cardinality we have
      // allocated thus far.
      for( std::map< int, Node >::iterator it = d_cardinality_literal.begin();
           it != d_cardinality_literal.end(); ++it ){
        if( applyTotality( it->first ) ){
          addTotalityAxiom( n, it->first, &d_thss->getOutputChannel() );
        }
      }
      if( options::ufssTotality() ){
        // Regions map will store whether we need to equate this term
        // with a constant equivalence class.
        if( std::find( d_totality_terms[0].begin(), d_totality_terms[0].end(), n )==d_totality_terms[0].end() ){
          d_regions_map[n] = 0;
        }else{
          d_regions_map[n] = -1;
        }
      }else{
        d_regions_map[n] = d_regions_index;
        Debug("uf-ss") << "CardinalityExtension: New Eq Class " << n
                       << std::endl;
        Debug("uf-ss-debug") << d_regions_index << " "
                             << (int)d_regions.size() << std::endl;
        if( d_regions_index<d_regions.size() ){
          d_regions[ d_regions_index ]->debugPrint("uf-ss-debug",true);
          d_regions[ d_regions_index ]->setValid(true);
          Assert(d_regions[d_regions_index]->getNumReps() == 0);
        }else{
          d_regions.push_back( new Region( this, d_thss->getSatContext() ) );
        }
        d_regions[ d_regions_index ]->addRep( n );
        d_regions_index = d_regions_index + 1;
      }
      d_reps = d_reps + 1;
    }
  }
}

/** merge */
void SortModel::merge( Node a, Node b ){
  if( !d_conflict ){
    if( options::ufssTotality() ){
      if( d_regions_map[b]==-1 ){
        d_regions_map[a] = -1;
      }
      d_regions_map[b] = -1;
    }else{
      Debug("uf-ss") << "CardinalityExtension: Merging " << a << " = " << b
                     << "..." << std::endl;
      if( a!=b ){
        Assert(d_regions_map.find(a) != d_regions_map.end());
        Assert(d_regions_map.find(b) != d_regions_map.end());
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
            // Either move a to d_regions[bi], or b to d_regions[ai].
            RegionNodeInfo* a_region_info = d_regions[ai]->getRegionInfo(a);
            RegionNodeInfo* b_region_info = d_regions[bi]->getRegionInfo(b);
            int aex = ( a_region_info->getNumInternalDisequalities() -
                        getNumDisequalitiesToRegion( a, bi ) );
            int bex = ( b_region_info->getNumInternalDisequalities() -
                        getNumDisequalitiesToRegion( b, ai ) );
            // Based on which would produce the fewest number of
            // external disequalities.
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
        d_regions_map[b] = -1;
      }
      d_reps = d_reps - 1;
    }
  }
}

/** assert terms are disequal */
void SortModel::assertDisequal( Node a, Node b, Node reason ){
  if( !d_conflict ){
    if( options::ufssTotality() ){
      //do nothing
    }else{
      //if they are not already disequal
      eq::EqualityEngine* ee = d_thss->getTheory()->getEqualityEngine();
      a = ee->getRepresentative(a);
      b = ee->getRepresentative(b);
      int ai = d_regions_map[a];
      int bi = d_regions_map[b];
      if( !d_regions[ai]->isDisequal( a, b, ai==bi ) ){
        Debug("uf-ss") << "Assert disequal " << a << " != " << b << "..." << std::endl;
        //if( reason.getKind()!=NOT || reason[0].getKind()!=EQUAL ||
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
        Assert(d_regions_map.find(a) != d_regions_map.end());
        Assert(d_regions_map.find(b) != d_regions_map.end());
        Debug("uf-ss") << "   regions: " << ai << " " << bi << std::endl;
        if( ai==bi ){
          //internal disequality
          d_regions[ai]->setDisequal( a, b, 1, true );
          d_regions[ai]->setDisequal( b, a, 1, true );
          checkRegion( ai, false );  //do not need to check if it needs to combine (no new ext. disequalities)
        }else{
          //external disequality
          d_regions[ai]->setDisequal( a, b, 0, true );
          d_regions[bi]->setDisequal( b, a, 0, true );
          checkRegion( ai );
          checkRegion( bi );
        }
      }
    }
  }
}

bool SortModel::areDisequal( Node a, Node b ) {
  Assert(a == d_thss->getTheory()->getEqualityEngine()->getRepresentative(a));
  Assert(b == d_thss->getTheory()->getEqualityEngine()->getRepresentative(b));
  if( d_regions_map.find( a )!=d_regions_map.end() &&
      d_regions_map.find( b )!=d_regions_map.end() ){
    int ai = d_regions_map[a];
    int bi = d_regions_map[b];
    return d_regions[ai]->isDisequal(a, b, ai==bi ? 1 : 0);
  }else{
    return false;
  }
}

/** check */
void SortModel::check( Theory::Effort level, OutputChannel* out ){
  Assert(options::ufssMode() == options::UfssMode::FULL);
  if( level>=Theory::EFFORT_STANDARD && d_hasCard && !d_conflict ){
    Debug("uf-ss") << "CardinalityExtension: Check " << level << " " << d_type
                   << std::endl;
    if( level==Theory::EFFORT_FULL ){
      Debug("fmf-full-check") << std::endl;
      Debug("fmf-full-check") << "Full check for SortModel " << d_type << ", status : " << std::endl;
      debugPrint("fmf-full-check");
      Debug("fmf-full-check") << std::endl;
    }
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
      //first check if we can generate a clique conflict
      if( !options::ufssTotality() ){
        //do a check within each region
        for( int i=0; i<(int)d_regions_index; i++ ){
          if( d_regions[i]->valid() ){
            std::vector< Node > clique;
            if( d_regions[i]->check( level, d_cardinality, clique ) ){
              //add clique lemma
              addCliqueLemma( clique, out );
              return;
            }else{
              Trace("uf-ss-debug") << "No clique in Region #" << i << std::endl;
            }
          }
        }
      }
      if( !applyTotality( d_cardinality ) ){
        //do splitting on demand
        bool addedLemma = false;
        if (level==Theory::EFFORT_FULL)
        {
          Trace("uf-ss-debug") << "Add splits?" << std::endl;
          //see if we have any recommended splits from large regions
          for( int i=0; i<(int)d_regions_index; i++ ){
            if( d_regions[i]->valid() && d_regions[i]->getNumReps()>d_cardinality ){

              int sp = addSplit( d_regions[i], out );
              if( sp==1 ){
                addedLemma = true;
#ifdef ONE_SPLIT_REGION
                break;
#endif
              }else if( sp==-1 ){
                check( level, out );
                return;
              }
            }
          }
        }
        //If no added lemmas, force continuation via combination of regions.
        if( level==Theory::EFFORT_FULL ){
          if( !addedLemma ){
            Trace("uf-ss-debug") << "No splits added. " << d_cardinality
                                 << std::endl;
            Trace("uf-ss-si")  << "Must combine region" << std::endl;
            bool recheck = false;
            SortInference* si = d_thss->getSortInference();
            if (si != nullptr)
            {
              //If sort inference is enabled, search for regions with same sort.
              std::map< int, int > sortsFound;
              for( int i=0; i<(int)d_regions_index; i++ ){
                if( d_regions[i]->valid() ){
                  Node op = d_regions[i]->frontKey();
                  int sort_id = si->getSortId(op);
                  if( sortsFound.find( sort_id )!=sortsFound.end() ){
                    Debug("fmf-full-check") << "Combined regions " << i << " " << sortsFound[sort_id] << std::endl;
                    combineRegions( sortsFound[sort_id], i );
                    recheck = true;
                    break;
                  }else{
                    sortsFound[sort_id] = i;
                  }
                }
              }
            }
            if( !recheck ) {
              //naive strategy, force region combination involving the first valid region
              for( int i=0; i<(int)d_regions_index; i++ ){
                if( d_regions[i]->valid() ){
                  int fcr = forceCombineRegion( i, false );
                  Debug("fmf-full-check") << "Combined regions " << i << " " << fcr << std::endl;
                  Trace("uf-ss-debug") << "Combined regions " << i << " " << fcr << std::endl;
                  recheck = true;
                  break;
                }
              }
            }
            if( recheck ){
              Trace("uf-ss-debug") << "Must recheck." << std::endl;
              check( level, out );
            }
          }
        }
      }
    }
  }
}

void SortModel::presolve() {
  d_initialized = false;
}

void SortModel::propagate( Theory::Effort level, OutputChannel* out ){

}

int SortModel::getNumDisequalitiesToRegion( Node n, int ri ){
  int ni = d_regions_map[n];
  int counter = 0;
  DiseqList* del = d_regions[ni]->getRegionInfo(n)->get(0);
  for( DiseqList::iterator it = del->begin(); it != del->end(); ++it ){
    if( (*it).second ){
      if( d_regions_map[ (*it).first ]==ri ){
        counter++;
      }
    }
  }
  return counter;
}

void SortModel::getDisequalitiesToRegions(int ri,
                                          std::map< int, int >& regions_diseq)
{
  Region* region = d_regions[ri];
  for(Region::iterator it = region->begin(); it != region->end(); ++it ){
    if( it->second->valid() ){
      DiseqList* del = it->second->get(0);
      for( DiseqList::iterator it2 = del->begin(); it2 != del->end(); ++it2 ){
        if( (*it2).second ){
          Assert(isValid(d_regions_map[(*it2).first]));
          //Notice() << "Found disequality with " << (*it2).first << ", region = " << d_regions_map[ (*it2).first ] << std::endl;
          regions_diseq[ d_regions_map[ (*it2).first ] ]++;
        }
      }
    }
  }
}

void SortModel::setSplitScore( Node n, int s ){
  if( d_split_score.find( n )!=d_split_score.end() ){
    int ss = d_split_score[ n ];
    d_split_score[ n ] = s>ss ? s : ss;
  }else{
    d_split_score[ n ] = s;
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    setSplitScore( n[i], s+1 );
  }
}

void SortModel::assertCardinality( OutputChannel* out, int c, bool val ){
  if( !d_conflict ){
    Trace("uf-ss-assert")
        << "Assert cardinality " << d_type << " " << c << " " << val
        << " level = "
        << d_thss->getTheory()->getValuation().getAssertionLevel() << std::endl;
    Assert(c > 0);
    Node cl = getCardinalityLiteral( c );
    if( val ){
      bool doCheckRegions = !d_hasCard;
      bool prevHasCard = d_hasCard;
      d_hasCard = true;
      if( !prevHasCard || c<d_cardinality ){
        d_cardinality = c;
        simpleCheckCardinality();
        if( d_thss->d_conflict.get() ){
          return;
        }
      }
      //should check all regions now
      if( doCheckRegions ){
        for( int i=0; i<(int)d_regions_index; i++ ){
          if( d_regions[i]->valid() ){
            checkRegion( i );
            if( d_conflict ){
              return;
            }
          }
        }
      }
      // we assert it positively, if its beyond the bound, abort
      if (options::ufssAbortCardinality() != -1
          && c >= options::ufssAbortCardinality())
      {
        std::stringstream ss;
        ss << "Maximum cardinality (" << options::ufssAbortCardinality()
           << ")  for finite model finding exceeded." << std::endl;
        throw LogicException(ss.str());
      }
    }
    else
    {
      if( c>d_maxNegCard.get() ){
        Trace("uf-ss-com-card-debug") << "Maximum negative cardinality for " << d_type << " is now " << c << std::endl;
        d_maxNegCard.set( c );
        simpleCheckCardinality();
      }
    }
  }
}

void SortModel::checkRegion( int ri, bool checkCombine ){
  if( isValid(ri) && d_hasCard ){
    Assert(d_cardinality > 0);
    if( checkCombine && d_regions[ri]->getMustCombine( d_cardinality ) ){
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
      if( riNew>=0 ){
        checkRegion( riNew, checkCombine );
      }
    }
    //now check if region is in conflict
    std::vector< Node > clique;
    if( d_regions[ri]->check( Theory::EFFORT_STANDARD, d_cardinality, clique ) ){
      //explain clique
      addCliqueLemma( clique, &d_thss->getOutputChannel() );
    }
  }
}

int SortModel::forceCombineRegion( int ri, bool useDensity ){
  if( !useDensity ){
    for( int i=0; i<(int)d_regions_index; i++ ){
      if( ri!=i && d_regions[i]->valid() ){
        return combineRegions( ri, i );
      }
    }
    return -1;
  }else{
    //this region must merge with another
    if( Debug.isOn("uf-ss-check-region") ){
      Debug("uf-ss-check-region") << "We must combine Region #" << ri << ". " << std::endl;
      d_regions[ri]->debugPrint("uf-ss-check-region");
    }
    //take region with maximum disequality density
    double maxScore = 0;
    int maxRegion = -1;
    std::map< int, int > regions_diseq;
    getDisequalitiesToRegions( ri, regions_diseq );
    for( std::map< int, int >::iterator it = regions_diseq.begin(); it != regions_diseq.end(); ++it ){
      Debug("uf-ss-check-region") << it->first << " : " << it->second << std::endl;
    }
    for( std::map< int, int >::iterator it = regions_diseq.begin(); it != regions_diseq.end(); ++it ){
      Assert(it->first != ri);
      Assert(isValid(it->first));
      Assert(d_regions[it->first]->getNumReps() > 0);
      double tempScore = double(it->second)/double(d_regions[it->first]->getNumReps() );
      if( tempScore>maxScore ){
        maxRegion = it->first;
        maxScore = tempScore;
      }
    }
    if( maxRegion!=-1 ){
      if( Debug.isOn("uf-ss-check-region") ){
        Debug("uf-ss-check-region") << "Combine with region #" << maxRegion << ":" << std::endl;
        d_regions[maxRegion]->debugPrint("uf-ss-check-region");
      }
      return combineRegions( ri, maxRegion );
    }
    return -1;
  }
}


int SortModel::combineRegions( int ai, int bi ){
#ifdef COMBINE_REGIONS_SMALL_INTO_LARGE
  if( d_regions[ai]->getNumReps()<d_regions[bi]->getNumReps() ){
    return combineRegions( bi, ai );
  }
#endif
  Debug("uf-ss-region") << "uf-ss: Combine Region #" << bi << " with Region #" << ai << std::endl;
  Assert(isValid(ai) && isValid(bi));
  Region* region_bi = d_regions[bi];
  for(Region::iterator it = region_bi->begin(); it != region_bi->end(); ++it){
    Region::RegionNodeInfo* rni = it->second;
    if( rni->valid() ){
      d_regions_map[ it->first ] = ai;
    }
  }
  //update regions disequal DO_THIS?
  d_regions[ai]->combine( d_regions[bi] );
  d_regions[bi]->setValid( false );
  return ai;
}

void SortModel::moveNode( Node n, int ri ){
  Debug("uf-ss-region") << "uf-ss: Move node " << n << " to Region #" << ri << std::endl;
  Assert(isValid(d_regions_map[n]));
  Assert(isValid(ri));
  //move node to region ri
  d_regions[ri]->takeNode( d_regions[ d_regions_map[n] ], n );
  d_regions_map[n] = ri;
}

int SortModel::addSplit( Region* r, OutputChannel* out ){
  Node s;
  if( r->hasSplits() ){
    //take the first split you find
    for( Region::split_iterator it = r->begin_splits();
         it != r->end_splits(); ++it ){
      if( (*it).second ){
        s = (*it).first;
        break;
      }
    }
    Assert(s != Node::null());
  }
  if (!s.isNull() ){
    //add lemma to output channel
    Assert(s.getKind() == EQUAL);
    Node ss = Rewriter::rewrite( s );
    if( ss.getKind()!=EQUAL ){
      Node b_t = NodeManager::currentNM()->mkConst( true );
      Node b_f = NodeManager::currentNM()->mkConst( false );
      if( ss==b_f ){
        Trace("uf-ss-lemma") << "....Assert disequal directly : "
                             << s[0] << " " << s[1] << std::endl;
        assertDisequal( s[0], s[1], b_t );
        return -1;
      }else{
        Trace("uf-ss-warn") << "Split on unknown literal : " << ss << std::endl;
      }
      if( ss==b_t ){
        Message() << "Bad split " << s << std::endl;
        AlwaysAssert(false);
      }
    }
    SortInference* si = d_thss->getSortInference();
    if (si != nullptr)
    {
      for( int i=0; i<2; i++ ){
        int sid = si->getSortId(ss[i]);
        Trace("uf-ss-split-si") << sid << " ";
      }
      Trace("uf-ss-split-si")  << std::endl;
    }
    //Trace("uf-ss-lemma") << d_th->getEqualityEngine()->areEqual( s[0], s[1] ) << " ";
    //Trace("uf-ss-lemma") << d_th->getEqualityEngine()->areDisequal( s[0], s[1] ) << std::endl;
    //Trace("uf-ss-lemma") << s[0].getType() << " " << s[1].getType() << std::endl;
    //Notice() << "*** Split on " << s << std::endl;
    //split on the equality s
    Node lem = NodeManager::currentNM()->mkNode( kind::OR, ss, ss.negate() );
    if( doSendLemma( lem ) ){
      Trace("uf-ss-lemma") << "*** Split on " << s << std::endl;
      //tell the sat solver to explore the equals branch first
      out->requirePhase( ss, true );
      ++( d_thss->d_statistics.d_split_lemmas );
    }
    return 1;
  }else{
    return 0;
  }
}


void SortModel::addCliqueLemma( std::vector< Node >& clique, OutputChannel* out ){
  Assert(d_hasCard);
  Assert(d_cardinality > 0);
  while( clique.size()>size_t(d_cardinality+1) ){
    clique.pop_back();
  }
  // add as lemma
  std::vector<Node> eqs;
  for (unsigned i = 0, size = clique.size(); i < size; i++)
  {
    for (unsigned j = 0; j < i; j++)
    {
      eqs.push_back(clique[i].eqNode(clique[j]));
    }
  }
  eqs.push_back(d_cardinality_literal[d_cardinality].notNode());
  Node lem = NodeManager::currentNM()->mkNode(OR, eqs);
  if (doSendLemma(lem))
  {
    Trace("uf-ss-lemma") << "*** Add clique lemma " << lem << std::endl;
    ++(d_thss->d_statistics.d_clique_lemmas);
  }
}

void SortModel::addTotalityAxiom( Node n, int cardinality, OutputChannel* out ){
  if( std::find( d_totality_terms[0].begin(), d_totality_terms[0].end(), n )==d_totality_terms[0].end() ){
    if( std::find( d_totality_lems[n].begin(), d_totality_lems[n].end(), cardinality ) == d_totality_lems[n].end() ){
      NodeManager* nm = NodeManager::currentNM();
      d_totality_lems[n].push_back( cardinality );
      Node cardLit = d_cardinality_literal[ cardinality ];
      int sort_id = 0;
      SortInference* si = d_thss->getSortInference();
      if (si != nullptr)
      {
        sort_id = si->getSortId(n);
      }
      Trace("uf-ss-totality") << "Add totality lemma for " << n << " " << cardinality << ", sort id is " << sort_id << std::endl;
      int use_cardinality = cardinality;
      if( options::ufssTotalitySymBreak() ){
        if( d_sym_break_index.find(n)!=d_sym_break_index.end() ){
          use_cardinality = d_sym_break_index[n];
        }else if( (int)d_sym_break_terms[n.getType()][sort_id].size()<cardinality-1 ){
          use_cardinality = d_sym_break_terms[n.getType()][sort_id].size() + 1;
          d_sym_break_terms[n.getType()][sort_id].push_back( n );
          d_sym_break_index[n] = use_cardinality;
          Trace("uf-ss-totality") << "Allocate symmetry breaking term " << n << ", index = " << use_cardinality << std::endl;
          if( d_sym_break_terms[n.getType()][sort_id].size()>1 ){
            //enforce canonicity
            for( int i=2; i<use_cardinality; i++ ){
              //can only be assigned to domain constant d if someone has been assigned domain constant d-1
              Node eq = n.eqNode( getTotalityLemmaTerm( cardinality, i ) );
              std::vector< Node > eqs;
              for( unsigned j=0; j<(d_sym_break_terms[n.getType()][sort_id].size()-1); j++ ){
                eqs.push_back( d_sym_break_terms[n.getType()][sort_id][j].eqNode( getTotalityLemmaTerm( cardinality, i-1 ) ) );
              }
              Node ax = eqs.size()==1 ? eqs[0] : NodeManager::currentNM()->mkNode( OR, eqs );
              Node lem = NodeManager::currentNM()->mkNode( IMPLIES, eq, ax );
              Trace("uf-ss-lemma") << "*** Add (canonicity) totality axiom " << lem << std::endl;
              d_thss->getOutputChannel().lemma( lem );
            }
          }
        }
      }

      std::vector< Node > eqs;
      for( int i=0; i<use_cardinality; i++ ){
        eqs.push_back( n.eqNode( getTotalityLemmaTerm( cardinality, i ) ) );
      }
      Node ax = eqs.size() == 1 ? eqs[0] : nm->mkNode(OR, eqs);
      Node lem = NodeManager::currentNM()->mkNode( IMPLIES, cardLit, ax );
      Trace("uf-ss-lemma") << "*** Add totality axiom " << lem << std::endl;
      //send as lemma to the output channel
      d_thss->getOutputChannel().lemma( lem );
      ++( d_thss->d_statistics.d_totality_lemmas );
    }
  }
}

/** apply totality */
bool SortModel::applyTotality( int cardinality ){
  return options::ufssTotality() || cardinality<=options::ufssTotalityLimited();
}

/** get totality lemma terms */
Node SortModel::getTotalityLemmaTerm( int cardinality, int i ){
  return d_totality_terms[0][i];
}

void SortModel::simpleCheckCardinality() {
  if( d_maxNegCard.get()!=0 && d_hasCard.get() && d_cardinality.get()<d_maxNegCard.get() ){
    Node lem = NodeManager::currentNM()->mkNode( AND, getCardinalityLiteral( d_cardinality.get() ),
                                                      getCardinalityLiteral( d_maxNegCard.get() ).negate() );
    Trace("uf-ss-lemma") << "*** Simple cardinality conflict : " << lem << std::endl;
    d_thss->getOutputChannel().conflict( lem );
    d_thss->d_conflict.set( true );
  }
}

bool SortModel::doSendLemma( Node lem ) {
  if( d_lemma_cache.find( lem )==d_lemma_cache.end() ){
    d_lemma_cache[lem] = true;
    d_thss->getOutputChannel().lemma( lem );
    return true;
  }else{
    return false;
  }
}

void SortModel::debugPrint( const char* c ){
  if( Debug.isOn( c ) ){
    Debug( c ) << "Number of reps = " << d_reps << std::endl;
    Debug( c ) << "Cardinality req = " << d_cardinality << std::endl;
    unsigned debugReps = 0;
    for( unsigned i=0; i<d_regions_index; i++ ){
      Region* region = d_regions[i]; 
      if( region->valid() ){
        Debug( c ) << "Region #" << i << ": " << std::endl;
        region->debugPrint( c, true );
        Debug( c ) << std::endl;
        for( Region::iterator it = region->begin(); it != region->end(); ++it ){
          if( it->second->valid() ){
            if( d_regions_map[ it->first ]!=(int)i ){
              Debug( c ) << "***Bad regions map : " << it->first
                         << " " << d_regions_map[ it->first ].get() << std::endl;
            }
          }
        }
        debugReps += region->getNumReps();
      }
    }

    if( debugReps!=d_reps ){
      Debug( c ) << "***Bad reps: " << d_reps << ", "
                 << "actual = " << debugReps << std::endl;
    }
  }
}

bool SortModel::debugModel( TheoryModel* m ){
  if( Trace.isOn("uf-ss-warn") ){
    std::vector< Node > eqcs;
    eq::EqClassesIterator eqcs_i =
        eq::EqClassesIterator(m->getEqualityEngine());
    while( !eqcs_i.isFinished() ){
      Node eqc = (*eqcs_i);
      if( eqc.getType()==d_type ){
        if( std::find( eqcs.begin(), eqcs.end(), eqc )==eqcs.end() ){
          eqcs.push_back( eqc );
          //we must ensure that this equivalence class has been accounted for
          if( d_regions_map.find( eqc )==d_regions_map.end() ){
            Trace("uf-ss-warn") << "WARNING : equivalence class " << eqc << " unaccounted for." << std::endl;
            Trace("uf-ss-warn") << "  type : " << d_type << std::endl;
            Trace("uf-ss-warn") << "  kind : " << eqc.getKind() << std::endl;
          }
        }
      }
      ++eqcs_i;
    }
  }
  RepSet* rs = m->getRepSetPtr();
  int nReps = (int)rs->getNumRepresentatives(d_type);
  if( nReps!=(d_maxNegCard+1) ){
    Trace("uf-ss-warn") << "WARNING : Model does not have same # representatives as cardinality for " << d_type << "." << std::endl;
    Trace("uf-ss-warn") << "   Max neg cardinality : " << d_maxNegCard << std::endl;
    Trace("uf-ss-warn") << "   # Reps : " << nReps << std::endl;
    if( d_maxNegCard>=nReps ){
      while( (int)d_fresh_aloc_reps.size()<=d_maxNegCard ){
        std::stringstream ss;
        ss << "r_" << d_type << "_";
        Node nn = NodeManager::currentNM()->mkSkolem( ss.str(), d_type, "enumeration to meet negative card constraint" );
        d_fresh_aloc_reps.push_back( nn );
      }
      if( d_maxNegCard==0 ){
        rs->d_type_reps[d_type].push_back(d_fresh_aloc_reps[0]);
      }else{
        //must add lemma
        std::vector< Node > force_cl;
        for( int i=0; i<=d_maxNegCard; i++ ){
          for( int j=(i+1); j<=d_maxNegCard; j++ ){
            force_cl.push_back( d_fresh_aloc_reps[i].eqNode( d_fresh_aloc_reps[j] ).negate() );
          }
        }
        Node cl = getCardinalityLiteral( d_maxNegCard );
        Node lem = NodeManager::currentNM()->mkNode( OR, cl, NodeManager::currentNM()->mkNode( AND, force_cl ) );
        Trace("uf-ss-lemma") << "*** Enforce negative cardinality constraint lemma : " << lem << std::endl;
        d_thss->getOutputChannel().lemma( lem );
        return false;
      }
    }
  }
  return true;
}

int SortModel::getNumRegions(){
  int count = 0;
  for( int i=0; i<(int)d_regions_index; i++ ){
    if( d_regions[i]->valid() ){
      count++;
    }
  }
  return count;
}

Node SortModel::getCardinalityLiteral(unsigned c)
{
  Assert(c > 0);
  std::map<int, Node>::iterator itcl = d_cardinality_literal.find(c);
  if (itcl != d_cardinality_literal.end())
  {
    return itcl->second;
  }
  // get the literal from the decision strategy
  Node lit = d_c_dec_strat->getLiteral(c - 1);
  d_cardinality_literal[c] = lit;

  // Since we are reasoning about cardinality c, we invoke a totality axiom
  if (!applyTotality(c))
  {
    // return if we are not using totality axioms
    return lit;
  }

  NodeManager* nm = NodeManager::currentNM();
  Node var;
  if (c == 1 && !options::ufssTotalitySymBreak())
  {
    // get arbitrary ground term
    var = d_cardinality_term;
  }
  else
  {
    std::stringstream ss;
    ss << "_c_" << c;
    var = nm->mkSkolem(ss.str(), d_type, "is a cardinality lemma term");
  }
  if ((c - 1) < d_totality_terms[0].size())
  {
    d_totality_terms[0][c - 1] = var;
  }
  else
  {
    d_totality_terms[0].push_back(var);
  }
  // must be distinct from all other cardinality terms
  for (unsigned i = 1, size = d_totality_terms[0].size(); i < size; i++)
  {
    Node lem = var.eqNode(d_totality_terms[0][i - 1]).notNode();
    Trace("uf-ss-lemma") << "Totality distinctness lemma : " << lem
                         << std::endl;
    d_thss->getOutputChannel().lemma(lem);
  }
  // must send totality axioms for each existing term
  for (NodeIntMap::iterator it = d_regions_map.begin();
       it != d_regions_map.end();
       ++it)
  {
    addTotalityAxiom((*it).first, c, &d_thss->getOutputChannel());
  }
  return lit;
}

CardinalityExtension::CardinalityExtension(context::Context* c,
                                           context::UserContext* u,
                                           OutputChannel& out,
                                           TheoryUF* th)
    : d_out(&out),
      d_th(th),
      d_conflict(c, false),
      d_rep_model(),
      d_min_pos_com_card(c, -1),
      d_cc_dec_strat(nullptr),
      d_initializedCombinedCardinality(u, false),
      d_card_assertions_eqv_lemma(u),
      d_min_pos_tn_master_card(c, -1),
      d_rel_eqc(c)
{
  if (options::ufssMode() == options::UfssMode::FULL && options::ufssFairness())
  {
    // Register the strategy with the decision manager of the theory.
    // We are guaranteed that the decision manager is ready since we
    // construct this module during TheoryUF::finishInit.
    d_cc_dec_strat.reset(
        new CombinedCardinalityDecisionStrategy(c, th->getValuation()));
  }
}

CardinalityExtension::~CardinalityExtension()
{
  for (std::map<TypeNode, SortModel*>::iterator it = d_rep_model.begin();
       it != d_rep_model.end(); ++it) {
    delete it->second;
  }
}

SortInference* CardinalityExtension::getSortInference()
{
  if (!options::sortInference())
  {
    return nullptr;
  }
  QuantifiersEngine* qe = d_th->getQuantifiersEngine();
  if (qe != nullptr)
  {
    return qe->getTheoryEngine()->getSortInference();
  }
  return nullptr;
}

/** get default sat context */
context::Context* CardinalityExtension::getSatContext()
{
  return d_th->getSatContext();
}

/** get default output channel */
OutputChannel& CardinalityExtension::getOutputChannel()
{
  return d_th->getOutputChannel();
}

/** ensure eqc */
void CardinalityExtension::ensureEqc(SortModel* c, Node a)
{
  if( !hasEqc( a ) ){
    d_rel_eqc[a] = true;
    Trace("uf-ss-solver") << "CardinalityExtension: New eq class " << a << " : "
                          << a.getType() << std::endl;
    c->newEqClass( a );
    Trace("uf-ss-solver") << "CardinalityExtension: Done New eq class."
                          << std::endl;
  }
}

void CardinalityExtension::ensureEqcRec(Node n)
{
  if( !hasEqc( n ) ){
    SortModel* c = getSortModel( n );
    if( c ){
      ensureEqc( c, n );
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      ensureEqcRec( n[i] );
    }
  }
}

/** has eqc */
bool CardinalityExtension::hasEqc(Node a)
{
  NodeBoolMap::iterator it = d_rel_eqc.find( a );
  return it!=d_rel_eqc.end() && (*it).second;
}

/** new node */
void CardinalityExtension::newEqClass(Node a)
{
  SortModel* c = getSortModel( a );
  if( c ){
#ifdef LAZY_REL_EQC
    //do nothing
#else
    Trace("uf-ss-solver") << "CardinalityExtension: New eq class " << a << " : "
                          << a.getType() << std::endl;
    c->newEqClass( a );
    Trace("uf-ss-solver") << "CardinalityExtension: Done New eq class."
                          << std::endl;
#endif
  }
}

/** merge */
void CardinalityExtension::merge(Node a, Node b)
{
  //TODO: ensure they are relevant
  SortModel* c = getSortModel( a );
  if( c ){
#ifdef LAZY_REL_EQC
    ensureEqc( c, a );
    if( hasEqc( b ) ){
      Trace("uf-ss-solver") << "CardinalityExtension: Merge " << a << " " << b
                            << " : " << a.getType() << std::endl;
      c->merge( a, b );
      Trace("uf-ss-solver") << "CardinalityExtension: Done Merge." << std::endl;
    }else{
      //c->assignEqClass( b, a );
      d_rel_eqc[b] = true;
    }
#else
    Trace("uf-ss-solver") << "CardinalityExtension: Merge " << a << " " << b
                          << " : " << a.getType() << std::endl;
    c->merge( a, b );
    Trace("uf-ss-solver") << "CardinalityExtension: Done Merge." << std::endl;
#endif
  }
}

/** assert terms are disequal */
void CardinalityExtension::assertDisequal(Node a, Node b, Node reason)
{
  SortModel* c = getSortModel( a );
  if( c ){
#ifdef LAZY_REL_EQC
    ensureEqc( c, a );
    ensureEqc( c, b );
#endif
    Trace("uf-ss-solver") << "CardinalityExtension: Assert disequal " << a
                          << " " << b << " : " << a.getType() << std::endl;
    c->assertDisequal( a, b, reason );
    Trace("uf-ss-solver") << "CardinalityExtension: Done Assert disequal."
                          << std::endl;
  }
}

/** assert a node */
void CardinalityExtension::assertNode(Node n, bool isDecision)
{
  Trace("uf-ss") << "Assert " << n << " " << isDecision << std::endl;
#ifdef LAZY_REL_EQC
  ensureEqcRec( n );
#endif
  bool polarity = n.getKind() != kind::NOT;
  TNode lit = polarity ? n : n[0];
  if (options::ufssMode() == options::UfssMode::FULL)
  {
    if( lit.getKind()==CARDINALITY_CONSTRAINT ){
      TypeNode tn = lit[0].getType();
      Assert(tn.isSort());
      Assert(d_rep_model[tn]);
      int nCard = lit[1].getConst<Rational>().getNumerator().getSignedInt();
      Node ct = d_rep_model[tn]->getCardinalityTerm();
      Trace("uf-ss-debug") << "...check cardinality terms : " << lit[0] << " " << ct << std::endl;
      if( lit[0]==ct ){
        if( options::ufssFairnessMonotone() ){
          Trace("uf-ss-com-card-debug") << "...set master/slave" << std::endl;
          if( tn!=d_tn_mono_master ){
            std::map< TypeNode, bool >::iterator it = d_tn_mono_slave.find( tn );
            if( it==d_tn_mono_slave.end() ){
              bool isMonotonic;
              SortInference* si = getSortInference();
              if (si != nullptr)
              {
                isMonotonic = si->isMonotonic(tn);
              }else{
                //if ground, everything is monotonic
                isMonotonic = true;
              }
              if( isMonotonic ){
                if( d_tn_mono_master.isNull() ){
                  Trace("uf-ss-com-card-debug") << "uf-ss-fair-monotone: Set master : " << tn << std::endl;
                  d_tn_mono_master = tn;
                }else{
                  Trace("uf-ss-com-card-debug") << "uf-ss-fair-monotone: Set slave : " << tn << std::endl;
                  d_tn_mono_slave[tn] = true;
                }
              }else{
                Trace("uf-ss-com-card-debug") << "uf-ss-fair-monotone: Set non-monotonic : " << tn << std::endl;
                d_tn_mono_slave[tn] = false;
              }
            }
          }
          //set the minimum positive cardinality for master if necessary
          if( polarity && tn==d_tn_mono_master ){
            Trace("uf-ss-com-card-debug") << "...set min positive cardinality" << std::endl;
            if( d_min_pos_tn_master_card.get()==-1 || nCard<d_min_pos_tn_master_card.get() ){
              d_min_pos_tn_master_card.set( nCard );
            }
          }
        }
        Trace("uf-ss-com-card-debug") << "...assert cardinality" << std::endl;
        d_rep_model[tn]->assertCardinality( d_out, nCard, polarity );
        //check if combined cardinality is violated
        checkCombinedCardinality();
      }else{
        //otherwise, make equal via lemma
        if( d_card_assertions_eqv_lemma.find( lit )==d_card_assertions_eqv_lemma.end() ){
          Node eqv_lit = NodeManager::currentNM()->mkNode( CARDINALITY_CONSTRAINT, ct, lit[1] );
          eqv_lit = lit.eqNode( eqv_lit );
          Trace("uf-ss-lemma") << "*** Cardinality equiv lemma : " << eqv_lit << std::endl;
          getOutputChannel().lemma( eqv_lit );
          d_card_assertions_eqv_lemma[lit] = true;
        }
      }
    }else if( lit.getKind()==COMBINED_CARDINALITY_CONSTRAINT ){
      if( polarity ){
        //safe to assume int here
        int nCard = lit[0].getConst<Rational>().getNumerator().getSignedInt();
        if( d_min_pos_com_card.get()==-1 || nCard<d_min_pos_com_card.get() ){
          d_min_pos_com_card.set( nCard );
          checkCombinedCardinality();
        }
      }
    }else{
      if( Trace.isOn("uf-ss-warn") ){
        ////FIXME: this is too strict: theory propagations are showing up as isDecision=true, but
        ////       a theory propagation is not a decision.
        if( isDecision ){
          for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
            if( !it->second->hasCardinalityAsserted() ){
              Trace("uf-ss-warn") << "WARNING: Assert " << n << " as a decision before cardinality for " << it->first << "." << std::endl;
              //Message() << "Error: constraint asserted before cardinality for " << it->first << std::endl;
              //Unimplemented();
            }
          }
        }
      }
    }
  }
  else
  {
    if( lit.getKind()==CARDINALITY_CONSTRAINT || lit.getKind()==COMBINED_CARDINALITY_CONSTRAINT ){
      // cardinality constraint from user input, set incomplete   
      Trace("uf-ss") << "Literal " << lit << " not handled when uf ss mode is not FULL, set incomplete." << std::endl;
      d_out->setIncomplete();
    }
  }
  Trace("uf-ss") << "Assert: done " << n << " " << isDecision << std::endl;
}

bool CardinalityExtension::areDisequal(Node a, Node b)
{
  if( a==b ){
    return false;
  }
  eq::EqualityEngine* ee = d_th->getEqualityEngine();
  a = ee->getRepresentative(a);
  b = ee->getRepresentative(b);
  if (ee->areDisequal(a, b, false))
  {
    return true;
  }
  SortModel* c = getSortModel(a);
  if (c)
  {
    return c->areDisequal(a, b);
  }
  return false;
}

/** check */
void CardinalityExtension::check(Theory::Effort level)
{
  if( !d_conflict ){
    if (options::ufssMode() == options::UfssMode::FULL)
    {
      Trace("uf-ss-solver")
          << "CardinalityExtension: check " << level << std::endl;
      if (level == Theory::EFFORT_FULL)
      {
        if (Debug.isOn("uf-ss-debug"))
        {
          debugPrint("uf-ss-debug");
        }
        if (Trace.isOn("uf-ss-state"))
        {
          Trace("uf-ss-state")
              << "CardinalityExtension::check " << level << std::endl;
          for (std::pair<const TypeNode, SortModel*>& rm : d_rep_model)
          {
            Trace("uf-ss-state") << "  " << rm.first << " has cardinality "
                                 << rm.second->getCardinality() << std::endl;
          }
        }
      }
      for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
        it->second->check( level, d_out );
        if( it->second->isConflict() ){
          d_conflict = true;
          break;
        }
      }
    }
    else if (options::ufssMode() == options::UfssMode::NO_MINIMAL)
    {
      if( level==Theory::EFFORT_FULL ){
        // split on an equality between two equivalence classes (at most one per type)
        std::map< TypeNode, std::vector< Node > > eqc_list;
        std::map< TypeNode, bool > type_proc;
        eq::EqClassesIterator eqcs_i(d_th->getEqualityEngine());
        while( !eqcs_i.isFinished() ){
          Node a = *eqcs_i;
          TypeNode tn = a.getType();
          if( tn.isSort() ){
            if( type_proc.find( tn )==type_proc.end() ){
              std::map< TypeNode, std::vector< Node > >::iterator itel = eqc_list.find( tn );
              if( itel!=eqc_list.end() ){
                for( unsigned j=0; j<itel->second.size(); j++ ){
                  Node b = itel->second[j];
                  if( !d_th->getEqualityEngine()->areDisequal( a, b, false ) ){
                    Node eq = Rewriter::rewrite( a.eqNode( b ) );
                    Node lem = NodeManager::currentNM()->mkNode( kind::OR, eq, eq.negate() );
                    Trace("uf-ss-lemma") << "*** Split (no-minimal) : " << lem << std::endl;
                    d_out->lemma( lem );
                    d_out->requirePhase( eq, true );
                    type_proc[tn] = true;
                    break;
                  }
                }
              }
              eqc_list[tn].push_back( a );
            }
          }
          ++eqcs_i;
        }
      }
    }
    else
    {
      // unhandled uf ss mode
      Assert(false);
    }
    Trace("uf-ss-solver") << "Done CardinalityExtension: check " << level
                          << std::endl;
  }
}

void CardinalityExtension::presolve()
{
  d_initializedCombinedCardinality = false;
  for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
    it->second->presolve();
    it->second->initialize( d_out );
  }
}

CardinalityExtension::CombinedCardinalityDecisionStrategy::
    CombinedCardinalityDecisionStrategy(context::Context* satContext,
                                        Valuation valuation)
    : DecisionStrategyFmf(satContext, valuation)
{
}
Node CardinalityExtension::CombinedCardinalityDecisionStrategy::mkLiteral(
    unsigned i)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(COMBINED_CARDINALITY_CONSTRAINT, nm->mkConst(Rational(i)));
}

std::string
CardinalityExtension::CombinedCardinalityDecisionStrategy::identify() const
{
  return std::string("uf_combined_card");
}

void CardinalityExtension::preRegisterTerm(TNode n)
{
  if (options::ufssMode() == options::UfssMode::FULL)
  {
    //initialize combined cardinality
    initializeCombinedCardinality();

    Trace("uf-ss-register") << "Preregister " << n << "." << std::endl;
    //shouldn't have to preregister this type (it may be that there are no quantifiers over tn)
    TypeNode tn = n.getType();
    std::map< TypeNode, SortModel* >::iterator it = d_rep_model.find( tn );
    if( it==d_rep_model.end() ){
      SortModel* rm = NULL;
      if( tn.isSort() ){
        Trace("uf-ss-register") << "Create sort model " << tn << "." << std::endl;
        rm  = new SortModel( n, d_th->getSatContext(), d_th->getUserContext(), this );
        //getOutputChannel().lemma( n.eqNode( rm->getCardinalityTerm() ) );
      }else{
        /*
        if( tn==NodeManager::currentNM()->integerType() || tn==NodeManager::currentNM()->realType() ){
          Debug("uf-ss-na") << "Error: Cannot perform finite model finding on arithmetic quantifier";
          Debug("uf-ss-na") << " (" << f << ")";
          Debug("uf-ss-na") << std::endl;
          Unimplemented() << "Cannot perform finite model finding on arithmetic quantifier";
        }else if( tn.isDatatype() ){
          Debug("uf-ss-na") << "Error: Cannot perform finite model finding on datatype quantifier";
          Debug("uf-ss-na") << " (" << f << ")";
          Debug("uf-ss-na") << std::endl;
          Unimplemented() << "Cannot perform finite model finding on datatype quantifier";
        }
        */
      }
      if( rm ){
        rm->initialize( d_out );
        d_rep_model[tn] = rm;
        //d_rep_model_init[tn] = true;
      }
    }else{
      //ensure sort model is initialized
      it->second->initialize( d_out );
    }
  }
}

SortModel* CardinalityExtension::getSortModel(Node n)
{
  TypeNode tn = n.getType();
  std::map< TypeNode, SortModel* >::iterator it = d_rep_model.find( tn );
  //pre-register the type if not done already
  if( it==d_rep_model.end() ){
    preRegisterTerm( n );
    it = d_rep_model.find( tn );
  }
  if( it!=d_rep_model.end() ){
    return it->second;
  }else{
    return NULL;
  }
}

/** get cardinality for sort */
int CardinalityExtension::getCardinality(Node n)
{
  SortModel* c = getSortModel( n );
  if( c ){
    return c->getCardinality();
  }else{
    return -1;
  }
}

int CardinalityExtension::getCardinality(TypeNode tn)
{
  std::map< TypeNode, SortModel* >::iterator it = d_rep_model.find( tn );
  if( it!=d_rep_model.end() && it->second ){
    return it->second->getCardinality();
  }
  return -1;
}

//print debug
void CardinalityExtension::debugPrint(const char* c)
{
  for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
    Debug( c ) << "Conflict find structure for " << it->first << ": " << std::endl;
    it->second->debugPrint( c );
    Debug( c ) << std::endl;
  }
}

bool CardinalityExtension::debugModel(TheoryModel* m)
{
  for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
    if( !it->second->debugModel( m ) ){
      return false;
    }
  }
  return true;
}

/** initialize */
void CardinalityExtension::initializeCombinedCardinality()
{
  if (d_cc_dec_strat.get() != nullptr
      && !d_initializedCombinedCardinality.get())
  {
    d_initializedCombinedCardinality = true;
    d_th->getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_UF_COMBINED_CARD, d_cc_dec_strat.get());
  }
}

/** check */
void CardinalityExtension::checkCombinedCardinality()
{
  Assert(options::ufssMode() == options::UfssMode::FULL);
  if( options::ufssFairness() ){
    Trace("uf-ss-com-card-debug") << "Check combined cardinality, get maximum negative cardinalities..." << std::endl;
    int totalCombinedCard = 0;
    int maxMonoSlave = 0;
    TypeNode maxSlaveType;
    for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
      int max_neg = it->second->getMaximumNegativeCardinality();
      if( !options::ufssFairnessMonotone() ){
        totalCombinedCard += max_neg;
      }else{
        std::map< TypeNode, bool >::iterator its = d_tn_mono_slave.find( it->first );
        if( its==d_tn_mono_slave.end() || !its->second ){
          totalCombinedCard += max_neg;
        }else{
          if( max_neg>maxMonoSlave ){
            maxMonoSlave = max_neg;
            maxSlaveType = it->first;
          }
        }
      }
    }
    Trace("uf-ss-com-card-debug") << "Check combined cardinality, total combined card : " << totalCombinedCard << std::endl;
    if( options::ufssFairnessMonotone() ){
      Trace("uf-ss-com-card-debug") << "Max slave monotonic negated cardinality : " << maxMonoSlave << std::endl;
      if( d_min_pos_tn_master_card.get()!=-1 && maxMonoSlave>d_min_pos_tn_master_card.get() ){
        int mc = d_min_pos_tn_master_card.get();
        std::vector< Node > conf;
        conf.push_back( d_rep_model[d_tn_mono_master]->getCardinalityLiteral( mc ) );
        conf.push_back( d_rep_model[maxSlaveType]->getCardinalityLiteral( maxMonoSlave ).negate() );
        Node cf = NodeManager::currentNM()->mkNode( AND, conf );
        Trace("uf-ss-lemma") << "*** Combined monotone cardinality conflict"
                             << " : " << cf << std::endl;
        Trace("uf-ss-com-card") << "*** Combined monotone cardinality conflict"
                                << " : " << cf << std::endl;
        getOutputChannel().conflict( cf );
        d_conflict.set( true );
        return;
      }
    }
    int cc = d_min_pos_com_card.get();
    if( cc !=-1 && totalCombinedCard > cc ){
      //conflict
      Node com_lit = d_cc_dec_strat->getLiteral(cc);
      std::vector< Node > conf;
      conf.push_back( com_lit );
      int totalAdded = 0;
      for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); 
           it != d_rep_model.end(); ++it ){
        bool doAdd = true;
        if( options::ufssFairnessMonotone() ){
          std::map< TypeNode, bool >::iterator its =
            d_tn_mono_slave.find( it->first );
          if( its!=d_tn_mono_slave.end() && its->second ){
            doAdd = false;
          }
        }
        if( doAdd ){
          int c = it->second->getMaximumNegativeCardinality();
          if( c>0 ){
            conf.push_back( it->second->getCardinalityLiteral( c ).negate() );
            totalAdded += c;
          }
          if( totalAdded>cc ){
            break;
          }
        }
      }
      Node cf = NodeManager::currentNM()->mkNode( AND, conf );
      Trace("uf-ss-lemma") << "*** Combined cardinality conflict : " << cf
                           << std::endl;
      Trace("uf-ss-com-card") << "*** Combined cardinality conflict : " << cf
                              << std::endl;
      getOutputChannel().conflict( cf );
      d_conflict.set( true );
    }
  }
}

CardinalityExtension::Statistics::Statistics()
    : d_clique_conflicts("CardinalityExtension::Clique_Conflicts", 0),
      d_clique_lemmas("CardinalityExtension::Clique_Lemmas", 0),
      d_split_lemmas("CardinalityExtension::Split_Lemmas", 0),
      d_disamb_term_lemmas("CardinalityExtension::Disambiguate_Term_Lemmas", 0),
      d_totality_lemmas("CardinalityExtension::Totality_Lemmas", 0),
      d_max_model_size("CardinalityExtension::Max_Model_Size", 1)
{
  smtStatisticsRegistry()->registerStat(&d_clique_conflicts);
  smtStatisticsRegistry()->registerStat(&d_clique_lemmas);
  smtStatisticsRegistry()->registerStat(&d_split_lemmas);
  smtStatisticsRegistry()->registerStat(&d_disamb_term_lemmas);
  smtStatisticsRegistry()->registerStat(&d_totality_lemmas);
  smtStatisticsRegistry()->registerStat(&d_max_model_size);
}

CardinalityExtension::Statistics::~Statistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_clique_conflicts);
  smtStatisticsRegistry()->unregisterStat(&d_clique_lemmas);
  smtStatisticsRegistry()->unregisterStat(&d_split_lemmas);
  smtStatisticsRegistry()->unregisterStat(&d_disamb_term_lemmas);
  smtStatisticsRegistry()->unregisterStat(&d_totality_lemmas);
  smtStatisticsRegistry()->unregisterStat(&d_max_model_size);
}

}/* CVC4::theory namespace::uf */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
