/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of theory of UF with cardinality.
 */

#include "theory/uf/cardinality_extension.h"

#include <sstream>

#include "expr/cardinality_constraint.h"
#include "expr/skolem_manager.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "smt/logic_exception.h"
#include "theory/decision_manager.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "util/rational.h"

using namespace std;
using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace uf {

/* These are names are unambigious are we use abbreviations. */
typedef CardinalityExtension::SortModel SortModel;
typedef SortModel::Region Region;
typedef Region::RegionNodeInfo RegionNodeInfo;
typedef RegionNodeInfo::DiseqList DiseqList;

Region::Region(SortModel* cf, context::Context* c)
    : d_cf(cf),
      d_testCliqueSize(c, 0),
      d_splitsSize(c, 0),
      d_testClique(c),
      d_splits(c),
      d_reps_size(c, 0),
      d_total_diseq_external(c, 0),
      d_total_diseq_internal(c, 0),
      d_valid(c, true)
{
}

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
  //Trace("uf-ss-region-debug") << "set disequal " << n1 << " " << n2 << " "
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
            Trace("uf-ss-debug") << "removing split for " << n1 << " " << n2
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
    d_nodes[n] = new RegionNodeInfo(d_cf->d_thss->context());
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
          Trace("uf-ss-debug") << "Choose to add clique member "
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
  Trace( c ) << "Num reps: " << d_reps_size << std::endl;
  for( Region::iterator it = begin(); it != end(); ++it ){
    RegionNodeInfo* rni = it->second;
    if( rni->valid() ){
      Node n = it->first;
      Trace( c ) << "   " << n << std::endl;
      for( int i=0; i<2; i++ ){
        Trace( c ) << "      " << ( i==0 ? "Ext" : "Int" ) << " disequal:";
        DiseqList* del = rni->get(i);
        for( DiseqList::iterator it2 = del->begin(); it2 != del->end(); ++it2 ){
          if( (*it2).second ){
            Trace( c ) << " " << (*it2).first;
          }
        }
        Trace( c ) << ", total = " << del->size() << std::endl;
      }
    }
  }
  Trace( c ) << "Total disequal: " << d_total_diseq_external << " external,";
  Trace( c ) << " " << d_total_diseq_internal << " internal." << std::endl;

  if( incClique ){
    if( !d_testClique.empty() ){
      Trace( c ) << "Candidate clique members: " << std::endl;
      Trace( c ) << "   ";
      for( NodeBoolMap::iterator it = d_testClique.begin();
           it != d_testClique.end(); ++ it ){
        if( (*it).second ){
          Trace( c ) << (*it).first << " ";
        }
      }
      Trace( c ) << ", size = " << d_testCliqueSize << std::endl;
    }
    if( !d_splits.empty() ){
      Trace( c ) << "Required splits: " << std::endl;
      Trace( c ) << "   ";
      for( NodeBoolMap::iterator it = d_splits.begin(); it != d_splits.end();
           ++ it ){
        if( (*it).second ){
          Trace( c ) << (*it).first << " ";
        }
      }
      Trace( c ) << ", size = " << d_splitsSize << std::endl;
    }
  }
}

SortModel::CardinalityDecisionStrategy::CardinalityDecisionStrategy(
    Env& env, TypeNode type, Valuation valuation)
    : DecisionStrategyFmf(env, valuation), d_type(type)
{
}

Node SortModel::CardinalityDecisionStrategy::mkLiteral(unsigned i)
{
  NodeManager* nm = NodeManager::currentNM();
  Node cco = nm->mkConst(CardinalityConstraint(d_type, Integer(i + 1)));
  return nm->mkNode(CARDINALITY_CONSTRAINT, cco);
}

std::string SortModel::CardinalityDecisionStrategy::identify() const
{
  return std::string("uf_card");
}

SortModel::SortModel(Env& env,
                     TypeNode tn,
                     TheoryState& state,
                     TheoryInferenceManager& im,
                     CardinalityExtension* thss)
    : EnvObj(env),
      d_type(tn),
      d_state(state),
      d_im(im),
      d_thss(thss),
      d_regions_index(thss->context(), 0),
      d_regions_map(thss->context()),
      d_split_score(thss->context()),
      d_disequalities_index(thss->context(), 0),
      d_reps(thss->context(), 0),
      d_cardinality(thss->context(), 1),
      d_hasCard(thss->context(), false),
      d_maxNegCard(thss->context(), 0),
      d_initialized(thss->userContext(), false),
      d_c_dec_strat(nullptr)
{
  if (options().uf.ufssMode == options::UfssMode::FULL)
  {
    // Register the strategy with the decision manager of the theory.
    // We are guaranteed that the decision manager is ready since we
    // construct this module during TheoryUF::finishInit.
    d_c_dec_strat.reset(new CardinalityDecisionStrategy(
        thss->d_env, d_type, thss->getTheory()->getValuation()));
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
void SortModel::initialize()
{
  if (d_c_dec_strat.get() != nullptr && !d_initialized)
  {
    d_initialized = true;
    // Strategy is user-context-dependent, since it is in sync with
    // user-context-dependent flag d_initialized.
    d_im.getDecisionManager()->registerStrategy(DecisionManager::STRAT_UF_CARD,
                                                d_c_dec_strat.get());
  }
}

/** new node */
void SortModel::newEqClass( Node n ){
  if (!d_state.isInConflict())
  {
    if( d_regions_map.find( n )==d_regions_map.end() ){
      d_regions_map[n] = d_regions_index;
      Trace("uf-ss") << "CardinalityExtension: New Eq Class " << n << std::endl;
      Trace("uf-ss-debug") << d_regions_index << " " << (int)d_regions.size()
                           << std::endl;
      if (d_regions_index < d_regions.size())
      {
        d_regions[d_regions_index]->debugPrint("uf-ss-debug", true);
        d_regions[d_regions_index]->setValid(true);
        Assert(d_regions[d_regions_index]->getNumReps() == 0);
      }else{
        d_regions.push_back(new Region(this, d_thss->context()));
      }
      d_regions[d_regions_index]->addRep(n);
      d_regions_index = d_regions_index + 1;

      d_reps = d_reps + 1;
    }
  }
}

/** merge */
void SortModel::merge( Node a, Node b ){
  if (d_state.isInConflict())
  {
    return;
  }
  Trace("uf-ss") << "CardinalityExtension: Merging " << a << " = " << b << "..."
                 << std::endl;
  if (a != b)
  {
    Assert(d_regions_map.find(a) != d_regions_map.end());
    Assert(d_regions_map.find(b) != d_regions_map.end());
    int ai = d_regions_map[a];
    int bi = d_regions_map[b];
    Trace("uf-ss") << "   regions: " << ai << " " << bi << std::endl;
    if (ai != bi)
    {
      if (d_regions[ai]->getNumReps() == 1)
      {
        int ri = combineRegions(bi, ai);
        d_regions[ri]->setEqual(a, b);
        checkRegion(ri);
      }
      else if (d_regions[bi]->getNumReps() == 1)
      {
        int ri = combineRegions(ai, bi);
        d_regions[ri]->setEqual(a, b);
        checkRegion(ri);
      }
      else
      {
        // Either move a to d_regions[bi], or b to d_regions[ai].
        RegionNodeInfo* a_region_info = d_regions[ai]->getRegionInfo(a);
        RegionNodeInfo* b_region_info = d_regions[bi]->getRegionInfo(b);
        int aex = (a_region_info->getNumInternalDisequalities()
                   - getNumDisequalitiesToRegion(a, bi));
        int bex = (b_region_info->getNumInternalDisequalities()
                   - getNumDisequalitiesToRegion(b, ai));
        // Based on which would produce the fewest number of
        // external disequalities.
        if (aex < bex)
        {
          moveNode(a, bi);
          d_regions[bi]->setEqual(a, b);
        }else{
          moveNode(b, ai);
          d_regions[ai]->setEqual( a, b );
        }
        checkRegion(ai);
        checkRegion(bi);
      }
    }
    else
    {
      d_regions[ai]->setEqual(a, b);
      checkRegion(ai);
    }
    d_regions_map[b] = -1;
  }
  d_reps = d_reps - 1;
}

/** assert terms are disequal */
void SortModel::assertDisequal( Node a, Node b, Node reason ){
  if (d_state.isInConflict())
  {
    return;
  }
  // if they are not already disequal
  eq::EqualityEngine* ee = d_thss->getTheory()->getEqualityEngine();
  a = ee->getRepresentative(a);
  b = ee->getRepresentative(b);
  int ai = d_regions_map[a];
  int bi = d_regions_map[b];
  if (d_regions[ai]->isDisequal(a, b, ai == bi))
  {
    // already disequal
    return;
  }
  Trace("uf-ss") << "Assert disequal " << a << " != " << b << "..."
                 << std::endl;
  Trace("uf-ss-disequal") << "Assert disequal " << a << " != " << b << "..."
                          << std::endl;
  // add to list of disequalities
  if (d_disequalities_index < d_disequalities.size())
  {
    d_disequalities[d_disequalities_index] = reason;
  }
  else
  {
    d_disequalities.push_back(reason);
  }
  d_disequalities_index = d_disequalities_index + 1;
  // now, add disequalities to regions
  Assert(d_regions_map.find(a) != d_regions_map.end());
  Assert(d_regions_map.find(b) != d_regions_map.end());
  Trace("uf-ss") << "   regions: " << ai << " " << bi << std::endl;
  if (ai == bi)
  {
    // internal disequality
    d_regions[ai]->setDisequal(a, b, 1, true);
    d_regions[ai]->setDisequal(b, a, 1, true);
    // do not need to check if it needs to combine (no new ext. disequalities)
    checkRegion(ai, false);
  }
  else
  {
    // external disequality
    d_regions[ai]->setDisequal(a, b, 0, true);
    d_regions[bi]->setDisequal(b, a, 0, true);
    checkRegion(ai);
    checkRegion(bi);
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

void SortModel::check(Theory::Effort level)
{
  Assert(options().uf.ufssMode == options::UfssMode::FULL);
  if (!d_hasCard && d_state.isInConflict())
  {
    // not necessary to check
    return;
  }
  Trace("uf-ss") << "CardinalityExtension: Check " << level << " " << d_type
                 << std::endl;
  if (level == Theory::EFFORT_FULL)
  {
    Trace("fmf-full-check") << std::endl;
    Trace("fmf-full-check")
        << "Full check for SortModel " << d_type << ", status : " << std::endl;
    debugPrint("fmf-full-check");
    Trace("fmf-full-check") << std::endl;
  }
  if (d_reps <= (unsigned)d_cardinality)
  {
    Trace("uf-ss-debug") << "We have " << d_reps << " representatives for type "
                         << d_type << ", <= " << d_cardinality << std::endl;
    if( level==Theory::EFFORT_FULL ){
      Trace("uf-ss-sat") << "We have " << d_reps << " representatives for type "
                         << d_type << ", <= " << d_cardinality << std::endl;
    }
    return;
  }
  // first check if we can generate a clique conflict
  // do a check within each region
  for (size_t i = 0; i < d_regions_index; i++)
  {
    if (d_regions[i]->valid())
    {
      std::vector<Node> clique;
      if (d_regions[i]->check(level, d_cardinality, clique))
      {
        // add clique lemma
        addCliqueLemma(clique);
        return;
      }
      else
      {
        Trace("uf-ss-debug") << "No clique in Region #" << i << std::endl;
      }
    }
  }
  // do splitting on demand
  bool addedLemma = false;
  if (level == Theory::EFFORT_FULL)
  {
    Trace("uf-ss-debug") << "Add splits?" << std::endl;
    // see if we have any recommended splits from large regions
    for (size_t i = 0; i < d_regions_index; i++)
    {
      if (d_regions[i]->valid() && d_regions[i]->getNumReps() > d_cardinality)
      {
        int sp = addSplit(d_regions[i]);
        if (sp == 1)
        {
          addedLemma = true;
        }
        else if (sp == -1)
        {
          check(level);
          return;
        }
      }
    }
  }
  // If no added lemmas, force continuation via combination of regions.
  if (level != Theory::EFFORT_FULL || addedLemma)
  {
    return;
  }
  // check at full effort
  Trace("uf-ss-debug") << "No splits added. " << d_cardinality << std::endl;
  Trace("uf-ss-si") << "Must combine region" << std::endl;
  bool recheck = false;
  SortInference* si = d_state.getSortInference();
  if (si != nullptr)
  {
    // If sort inference is enabled, search for regions with same sort.
    std::map<int, int> sortsFound;
    for (size_t i = 0; i < d_regions_index; i++)
    {
      if (d_regions[i]->valid())
      {
        Node op = d_regions[i]->frontKey();
        int sort_id = si->getSortId(op);
        if (sortsFound.find(sort_id) != sortsFound.end())
        {
          Trace("fmf-full-check") << "Combined regions " << i << " "
                                  << sortsFound[sort_id] << std::endl;
          combineRegions(sortsFound[sort_id], i);
          recheck = true;
          break;
        }
        else
        {
          sortsFound[sort_id] = i;
        }
      }
    }
  }
  if (!recheck)
  {
    // naive strategy, force region combination involving the first
    // valid region
    for (size_t i = 0; i < d_regions_index; i++)
    {
      if (d_regions[i]->valid())
      {
        int fcr = forceCombineRegion(i, false);
        Trace("fmf-full-check")
            << "Combined regions " << i << " " << fcr << std::endl;
        Trace("uf-ss-debug")
            << "Combined regions " << i << " " << fcr << std::endl;
        recheck = true;
        break;
      }
    }
  }
  if (recheck)
  {
    Trace("uf-ss-debug") << "Must recheck." << std::endl;
    check(level);
  }
}

void SortModel::presolve() {
  d_initialized = false;
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

void SortModel::assertCardinality(uint32_t c, bool val)
{
  if (!d_state.isInConflict())
  {
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
      if (!prevHasCard || c < d_cardinality)
      {
        d_cardinality = c;
        simpleCheckCardinality();
        if (d_state.isInConflict())
        {
          return;
        }
      }
      //should check all regions now
      if (doCheckRegions)
      {
        for (size_t i = 0; i < d_regions_index; i++)
        {
          if( d_regions[i]->valid() ){
            checkRegion( i );
            if (d_state.isInConflict())
            {
              return;
            }
          }
        }
      }
      // we assert it positively, if its beyond the bound, abort
      if (options().uf.ufssAbortCardinality >= 0
          && c >= static_cast<uint32_t>(options().uf.ufssAbortCardinality))
      {
        std::stringstream ss;
        ss << "Maximum cardinality (" << options().uf.ufssAbortCardinality
           << ")  for finite model finding exceeded." << std::endl;
        throw LogicException(ss.str());
      }
    }
    else
    {
      if (c > d_maxNegCard.get())
      {
        Trace("uf-ss-com-card-debug") << "Maximum negative cardinality for "
                                      << d_type << " is now " << c << std::endl;
        d_maxNegCard.set(c);
        simpleCheckCardinality();
      }
    }
  }
}

void SortModel::checkRegion( int ri, bool checkCombine ){
  if( isValid(ri) && d_hasCard ){
    Assert(d_cardinality > 0);
    if( checkCombine && d_regions[ri]->getMustCombine( d_cardinality ) ){
      int riNew = forceCombineRegion( ri, true );
      if( riNew>=0 ){
        checkRegion( riNew, checkCombine );
      }
    }
    //now check if region is in conflict
    std::vector< Node > clique;
    if( d_regions[ri]->check( Theory::EFFORT_STANDARD, d_cardinality, clique ) ){
      //explain clique
      addCliqueLemma(clique);
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
    if( TraceIsOn("uf-ss-check-region") ){
      Trace("uf-ss-check-region") << "We must combine Region #" << ri << ". " << std::endl;
      d_regions[ri]->debugPrint("uf-ss-check-region");
    }
    //take region with maximum disequality density
    double maxScore = 0;
    int maxRegion = -1;
    std::map< int, int > regions_diseq;
    getDisequalitiesToRegions( ri, regions_diseq );
    for( std::map< int, int >::iterator it = regions_diseq.begin(); it != regions_diseq.end(); ++it ){
      Trace("uf-ss-check-region") << it->first << " : " << it->second << std::endl;
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
      if( TraceIsOn("uf-ss-check-region") ){
        Trace("uf-ss-check-region") << "Combine with region #" << maxRegion << ":" << std::endl;
        d_regions[maxRegion]->debugPrint("uf-ss-check-region");
      }
      return combineRegions( ri, maxRegion );
    }
    return -1;
  }
}


int SortModel::combineRegions( int ai, int bi ){
  Trace("uf-ss-region") << "uf-ss: Combine Region #" << bi << " with Region #" << ai << std::endl;
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
  Trace("uf-ss-region") << "uf-ss: Move node " << n << " to Region #" << ri << std::endl;
  Assert(isValid(d_regions_map[n]));
  Assert(isValid(ri));
  //move node to region ri
  d_regions[ri]->takeNode( d_regions[ d_regions_map[n] ], n );
  d_regions_map[n] = ri;
}

int SortModel::addSplit(Region* r)
{
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
    Node ss = rewrite(s);
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
      if (ss == b_t)
      {
        AlwaysAssert(false) << "Bad split " << s << std::endl;
      }
    }
    if (TraceIsOn("uf-ss-split-si"))
    {
      SortInference* si = d_state.getSortInference();
      if (si != nullptr)
      {
        for (size_t i = 0; i < 2; i++)
        {
          int sid = si->getSortId(ss[i]);
          Trace("uf-ss-split-si") << sid << " ";
        }
        Trace("uf-ss-split-si") << std::endl;
      }
    }
    //Trace("uf-ss-lemma") << d_th->getEqualityEngine()->areEqual( s[0], s[1] ) << " ";
    //Trace("uf-ss-lemma") << d_th->getEqualityEngine()->areDisequal( s[0], s[1] ) << std::endl;
    //Trace("uf-ss-lemma") << s[0].getType() << " " << s[1].getType() << std::endl;
    //split on the equality s
    Node lem = NodeManager::currentNM()->mkNode( kind::OR, ss, ss.negate() );
    // send lemma, with caching
    if (d_im.lemma(lem, InferenceId::UF_CARD_SPLIT))
    {
      Trace("uf-ss-lemma") << "*** Split on " << s << std::endl;
      //tell the sat solver to explore the equals branch first
      d_im.requirePhase(ss, true);
      ++( d_thss->d_statistics.d_split_lemmas );
    }
    return 1;
  }else{
    return 0;
  }
}

void SortModel::addCliqueLemma(std::vector<Node>& clique)
{
  Assert(d_hasCard);
  Assert(d_cardinality > 0);
  while (clique.size() > d_cardinality + 1)
  {
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
  // send lemma, with caching
  if (d_im.lemma(lem, InferenceId::UF_CARD_CLIQUE))
  {
    Trace("uf-ss-lemma") << "*** Add clique lemma " << lem << std::endl;
    ++(d_thss->d_statistics.d_clique_lemmas);
  }
}

void SortModel::simpleCheckCardinality() {
  if( d_maxNegCard.get()!=0 && d_hasCard.get() && d_cardinality.get()<d_maxNegCard.get() ){
    Node lem = NodeManager::currentNM()->mkNode( AND, getCardinalityLiteral( d_cardinality.get() ),
                                                      getCardinalityLiteral( d_maxNegCard.get() ).negate() );
    Trace("uf-ss-lemma") << "*** Simple cardinality conflict : " << lem << std::endl;
    d_im.conflict(lem, InferenceId::UF_CARD_SIMPLE_CONFLICT);
  }
}

void SortModel::debugPrint( const char* c ){
  if( TraceIsOn( c ) ){
    Trace( c ) << "Number of reps = " << d_reps << std::endl;
    Trace( c ) << "Cardinality req = " << d_cardinality << std::endl;
    unsigned debugReps = 0;
    for( unsigned i=0; i<d_regions_index; i++ ){
      Region* region = d_regions[i]; 
      if( region->valid() ){
        Trace( c ) << "Region #" << i << ": " << std::endl;
        region->debugPrint( c, true );
        Trace( c ) << std::endl;
        for( Region::iterator it = region->begin(); it != region->end(); ++it ){
          if( it->second->valid() ){
            if( d_regions_map[ it->first ]!=(int)i ){
              Trace( c ) << "***Bad regions map : " << it->first
                         << " " << d_regions_map[ it->first ].get() << std::endl;
            }
          }
        }
        debugReps += region->getNumReps();
      }
    }

    if( debugReps!=d_reps ){
      Trace( c ) << "***Bad reps: " << d_reps << ", "
                 << "actual = " << debugReps << std::endl;
    }
  }
}

bool SortModel::checkLastCall()
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  TheoryModel* m = d_state.getModel();
  if( TraceIsOn("uf-ss-warn") ){
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
  size_t nReps = rs->getNumRepresentatives(d_type);
  if (nReps != d_maxNegCard + 1)
  {
    Trace("uf-ss-warn") << "WARNING : Model does not have same # "
                           "representatives as cardinality for "
                        << d_type << "." << std::endl;
    Trace("uf-ss-warn") << "   Max neg cardinality : " << d_maxNegCard
                        << std::endl;
    Trace("uf-ss-warn") << "   # Reps : " << nReps << std::endl;
    if (d_maxNegCard >= nReps)
    {
      while (d_fresh_aloc_reps.size() <= d_maxNegCard)
      {
        std::stringstream ss;
        ss << "r_" << d_type << "_";
        Node nn = sm->mkDummySkolem(
            ss.str(), d_type, "enumeration to meet negative card constraint");
        d_fresh_aloc_reps.push_back( nn );
      }
      if (d_maxNegCard == 0)
      {
        rs->d_type_reps[d_type].push_back(d_fresh_aloc_reps[0]);
      }
      else
      {
        //must add lemma
        std::vector< Node > force_cl;
        for (size_t i = 0; i <= d_maxNegCard; i++)
        {
          for (size_t j = (i + 1); j <= d_maxNegCard; j++)
          {
            force_cl.push_back(
                d_fresh_aloc_reps[i].eqNode(d_fresh_aloc_reps[j]).negate());
          }
        }
        Node cl = getCardinalityLiteral( d_maxNegCard );
        Node lem = nm->mkNode(OR, cl, nm->mkAnd(force_cl));
        Trace("uf-ss-lemma") << "*** Enforce negative cardinality constraint lemma : " << lem << std::endl;
        d_im.lemma(lem, InferenceId::UF_CARD_ENFORCE_NEGATIVE);
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

Node SortModel::getCardinalityLiteral(uint32_t c)
{
  Assert(c > 0);
  std::map<uint32_t, Node>::iterator itcl = d_cardinality_literal.find(c);
  if (itcl != d_cardinality_literal.end())
  {
    return itcl->second;
  }
  // get the literal from the decision strategy
  Node lit = d_c_dec_strat->getLiteral(c - 1);
  d_cardinality_literal[c] = lit;

  // return the literal
  return lit;
}

CardinalityExtension::CardinalityExtension(Env& env,
                                           TheoryState& state,
                                           TheoryInferenceManager& im,
                                           TheoryUF* th)
    : EnvObj(env),
      d_statistics(statisticsRegistry()),
      d_state(state),
      d_im(im),
      d_th(th),
      d_rep_model(),
      d_min_pos_com_card(context(), 0),
      d_min_pos_com_card_set(context(), false),
      d_cc_dec_strat(nullptr),
      d_initializedCombinedCardinality(userContext(), false),
      d_card_assertions_eqv_lemma(userContext()),
      d_min_pos_tn_master_card(context(), 0),
      d_min_pos_tn_master_card_set(context(), false),
      d_rel_eqc(context())
{
  if (options().uf.ufssMode == options::UfssMode::FULL
      && options().uf.ufssFairness)
  {
    // Register the strategy with the decision manager of the theory.
    // We are guaranteed that the decision manager is ready since we
    // construct this module during TheoryUF::finishInit.
    d_cc_dec_strat.reset(
        new CombinedCardinalityDecisionStrategy(env, th->getValuation()));
  }
}

CardinalityExtension::~CardinalityExtension()
{
  for (std::map<TypeNode, SortModel*>::iterator it = d_rep_model.begin();
       it != d_rep_model.end(); ++it) {
    delete it->second;
  }
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
    Trace("uf-ss-solver") << "CardinalityExtension: New eq class " << a << " : "
                          << a.getType() << std::endl;
    c->newEqClass( a );
    Trace("uf-ss-solver") << "CardinalityExtension: Done New eq class."
                          << std::endl;
  }
}

/** merge */
void CardinalityExtension::merge(Node a, Node b)
{
  //TODO: ensure they are relevant
  SortModel* c = getSortModel( a );
  if( c ){
    Trace("uf-ss-solver") << "CardinalityExtension: Merge " << a << " " << b
                          << " : " << a.getType() << std::endl;
    c->merge( a, b );
    Trace("uf-ss-solver") << "CardinalityExtension: Done Merge." << std::endl;
  }
}

/** assert terms are disequal */
void CardinalityExtension::assertDisequal(Node a, Node b, Node reason)
{
  SortModel* c = getSortModel( a );
  if( c ){
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
  bool polarity = n.getKind() != kind::NOT;
  TNode lit = polarity ? n : n[0];
  if (options().uf.ufssMode == options::UfssMode::FULL)
  {
    if( lit.getKind()==CARDINALITY_CONSTRAINT ){
      const CardinalityConstraint& cc =
          lit.getOperator().getConst<CardinalityConstraint>();
      TypeNode tn = cc.getType();
      Assert(tn.isUninterpretedSort());
      Assert(d_rep_model[tn]);
      uint32_t nCard = cc.getUpperBound().getUnsignedInt();
      Trace("uf-ss-debug") << "...check cardinality constraint : " << tn
                           << std::endl;
      if (options().uf.ufssFairnessMonotone)
      {
        SortInference* si = d_state.getSortInference();
        Trace("uf-ss-com-card-debug") << "...set master/slave" << std::endl;
        if (tn != d_tn_mono_master)
        {
          std::map<TypeNode, bool>::iterator it = d_tn_mono_slave.find(tn);
          if (it == d_tn_mono_slave.end())
          {
            bool isMonotonic;
            if (si != nullptr)
            {
              isMonotonic = si->isMonotonic(tn);
            }
            else
            {
              // if ground, everything is monotonic
              isMonotonic = true;
            }
            if (isMonotonic)
            {
              if (d_tn_mono_master.isNull())
              {
                Trace("uf-ss-com-card-debug")
                    << "uf-ss-fair-monotone: Set master : " << tn << std::endl;
                d_tn_mono_master = tn;
              }
              else
              {
                Trace("uf-ss-com-card-debug")
                    << "uf-ss-fair-monotone: Set slave : " << tn << std::endl;
                d_tn_mono_slave[tn] = true;
              }
            }
            else
            {
              Trace("uf-ss-com-card-debug")
                  << "uf-ss-fair-monotone: Set non-monotonic : " << tn
                  << std::endl;
              d_tn_mono_slave[tn] = false;
            }
          }
        }
        // set the minimum positive cardinality for master if necessary
        if (polarity && tn == d_tn_mono_master)
        {
          Trace("uf-ss-com-card-debug")
              << "...set min positive cardinality" << std::endl;
          if (!d_min_pos_tn_master_card_set.get()
              || nCard < d_min_pos_tn_master_card.get())
          {
            d_min_pos_tn_master_card_set.set(true);
            d_min_pos_tn_master_card.set(nCard);
          }
        }
      }
      Trace("uf-ss-com-card-debug") << "...assert cardinality" << std::endl;
      d_rep_model[tn]->assertCardinality(nCard, polarity);
      // check if combined cardinality is violated
      checkCombinedCardinality();
    }else if( lit.getKind()==COMBINED_CARDINALITY_CONSTRAINT ){
      if( polarity ){
        //safe to assume int here
        const CombinedCardinalityConstraint& cc =
            lit.getOperator().getConst<CombinedCardinalityConstraint>();
        uint32_t nCard = cc.getUpperBound().getUnsignedInt();
        if (!d_min_pos_com_card_set.get() || nCard < d_min_pos_com_card.get())
        {
          d_min_pos_com_card_set.set(true);
          d_min_pos_com_card.set( nCard );
          checkCombinedCardinality();
        }
      }
    }else{
      if( TraceIsOn("uf-ss-warn") ){
        ////FIXME: this is too strict: theory propagations are showing up as isDecision=true, but
        ////       a theory propagation is not a decision.
        if( isDecision ){
          for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
            if( !it->second->hasCardinalityAsserted() ){
              Trace("uf-ss-warn") << "WARNING: Assert " << n << " as a decision before cardinality for " << it->first << "." << std::endl;
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
      d_im.setModelUnsound(IncompleteId::UF_CARD_MODE);
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
  if (level == Theory::EFFORT_LAST_CALL)
  {
    // if last call, call last call check for each sort
    for (std::pair<const TypeNode, SortModel*>& r : d_rep_model)
    {
      if (!r.second->checkLastCall())
      {
        break;
      }
    }
    return;
  }
  if (!d_state.isInConflict())
  {
    if (options().uf.ufssMode == options::UfssMode::FULL)
    {
      Trace("uf-ss-solver")
          << "CardinalityExtension: check " << level << std::endl;
      if (level == Theory::EFFORT_FULL)
      {
        if (TraceIsOn("uf-ss-debug"))
        {
          debugPrint("uf-ss-debug");
        }
        if (TraceIsOn("uf-ss-state"))
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
        it->second->check(level);
        if (d_state.isInConflict())
        {
          break;
        }
      }
    }
    else if (options().uf.ufssMode == options::UfssMode::NO_MINIMAL)
    {
      if( level==Theory::EFFORT_FULL ){
        // split on an equality between two equivalence classes (at most one per type)
        std::map< TypeNode, std::vector< Node > > eqc_list;
        std::map< TypeNode, bool > type_proc;
        eq::EqClassesIterator eqcs_i(d_th->getEqualityEngine());
        while( !eqcs_i.isFinished() ){
          Node a = *eqcs_i;
          TypeNode tn = a.getType();
          if (tn.isUninterpretedSort())
          {
            if( type_proc.find( tn )==type_proc.end() ){
              std::map< TypeNode, std::vector< Node > >::iterator itel = eqc_list.find( tn );
              if( itel!=eqc_list.end() ){
                for( unsigned j=0; j<itel->second.size(); j++ ){
                  Node b = itel->second[j];
                  if( !d_th->getEqualityEngine()->areDisequal( a, b, false ) ){
                    Node eq = rewrite(a.eqNode(b));
                    Node lem = NodeManager::currentNM()->mkNode( kind::OR, eq, eq.negate() );
                    Trace("uf-ss-lemma") << "*** Split (no-minimal) : " << lem << std::endl;
                    d_im.lemma(lem, InferenceId::UF_CARD_SPLIT);
                    d_im.requirePhase(eq, true);
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
    it->second->initialize();
  }
}

CardinalityExtension::CombinedCardinalityDecisionStrategy::
    CombinedCardinalityDecisionStrategy(Env& env, Valuation valuation)
    : DecisionStrategyFmf(env, valuation)
{
}
Node CardinalityExtension::CombinedCardinalityDecisionStrategy::mkLiteral(
    unsigned i)
{
  NodeManager* nm = NodeManager::currentNM();
  Node cco = nm->mkConst(CombinedCardinalityConstraint(Integer(i)));
  return nm->mkNode(COMBINED_CARDINALITY_CONSTRAINT, cco);
}

std::string
CardinalityExtension::CombinedCardinalityDecisionStrategy::identify() const
{
  return std::string("uf_combined_card");
}

void CardinalityExtension::preRegisterTerm(TNode n)
{
  if (options().uf.ufssMode != options::UfssMode::FULL)
  {
    return;
  }
  // initialize combined cardinality
  initializeCombinedCardinality();

  Trace("uf-ss-register") << "Preregister " << n << "." << std::endl;
  // shouldn't have to preregister this type (it may be that there are no
  // quantifiers over tn)
  TypeNode tn;
  if (n.getKind() == CARDINALITY_CONSTRAINT)
  {
    const CardinalityConstraint& cc =
        n.getOperator().getConst<CardinalityConstraint>();
    tn = cc.getType();
  }
  else
  {
    tn = n.getType();
  }
  if (!tn.isUninterpretedSort())
  {
    return;
  }
  std::map<TypeNode, SortModel*>::iterator it = d_rep_model.find(tn);
  if (it == d_rep_model.end())
  {
    SortModel* rm = nullptr;
    if (tn.isUninterpretedSort())
    {
      Trace("uf-ss-register") << "Create sort model " << tn << "." << std::endl;
      rm = new SortModel(d_env, tn, d_state, d_im, this);
    }
    if (rm)
    {
      rm->initialize();
      d_rep_model[tn] = rm;
      // d_rep_model_init[tn] = true;
    }
  }
  else
  {
    // ensure sort model is initialized
    it->second->initialize();
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
    Trace( c ) << "Conflict find structure for " << it->first << ": " << std::endl;
    it->second->debugPrint( c );
    Trace( c ) << std::endl;
  }
}

/** initialize */
void CardinalityExtension::initializeCombinedCardinality()
{
  if (d_cc_dec_strat.get() != nullptr
      && !d_initializedCombinedCardinality.get())
  {
    d_initializedCombinedCardinality = true;
    d_im.getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_UF_COMBINED_CARD, d_cc_dec_strat.get());
  }
}

/** check */
void CardinalityExtension::checkCombinedCardinality()
{
  Assert(options().uf.ufssMode == options::UfssMode::FULL);
  if (options().uf.ufssFairness)
  {
    Trace("uf-ss-com-card-debug") << "Check combined cardinality, get maximum negative cardinalities..." << std::endl;
    uint32_t totalCombinedCard = 0;
    uint32_t maxMonoSlave = 0;
    TypeNode maxSlaveType;
    for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
      uint32_t max_neg = it->second->getMaximumNegativeCardinality();
      if (!options().uf.ufssFairnessMonotone)
      {
        totalCombinedCard += max_neg;
      }
      else
      {
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
    if (options().uf.ufssFairnessMonotone)
    {
      Trace("uf-ss-com-card-debug") << "Max slave monotonic negated cardinality : " << maxMonoSlave << std::endl;
      if (!d_min_pos_tn_master_card_set.get()
          && maxMonoSlave > d_min_pos_tn_master_card.get())
      {
        uint32_t mc = d_min_pos_tn_master_card.get();
        std::vector< Node > conf;
        conf.push_back( d_rep_model[d_tn_mono_master]->getCardinalityLiteral( mc ) );
        conf.push_back( d_rep_model[maxSlaveType]->getCardinalityLiteral( maxMonoSlave ).negate() );
        Node cf = NodeManager::currentNM()->mkNode( AND, conf );
        Trace("uf-ss-lemma") << "*** Combined monotone cardinality conflict"
                             << " : " << cf << std::endl;
        Trace("uf-ss-com-card") << "*** Combined monotone cardinality conflict"
                                << " : " << cf << std::endl;
        d_im.conflict(cf, InferenceId::UF_CARD_MONOTONE_COMBINED);
        return;
      }
    }
    uint32_t cc = d_min_pos_com_card.get();
    if (d_min_pos_com_card_set.get() && totalCombinedCard > cc)
    {
      //conflict
      Node com_lit = d_cc_dec_strat->getLiteral(cc);
      std::vector< Node > conf;
      conf.push_back( com_lit );
      uint32_t totalAdded = 0;
      for( std::map< TypeNode, SortModel* >::iterator it = d_rep_model.begin(); 
           it != d_rep_model.end(); ++it ){
        bool doAdd = true;
        if (options().uf.ufssFairnessMonotone)
        {
          std::map< TypeNode, bool >::iterator its =
            d_tn_mono_slave.find( it->first );
          if( its!=d_tn_mono_slave.end() && its->second ){
            doAdd = false;
          }
        }
        if( doAdd ){
          uint32_t c = it->second->getMaximumNegativeCardinality();
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
      d_im.conflict(cf, InferenceId::UF_CARD_COMBINED);
    }
  }
}

CardinalityExtension::Statistics::Statistics(StatisticsRegistry& sr)
    : d_clique_conflicts(
        sr.registerInt("CardinalityExtension::Clique_Conflicts")),
      d_clique_lemmas(sr.registerInt("CardinalityExtension::Clique_Lemmas")),
      d_split_lemmas(sr.registerInt("CardinalityExtension::Split_Lemmas")),
      d_max_model_size(sr.registerInt("CardinalityExtension::Max_Model_Size"))
{
  d_max_model_size.maxAssign(1);
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
