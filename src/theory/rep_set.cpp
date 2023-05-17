/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of representative set.
 */

#include <unordered_set>

#include "theory/rep_set.h"
#include "theory/type_enumerator.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

void RepSet::clear(){
  d_type_reps.clear();
  d_type_complete.clear();
  d_tmap.clear();
  d_values_to_terms.clear();
}

bool RepSet::hasRep(TypeNode tn, Node n) const
{
  std::map<TypeNode, std::vector<Node> >::const_iterator it =
      d_type_reps.find(tn);
  if( it==d_type_reps.end() ){
    return false;
  }else{
    return std::find( it->second.begin(), it->second.end(), n )!=it->second.end();
  }
}

size_t RepSet::getNumRepresentatives(TypeNode tn) const
{
  const std::vector<Node>* reps = getTypeRepsOrNull(tn);
  return (reps != nullptr) ? reps->size() : 0;
}

Node RepSet::getRepresentative(TypeNode tn, unsigned i) const
{
  std::map<TypeNode, std::vector<Node> >::const_iterator it =
      d_type_reps.find(tn);
  Assert(it != d_type_reps.end());
  Assert(i < it->second.size());
  return it->second[i];
}

const std::vector<Node>* RepSet::getTypeRepsOrNull(TypeNode tn) const
{
  auto it = d_type_reps.find(tn);
  if (it == d_type_reps.end())
  {
    return nullptr;
  }
  return &(it->second);
}

namespace {

bool containsStoreAll(Node n, std::unordered_set<Node>& cache)
{
  if( std::find( cache.begin(), cache.end(), n )==cache.end() ){
    cache.insert(n);
    if( n.getKind()==STORE_ALL ){
      return true;
    }else{
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( containsStoreAll( n[i], cache ) ){
          return true;
        }
      }
    }
  }
  return false;
}

}  // namespace

void RepSet::add( TypeNode tn, Node n ){
  //for now, do not add array constants FIXME
  if( tn.isArray() ){
    std::unordered_set<Node> cache;
    if( containsStoreAll( n, cache ) ){
      return;
    }
  }
  Trace("rsi-debug") << "Add rep #" << d_type_reps[tn].size() << " for " << tn << " : " << n << std::endl;
  Assert(n.getType() == tn);
  d_tmap[ n ] = (int)d_type_reps[tn].size();
  d_type_reps[tn].push_back( n );
}

int RepSet::getIndexFor( Node n ) const {
  std::map< Node, int >::const_iterator it = d_tmap.find( n );
  if( it!=d_tmap.end() ){
    return it->second;
  }else{
    return -1;
  }
}

bool RepSet::complete( TypeNode t ){
  std::map< TypeNode, bool >::iterator it = d_type_complete.find( t );
  if( it==d_type_complete.end() ){
    //remove all previous
    for( unsigned i=0; i<d_type_reps[t].size(); i++ ){
      d_tmap.erase( d_type_reps[t][i] );
    }
    d_type_reps[t].clear();
    //now complete the type
    d_type_complete[t] = true;
    TypeEnumerator te(t);
    while( !te.isFinished() ){
      Node n = *te;
      if( std::find( d_type_reps[t].begin(), d_type_reps[t].end(), n )==d_type_reps[t].end() ){
        add( t, n );
      }
      ++te;
    }
    for( size_t i=0; i<d_type_reps[t].size(); i++ ){
      Trace("reps-complete") << d_type_reps[t][i] << " ";
    }
    Trace("reps-complete") << std::endl;
    return true;
  }else{
    return it->second;
  }
}

Node RepSet::getTermForRepresentative(Node n) const
{
  std::map<Node, Node>::const_iterator it = d_values_to_terms.find(n);
  if (it != d_values_to_terms.end())
  {
    return it->second;
  }
  else
  {
    return Node::null();
  }
}

void RepSet::setTermForRepresentative(Node n, Node t)
{
  d_values_to_terms[n] = t;
}

Node RepSet::getDomainValue(TypeNode tn, const std::vector<Node>& exclude) const
{
  std::map<TypeNode, std::vector<Node> >::const_iterator it =
      d_type_reps.find(tn);
  if (it != d_type_reps.end())
  {
    // try to find a pre-existing arbitrary element
    for (size_t i = 0; i < it->second.size(); i++)
    {
      if (std::find(exclude.begin(), exclude.end(), it->second[i])
          == exclude.end())
      {
        return it->second[i];
      }
    }
  }
  return Node::null();
}

void RepSet::toStream(std::ostream& out){
  for( std::map< TypeNode, std::vector< Node > >::iterator it = d_type_reps.begin(); it != d_type_reps.end(); ++it ){
    if( !it->first.isFunction() && !it->first.isPredicate() ){
      out << "(" << it->first << " " << it->second.size();
      out << " (";
      for( unsigned i=0; i<it->second.size(); i++ ){
        if( i>0 ){ out << " "; }
        out << it->second[i];
      }
      out << ")";
      out << ")" << std::endl;
    }
  }
}

}  // namespace theory
}  // namespace cvc5::internal
