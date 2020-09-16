/*********************                                                        */
/*! \file rep_set.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of representative set
 **/

#include <unordered_set>

#include "theory/rep_set.h"
#include "theory/type_enumerator.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
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

unsigned RepSet::getNumRepresentatives(TypeNode tn) const
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

bool containsStoreAll(Node n, std::unordered_set<Node, NodeHashFunction>& cache)
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
    std::unordered_set<Node, NodeHashFunction> cache;
    if( containsStoreAll( n, cache ) ){
      return;
    }
  }
  Trace("rsi-debug") << "Add rep #" << d_type_reps[tn].size() << " for " << tn << " : " << n << std::endl;
  Assert(n.getType().isSubtypeOf(tn));
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

RepSetIterator::RepSetIterator(const RepSet* rs, RepBoundExt* rext)
    : d_rs(rs), d_rext(rext), d_incomplete(false)
{
}

unsigned RepSetIterator::domainSize(unsigned i)
{
  unsigned v = d_var_order[i];
  return d_domain_elements[v].size();
}

TypeNode RepSetIterator::getTypeOf(unsigned i) const { return d_types[i]; }

bool RepSetIterator::setQuantifier(Node q)
{
  Trace("rsi") << "Make rsi for quantified formula " << q << std::endl;
  Assert(d_types.empty());
  //store indicies
  for (size_t i = 0; i < q[0].getNumChildren(); i++)
  {
    d_types.push_back(q[0][i].getType());
  }
  d_owner = q;
  return initialize();
}

bool RepSetIterator::setFunctionDomain(Node op)
{
  Trace("rsi") << "Make rsi for function " << op << std::endl;
  Assert(d_types.empty());
  TypeNode tn = op.getType();
  for( size_t i=0; i<tn.getNumChildren()-1; i++ ){
    d_types.push_back( tn[i] );
  }
  d_owner = op;
  return initialize();
}

bool RepSetIterator::initialize()
{
  Trace("rsi") << "Initialize rep set iterator..." << std::endl;
  for( unsigned v=0; v<d_types.size(); v++ ){
    d_index.push_back( 0 );
    //store default index order
    d_index_order.push_back( v );
    d_var_order[v] = v;
    //store default domain
    //d_domain.push_back( RepDomain() );
    d_domain_elements.push_back( std::vector< Node >() );
    TypeNode tn = d_types[v];
    Trace("rsi") << "Var #" << v << " is type " << tn << "..." << std::endl;
    bool inc = true;
    bool setEnum = false;
    //check if it is externally bound
    if (d_rext)
    {
      inc = !d_rext->initializeRepresentativesForType(tn);
      RsiEnumType rsiet = d_rext->setBound(d_owner, v, d_domain_elements[v]);
      if (rsiet != ENUM_INVALID)
      {
        d_enum_type.push_back(rsiet);
        inc = false;
        setEnum = true;
      }
    }
    if (inc)
    {
      Trace("fmf-incomplete") << "Incomplete because of quantification of type "
                              << tn << std::endl;
      d_incomplete = true;
    }

    //if we have yet to determine the type of enumeration
    if (!setEnum)
    {
      if (d_rs->hasType(tn))
      {
        d_enum_type.push_back( ENUM_DEFAULT );
        if (const auto* type_reps = d_rs->getTypeRepsOrNull(tn))
        {
          std::vector<Node>& v_domain_elements = d_domain_elements[v];
          v_domain_elements.insert(v_domain_elements.end(),
                                   type_reps->begin(), type_reps->end());
        }
      }else{
        Assert(d_incomplete);
        return false;
      }
    }
  }

  if (d_rext)
  {
    std::vector<unsigned> varOrder;
    if (d_rext->getVariableOrder(d_owner, varOrder))
    {
      if (Trace.isOn("bound-int-rsi"))
      {
        Trace("bound-int-rsi") << "Variable order : ";
        for (unsigned i = 0; i < varOrder.size(); i++)
        {
          Trace("bound-int-rsi") << varOrder[i] << " ";
        }
        Trace("bound-int-rsi") << std::endl;
      }
      std::vector<unsigned> indexOrder;
      indexOrder.resize(varOrder.size());
      for (unsigned i = 0; i < varOrder.size(); i++)
      {
        Assert(varOrder[i] < indexOrder.size());
        indexOrder[varOrder[i]] = i;
      }
      if (Trace.isOn("bound-int-rsi"))
      {
        Trace("bound-int-rsi") << "Will use index order : ";
        for (unsigned i = 0; i < indexOrder.size(); i++)
        {
          Trace("bound-int-rsi") << indexOrder[i] << " ";
        }
        Trace("bound-int-rsi") << std::endl;
      }
      setIndexOrder(indexOrder);
    }
  }
  //now reset the indices
  do_reset_increment( -1, true );
  return true;
}

void RepSetIterator::setIndexOrder(std::vector<unsigned>& indexOrder)
{
  d_index_order.clear();
  d_index_order.insert( d_index_order.begin(), indexOrder.begin(), indexOrder.end() );
  //make the d_var_order mapping
  for( unsigned i=0; i<d_index_order.size(); i++ ){
    d_var_order[d_index_order[i]] = i;
  }
}

int RepSetIterator::resetIndex(unsigned i, bool initial)
{
  d_index[i] = 0;
  unsigned v = d_var_order[i];
  Trace("bound-int-rsi") << "Reset " << i << ", var order = " << v << ", initial = " << initial << std::endl;
  if (d_rext)
  {
    if (!d_rext->resetIndex(this, d_owner, v, initial, d_domain_elements[v]))
    {
      return -1;
    }
  }
  return d_domain_elements[v].empty() ? 0 : 1;
}

int RepSetIterator::incrementAtIndex(int i)
{
  Assert(!isFinished());
#ifdef DISABLE_EVAL_SKIP_MULTIPLE
  i = (int)d_index.size()-1;
#endif
  Trace("rsi-debug") << "RepSetIterator::incrementAtIndex: " << i << std::endl;
  //increment d_index
  if( i>=0){
    Trace("rsi-debug") << "domain size of " << i << " is " << domainSize(i) << std::endl;
  }
  while( i>=0 && d_index[i]>=(int)(domainSize(i)-1) ){
    i--;
    if( i>=0){
      Trace("rsi-debug") << "domain size of " << i << " is " << domainSize(i) << std::endl;
    }
  }
  if( i==-1 ){
    Trace("rsi-debug") << "increment failed" << std::endl;
    d_index.clear();
    return -1;
  }else{
    Trace("rsi-debug") << "increment " << i << std::endl;
    d_index[i]++;
    return do_reset_increment( i );
  }
}

int RepSetIterator::do_reset_increment( int i, bool initial ) {
  Trace("rsi-debug") << "RepSetIterator::do_reset_increment: " << i
                     << ", initial=" << initial << std::endl;
  for( unsigned ii=(i+1); ii<d_index.size(); ii++ ){
    bool emptyDomain = false;
    int ri_res = resetIndex( ii, initial );
    if( ri_res==-1 ){
      //failed
      d_index.clear();
      d_incomplete = true;
      break;
    }else if( ri_res==0 ){
      emptyDomain = true;
    }
    //force next iteration if currently an empty domain
    if (emptyDomain)
    {
      Trace("rsi-debug") << "This is an empty domain (index " << ii << ")."
                         << std::endl;
      if (ii > 0)
      {
        // increment at the previous index
        return incrementAtIndex(ii - 1);
      }
      else
      {
        // this is the first index, we are done
        d_index.clear();
        return -1;
      }
    }
  }
  Trace("rsi-debug") << "Finished, return " << i << std::endl;
  return i;
}

int RepSetIterator::increment(){
  if( !isFinished() ){
    return incrementAtIndex(d_index.size() - 1);
  }else{
    return -1;
  }
}

bool RepSetIterator::isFinished() const { return d_index.empty(); }

Node RepSetIterator::getCurrentTerm(unsigned i, bool valTerm) const
{
  unsigned ii = d_index_order[i];
  unsigned curr = d_index[ii];
  Trace("rsi-debug") << "rsi : get term " << i
                     << ", index order = " << d_index_order[i] << std::endl;
  Trace("rsi-debug") << "rsi : curr = " << curr << " / "
                     << d_domain_elements[i].size() << std::endl;
  Assert(0 <= curr && curr < d_domain_elements[i].size());
  Node t = d_domain_elements[i][curr];
  if (valTerm)
  {
    Node tt = d_rs->getTermForRepresentative(t);
    if (!tt.isNull())
    {
      return tt;
    }
  }
  return t;
}

void RepSetIterator::getCurrentTerms(std::vector<Node>& terms) const
{
  for (unsigned i = 0, size = d_index_order.size(); i < size; i++)
  {
    terms.push_back(getCurrentTerm(i));
  }
}

void RepSetIterator::debugPrint( const char* c ){
  for( unsigned v=0; v<d_index.size(); v++ ){
    Debug( c ) << v << " : " << getCurrentTerm( v ) << std::endl;
  }
}

void RepSetIterator::debugPrintSmall( const char* c ){
  Debug( c ) << "RI: ";
  for( unsigned v=0; v<d_index.size(); v++ ){
    Debug( c ) << v << ": " << getCurrentTerm( v ) << " ";
  }
  Debug( c ) << std::endl;
}

} /* CVC4::theory namespace */
} /* CVC4 namespace */
