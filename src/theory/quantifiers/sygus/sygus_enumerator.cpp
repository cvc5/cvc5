/*********************                                                        */
/*! \file sygus_enumerator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_enumerator
 **/

#include "theory/quantifiers/sygus/sygus_enumerator.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {
  
SygusEnumerator::SygusEnumerator( TermDbSygus* tds ) : d_tds(tds) {

}

void SygusEnumerator::initialize(Node e)
{
  d_enum.initialize(this,e.getType(),false, 0,false);
}

void SygusEnumerator::addValue(Node v)
{
  // do nothing
}

Node SygusEnumerator::getNext()
{
  if( d_enum.increment() )
  {
    return d_enum.getCurrent();
  }
  return Node::null();
}
  
void SygusEnumerator::initializeTermCache( TypeNode tn )
{
  std::map< TypeNode, TermCache >::iterator itt = d_tcache.find(tn);
  if( itt==d_tcache.end() )
  {
    d_tcache[tn].initialize(tn,d_tds);
  }
}

SygusEnumerator::TermCache::TermCache() : d_tds(nullptr),
d_sizeEnum(0)
{
  
}
void SygusEnumerator::TermCache::initialize(TypeNode tn, TermDbSygus * tds)
{
  d_tn = tn;
  d_tds = tds;
}
bool SygusEnumerator::TermCache::addTerm(Node n)
{
  Node bn = d_tds->sygusToBuiltin(n);
  bn = d_tds->getExtRewriter()->extendedRewrite(bn);
  // must be unique up to rewriting
  if( d_bterms.find(bn)==d_bterms.end() )
  {
    d_terms.push_back(n);
    d_bterms.insert(bn);
    return true;
  }
  return false;
}
void SygusEnumerator::TermCache::pushEnumSize() 
{
  d_lastSizeIndex[d_sizeEnum] = d_terms.size();
  d_sizeEnum++;
}
unsigned SygusEnumerator::TermCache::getEnumSize() const {
  return d_sizeEnum; 
}
unsigned SygusEnumerator::TermCache::getIndexForSize( unsigned s ) const 
{ 
  if( s==0 )
  {
    return 0;
  }
  std::map< unsigned, unsigned >::const_iterator it = d_lastSizeIndex.find(s-1);
  Assert( it != d_lastSizeIndex.end() );
  return it->second;
}

Node  SygusEnumerator::TermCache::getTerm( unsigned index ) const
{
  Assert( index<d_terms.size() );
  return d_terms[index];
}

SygusEnumerator::TermEnum::TermEnum()
{
  
}

void SygusEnumerator::TermEnum::initialize(SygusEnumerator * se, TypeNode tn, bool hasSizeLim, unsigned sizeLim, bool sizeExact)
{
  d_se = se;
  d_tn = tn;
  d_se->initializeTermCache(d_tn);
  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
  d_hasSizeBound = hasSizeLim;
  d_sizeLim = sizeLim;
  if( d_hasSizeBound && d_sizeLim<tc.getEnumSize() )
  {
    d_isMaster = false;
    // if the size is exact, we start at the limit
    d_currSize = sizeExact ? sizeLim : 0;
    d_index = tc.getIndexForSize(d_currSize);
    d_indexNextEnd = tc.getIndexForSize(d_currSize+1);
    return;
  }
  d_isMaster = true;
  d_consNum = 0;
  // populate the children TODO
}

Node SygusEnumerator::TermEnum::getCurrent()
{
  if( !d_isMaster )
  {  
    // lookup in the cache
    SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
    return tc.getTerm(d_index);
  }
  // construct based on the children
  std::vector< Node > children;
  const Datatype& dt = d_tn.getDatatype();
  children.push_back( Node::fromExpr( dt[d_consNum].getConstructor() ) );
  for( std::pair< const unsigned, TermEnum >& c : d_children )
  {
    children.push_back(c.second.getCurrent());
  }
  return NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, children );
}

unsigned SygusEnumerator::TermEnum::getCurrentSize()
{
  return d_currSize;
}

bool SygusEnumerator::TermEnum::increment()
{
  if( !d_isMaster )
  {
    // increment index
    d_index++;
    // if we are at the beginning of the next size, increment current size
    if( d_index==d_indexNextEnd )
    {
      d_currSize++;
      Assert( d_hasSizeBound );
      // if we've hit the size limit, return false
      if( d_currSize==d_sizeLim )
      {
        return false;
      }
      // update the next end index
      SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
      d_indexNextEnd = tc.getIndexForSize(d_currSize+1);
    }
    return true;
  }
  // try incrementing the last child until success
  
  
  return false;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
