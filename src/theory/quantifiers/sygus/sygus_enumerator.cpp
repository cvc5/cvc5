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
  d_enum.initialize(this,e.getType(),
}

void SygusEnumerator::addValue(Node v)
{
  
}

Node SygusEnumerator::getNext()
{
  
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
  d_type = tn;
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
unsigned SygusEnumerator::TermCache::getEnumSize() {
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

SygusEnumerator::TermEnum::TermEnum()
{
  
}

void SygusEnumerator::TermEnum::initialize(SygusEnumerator * se, TypeNode tn, unsigned sizeLim, bool sizeExact)
{
  se->initialize(tn);
  d_se = se;
  SygusEnumerator::TermCache& tc = se->d_tcache[tn];
  if( sizeLim<tc.getEnumSize() )
  {
    d_isMaster = false;
    d_index = 0;
    if( sizeExact )
    {
      d_index = tc.getIndexForSize(sizeLim);
    }
    d_indexEnd = tc.getIndexForSize(sizeLim+1);
    return;
  }
  d_isMaster = true;
  d_consNum = 0;
  
}

Node SygusEnumerator::TermEnum::getCurrent()
{
  if( !d_isMaster )
  {  
    // lookup in the cache
    SygusEnumerator::TermCache& tc = se->d_tcache[tn];
    return tc.getTerm(d_index);
  }
  // construct based on the children
  std::vector< Node > children;
  const Datatype& dt = tn.getDatatype();
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
    // are we at 
    return d_index<d_indexEnd;
  }
  // try incrementing the last child until success
  
  
  return false;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
