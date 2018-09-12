/*********************                                                        */
/*! \file skolem_cache.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A cache of skolems for theory of strings.
 **/

#include "theory/strings/skolem_cache.h"


using namespace CVC4;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

SkolemCache::SkolemCache()
{
  
}

Node SkolemCache::mkSkolemCached( Node a, Node b, SkolemId id, const char * c ){
  std::map< SkolemId, Node >::iterator it = d_skolem_cache[a][b].find( id );
  if( it==d_skolem_cache[a][b].end() ){
    Node sk = mkSkolem( c );
    d_skolem_cache[a][b][id] = sk;
    return sk;
  }
  return it->second;
}

Node SkolemCache::mkSkolem( const char * c )
{
  NodeManager * nm = NodeManager::currentNM();
  Node n = nm->mkSkolem( c, nm->stringType(), "string skolem" );
  d_all_skolems.insert(n);
  return n;
}

bool SkolemCache::isSkolem(Node n) const
{
  return d_all_skolems.find(n)!=d_all_skolems.end();
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
