/*********************                                                        */
/*! \file skolem_cache.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of a cache of skolems for theory of strings.
 **/

#include "theory/strings/skolem_cache.h"

#include "theory/rewriter.h"
#include "theory/strings/theory_strings_rewriter.h"
#include "util/rational.h"

namespace CVC4 {
namespace theory {
namespace strings {

SkolemCache::SkolemCache()
{
  NodeManager* nm = NodeManager::currentNM();
  d_strType = nm->stringType();
  d_zero = nm->mkConst(Rational(0));
}

Node SkolemCache::mkSkolemCached(Node a, Node b, SkolemId id, const char* c)
{
  return mkTypedSkolemCached(d_strType, a, b, id, c);
}

Node SkolemCache::mkSkolemCached(Node a, SkolemId id, const char* c)
{
  return mkSkolemCached(a, Node::null(), id, c);
}

Node SkolemCache::mkTypedSkolemCached(
    TypeNode tn, Node a, Node b, SkolemId id, const char* c)
{
  a = a.isNull() ? a : Rewriter::rewrite(a);
  b = b.isNull() ? b : Rewriter::rewrite(b);

  if (tn == d_strType)
  {
    std::tie(id, a, b) = normalizeStringSkolem(id, a, b);
  }

  std::map<SkolemId, Node>::iterator it = d_skolemCache[a][b].find(id);
  if (it == d_skolemCache[a][b].end())
  {
    Node sk = mkTypedSkolem(tn, c);
    d_skolemCache[a][b][id] = sk;
    return sk;
  }
  return it->second;
}
Node SkolemCache::mkTypedSkolemCached(TypeNode tn,
                                      Node a,
                                      SkolemId id,
                                      const char* c)
{
  return mkTypedSkolemCached(tn, a, Node::null(), id, c);
}

Node SkolemCache::mkSkolem(const char* c)
{
  return mkTypedSkolem(d_strType, c);
}

Node SkolemCache::mkTypedSkolem(TypeNode tn, const char* c)
{
  Node n = NodeManager::currentNM()->mkSkolem(c, tn, "string skolem");
  d_allSkolems.insert(n);
  return n;
}

bool SkolemCache::isSkolem(Node n) const
{
  return d_allSkolems.find(n) != d_allSkolems.end();
}

std::tuple<SkolemCache::SkolemId, Node, Node>
SkolemCache::normalizeStringSkolem(SkolemId id, Node a, Node b)
{
  Trace("skolem-cache") << "normalizeStringSkolem start: (" << id << ", " << a
                        << ", " << b << ")" << std::endl;

  // SK_PURIFY(str.substr x 0 (str.indexof x y 0)) ---> SK_FIRST_CTN_PRE(x, y)
  if (id == SK_PURIFY && a.getKind() == kind::STRING_SUBSTR)
  {
    Node s = a[0];
    Node n = a[1];
    Node m = a[2];
    if (m.getKind() == kind::STRING_STRIDOF && m[0] == s)
    {
      if (n == d_zero && m[2] == d_zero)
      {
        id = SK_FIRST_CTN_PRE;
        a = m[0];
        b = m[1];
      }
    }
  }

  if (id == SK_FIRST_CTN_PRE)
  {
    // SK_FIRST_CTN_PRE((str.substr x 0 n), y) ---> SK_FIRST_CTN_PRE(x, y)
    while (a.getKind() == kind::STRING_SUBSTR && a[1] == d_zero)
    {
      a = a[0];
    }
  }

  Trace("skolem-cache") << "normalizeStringSkolem end: (" << id << ", " << a
                        << ", " << b << ")" << std::endl;
  return std::make_tuple(id, a, b);
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
