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
#include "theory/strings/arith_entail.h"
#include "util/rational.h"

using namespace CVC4::kind;

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
  // FIXME: delay rewriting
  a = a.isNull() ? a : Rewriter::rewrite(a);
  b = b.isNull() ? b : Rewriter::rewrite(b);

  std::tie(id, a, b) = normalizeStringSkolem(id, a, b);

  std::map<SkolemId, Node>::iterator it = d_skolemCache[a][b].find(id);
  if (it == d_skolemCache[a][b].end())
  {
    NodeManager* nm = NodeManager::currentNM();
    // the condition
    Node v = nm->mkBoundVar(tn);
    Node cond = nm->mkConst(true);
    switch (id)
    {
      // exists k. k = a
      case SK_PURIFY: cond = v.eqNode(a); break;
      // a != ""  ^ b != "" ^ len( a ) != len( b ) ^ a ++ a' != b ++ b' =>
      //    exists k_x k_y k_z.
      //         ( len( k_y ) = len( a ) ^ len( k_x ) = len( b ) ^ len( k_z) > 0
      //           ( a = k_x ++ k_z OR b = k_y ++ k_z ) )
      case SK_ID_DEQ_Z: break;
      // these are eliminated by normalizeStringSkolem
      case SK_ID_V_SPT: 
      case SK_ID_V_SPT_REV:
      case SK_ID_VC_SPT:
      case SK_ID_VC_SPT_REV:
      case SK_FIRST_CTN_POST:
      case SK_ID_C_SPT:
      case SK_ID_C_SPT_REV:
      case SK_ID_DC_SPT:
      case SK_ID_DC_SPT_REM:
      case SK_ID_DEQ_X:
      case SK_ID_DEQ_Y:
      case SK_FIRST_CTN_PRE:
      case SK_PREFIX:
      case SK_SUFFIX_REM:
        Unhandled() << "Expected to eliminate Skolem ID " << id << std::endl;
        break;
      // these are not easily formalized as witness terms
      // --------------- integer skolems
      // exists k. ( b occurs k times in a )
      case SK_NUM_OCCUR:
      // --------------- function skolems
      // For function k: Int -> Int
      //   exists k.
      //     forall 0 <= x <= n,
      //       k(x) is the end index of the x^th occurrence of b in a
      //   where n is the number of occurrences of b in a, and k(0)=0.
      case SK_OCCUR_INDEX:
      default:
        Notice() << "Don't know how to handle Skolem ID " << id << std::endl;
        break;
    }
    // use the proper way to make skolems while recording witness terms
    Node sk = d_pskc.mkSkolem(v, cond, c, "string skolem");
    d_allSkolems.insert(sk);
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
  // TODO: eliminate this
  Node n = NodeManager::currentNM()->mkSkolem(c, d_strType, "string skolem");
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

  NodeManager* nm = NodeManager::currentNM();

  if (id == SK_FIRST_CTN_POST)
  {
    // SK_FIRST_CTN_POST(x, y) --->
    //   SK_SUFFIX_REM(x, (+ (str.len SK_FIRST_CTN_PRE(x, y)) (str.len y)))
    id = SK_SUFFIX_REM;
    Node pre = mkSkolemCached(a, b, SK_FIRST_CTN_PRE, "pre");
    b = nm->mkNode(
        PLUS, nm->mkNode(STRING_LENGTH, pre), nm->mkNode(STRING_LENGTH, b));
  }

  if (id==SK_ID_V_SPT || id == SK_ID_C_SPT)
  {
    // SK_ID_*_SPT(x, y) ---> SK_SUFFIX_REM(x, (str.len y))
    id = SK_SUFFIX_REM;
    b = nm->mkNode(STRING_LENGTH, b);
  }
  else if (id==SK_ID_V_SPT_REV || id == SK_ID_C_SPT_REV)
  {
    // SK_ID_*_SPT_REV(x, y) ---> SK_PREFIX(x, (- (str.len x) (str.len y)))
    id = SK_PREFIX;
    b = nm->mkNode(
        MINUS, nm->mkNode(STRING_LENGTH, a), nm->mkNode(STRING_LENGTH, b));
  }
  else if (id == SK_ID_VC_SPT)
  {
    // SK_ID_VC_SPT(x, y) ---> SK_SUFFIX_REM(x, 1)
    id = SK_SUFFIX_REM;
    b = nm->mkConst(Rational(1));
  }
  else if (id == SK_ID_VC_SPT_REV)
  {
    // SK_ID_VC_SPT_REV(x, y) ---> SK_PREFIX(x, (- (str.len x) 1))
    id = SK_PREFIX;
    b = nm->mkNode(
        MINUS, nm->mkNode(STRING_LENGTH, a), nm->mkConst(Rational(1)));
  }
  else if (id == SK_ID_DC_SPT)
  {
    // SK_ID_DC_SPT(x, y) ---> SK_PREFIX(x, 1)
    id = SK_PREFIX;
    b = nm->mkConst(Rational(1));
  }
  else if (id == SK_ID_DC_SPT_REM)
  {
    // SK_ID_DC_SPT_REM(x, y) ---> SK_SUFFIX_REM(x, 1)
    id = SK_SUFFIX_REM;
    b = nm->mkConst(Rational(1));
  }
  else if (id == SK_ID_DEQ_X)
  {
    // SK_ID_DEQ_X(x, y) ---> SK_PREFIX(y, (str.len x))
    id = SK_PREFIX;
    Node aOld = a;
    a = b;
    b = nm->mkNode(STRING_LENGTH, aOld);
  }
  else if (id == SK_ID_DEQ_Y)
  {
    // SK_ID_DEQ_Y(x, y) ---> SK_PREFIX(x, (str.len y))
    id = SK_PREFIX;
    b = nm->mkNode(STRING_LENGTH, b);
  }

  if (id == SK_FIRST_CTN_PRE)
  {
    // SK_FIRST_CTN_PRE(x,y) ---> SK_PREFIX(x, indexof(x,y,0))
    id = SK_PREFIX;
    b = nm->mkNode(STRING_STRIDOF, a, b, d_zero);
  }
  if (id == SK_PREFIX)
  {
    // SK_PREFIX(x,y) ---> SK_PURIFY(substr(x,0,y))
    id = SK_PURIFY;
    a = nm->mkNode(STRING_SUBSTR, a, d_zero, b);
    b = Node::null();
  }
  else if (id == SK_SUFFIX_REM)
  {
    // SK_SUFFIX_REM(x,y) ---> SK_PURIFY(substr(x,y,str.len(x)-y))
    id = SK_PURIFY;
    a = nm->mkNode(STRING_SUBSTR,
                   a,
                   b,
                   nm->mkNode(MINUS, nm->mkNode(STRING_LENGTH, a), b));
    b = Node::null();
  }

  // FIXME: delay rewriting
  a = a.isNull() ? a : Rewriter::rewrite(a);
  b = b.isNull() ? b : Rewriter::rewrite(b);

  Trace("skolem-cache") << "normalizeStringSkolem end: (" << id << ", " << a
                        << ", " << b << ")" << std::endl;
  return std::make_tuple(id, a, b);
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
