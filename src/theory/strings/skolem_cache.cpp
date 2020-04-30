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
  a = a.isNull() ? a : Rewriter::rewrite(a);
  b = b.isNull() ? b : Rewriter::rewrite(b);

  if (tn == d_strType)
  {
    std::tie(id, a, b) = normalizeStringSkolem(id, a, b);
  }

  std::map<SkolemId, Node>::iterator it = d_skolemCache[a][b].find(id);
  if (it == d_skolemCache[a][b].end())
  {
    // the condition
    Node v = nm->mkBoundVar(tn);
    Node cond = nm->mkConst(true);
    case (id)
    {
    // exists k. k = a
    case SK_PURIFY:
      break;
    // a != "" ^ b = "ccccd" ^ a ++ "d" ++ a' = b ++ b' =>
    //    exists k. a = "cccc" + k
    case SK_ID_C_SPT_REV:
      break;
    // a != "" ^ b = "c" ^ len(a)!=len(b) ^ a ++ a' = b ++ b' =>
    //    exists k. a = "c" ++ k
    // a != ""  ^ b != "" ^ len( a ) != len( b ) ^ a ++ a' != b ++ b' =>
    //    exists k_x k_y k_z.
    //         ( len( k_y ) = len( a ) ^ len( k_x ) = len( b ) ^ len( k_z) > 0
    //           ( a = k_x ++ k_z OR b = k_y ++ k_z ) )
    case SK_ID_DEQ_Z:
      break;
    // contains( a, b ) =>
    //    exists k_pre, k_post. a = k_pre ++ b ++ k_post ^
    //                          ~contains(k_pre ++ substr( b, 0, len(b)-1 ), b)
    //
    // As an optimization, these skolems are reused for positive occurrences of
    // contains, where they have the semantics:
    //
    //   contains( a, b ) =>
    //      exists k_pre, k_post. a = k_pre ++ b ++ k_post
    //
    // We reuse them since it is sound to consider w.l.o.g. the first occurrence
    // of b in a as the witness for contains( a, b ).
    case SK_FIRST_CTN_PRE:
      break;
    // For integer b,
    // len( a ) > b =>
    //    exists k. a = k ++ a' ^ len( k ) = b
    case SK_PREFIX:
      break;
    // For integer b,
    // b > 0 =>
    //    exists k. a = a' ++ k ^ len( k ) = ite( len(a)>b, len(a)-b, 0 )
    case SK_SUFFIX_REM:
      break;
    // --------------- integer skolems
    // exists k. ( b occurs k times in a )
    case SK_NUM_OCCUR,
      break;
    // --------------- function skolems
    // For function k: Int -> Int
    //   exists k.
    //     forall 0 <= x <= n,
    //       k(x) is the end index of the x^th occurrence of b in a
    //   where n is the number of occurrences of b in a, and k(0)=0.
    case SK_OCCUR_INDEX:
      break;
    
    case SK_ID_VC_SPT:
    case SK_ID_VC_SPT_REV:
    case SK_FIRST_CTN_POST:
    case SK_ID_C_SPT:
    case SK_ID_V_SPT:
    case SK_ID_V_SPT_REV:
    case SK_ID_DC_SPT:
    case SK_ID_DC_SPT_REM:
    case SK_ID_DEQ_X:
    case SK_ID_DEQ_Y:
      Unhandled() << "Expected to eliminate Skolem ID " << id << std::endl;
      break;
    default:
      Notice() << "Don't know how to handle Skolem ID " << id << std::endl;
      break;
    }
    Node sk = d_pskc.mkSkolem(v,cond,c,"string skolem");
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
    b = Rewriter::rewrite(nm->mkNode(
        PLUS, nm->mkNode(STRING_LENGTH, pre), nm->mkNode(STRING_LENGTH, b)));
  }

  if (id == SK_ID_C_SPT)
  {
    // SK_ID_C_SPT(x, y) ---> SK_SUFFIX_REM(x, (str.len y))
    id = SK_SUFFIX_REM;
    b = Rewriter::rewrite(nm->mkNode(STRING_LENGTH, b));
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
    b = Rewriter::rewrite(nm->mkNode(
        MINUS, nm->mkNode(STRING_LENGTH, a), nm->mkConst(Rational(1))));
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
    b = Rewriter::rewrite(nm->mkNode(STRING_LENGTH, aOld));
  }
  else if (id == SK_ID_DEQ_Y)
  {
    // SK_ID_DEQ_Y(x, y) ---> SK_PREFIX(x, (str.len y))
    id = SK_PREFIX;
    b = Rewriter::rewrite(nm->mkNode(STRING_LENGTH, b));
  }

  if (id == SK_PURIFY && a.getKind() == kind::STRING_SUBSTR)
  {
    Node s = a[0];
    Node n = a[1];
    Node m = a[2];

    if (n == d_zero)
    {
      // SK_PURIFY((str.substr x 0 m)) ---> SK_PREFIX(x, m)
      id = SK_PREFIX;
      a = s;
      b = m;
    }
    else if (ArithEntail::check(nm->mkNode(PLUS, n, m),
                                nm->mkNode(STRING_LENGTH, s)))
    {
      // SK_PURIFY((str.substr x n m)) ---> SK_SUFFIX_REM(x, n)
      // if n + m >= (str.len x)
      id = SK_SUFFIX_REM;
      a = s;
      b = n;
    }
  }

  if (id == SK_PREFIX && b.getKind() == kind::STRING_STRIDOF && a == b[0]
      && b[2] == d_zero)
  {
    // SK_PREFIX(x, (str.indexof x y 0)) ---> SK_FIRST_CTN_PRE(x, y)
    id = SK_FIRST_CTN_PRE;
    b = b[1];
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
