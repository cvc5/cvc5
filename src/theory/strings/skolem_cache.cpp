/*********************                                                        */
/*! \file skolem_cache.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of a cache of skolems for theory of strings.
 **/

#include "theory/strings/skolem_cache.h"

#include "expr/attribute.h"
#include "theory/rewriter.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "util/rational.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

/**
 * A bound variable corresponding to the universally quantified integer
 * variable used to range over the valid positions in a string, used
 * for axiomatizing the behavior of some term.
 */
struct IndexVarAttributeId
{
};
typedef expr::Attribute<IndexVarAttributeId, Node> IndexVarAttribute;

SkolemCache::SkolemCache(bool useOpts) : d_useOpts(useOpts)
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
  Trace("skolem-cache") << "mkTypedSkolemCached start: (" << id << ", " << a
                        << ", " << b << ")" << std::endl;
  SkolemId idOrig = id;
  a = a.isNull() ? a : Rewriter::rewrite(a);
  b = b.isNull() ? b : Rewriter::rewrite(b);

  std::tie(id, a, b) = normalizeStringSkolem(id, a, b);

  // optimization: if we aren't asking for the purification skolem for constant
  // a, and the skolem is equivalent to a, then we just return a.
  if (d_useOpts && idOrig != SK_PURIFY && id == SK_PURIFY && a.isConst())
  {
    Trace("skolem-cache") << "...optimization: return constant " << a
                          << std::endl;
    return a;
  }

  std::map<SkolemId, Node>::iterator it = d_skolemCache[a][b].find(id);
  if (it != d_skolemCache[a][b].end())
  {
    // already cached
    return it->second;
  }

  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Node sk;
  switch (id)
  {
    // exists k. k = a
    case SK_PURIFY:
      sk = sm->mkPurifySkolem(a, c, "string purify skolem");
      break;
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
    case SK_NUM_OCCUR:
    case SK_OCCUR_INDEX:
    default:
    {
      Notice() << "Don't know how to handle Skolem ID " << id << std::endl;
      Node v = nm->mkBoundVar(tn);
      Node cond = nm->mkConst(true);
      sk = sm->mkSkolem(v, cond, c, "string skolem");
    }
    break;
  }
  d_allSkolems.insert(sk);
  d_skolemCache[a][b][id] = sk;
  return sk;
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

  NodeManager* nm = NodeManager::currentNM();

  // eliminate in terms of prefix/suffix_rem
  if (id == SK_FIRST_CTN_POST)
  {
    // SK_FIRST_CTN_POST(x, y) --->
    //   SK_SUFFIX_REM(x, (+ (str.len SK_FIRST_CTN_PRE(x, y)) (str.len y)))
    id = SK_SUFFIX_REM;
    Node pre = mkSkolemCached(a, b, SK_FIRST_CTN_PRE, "pre");
    b = nm->mkNode(
        PLUS, nm->mkNode(STRING_LENGTH, pre), nm->mkNode(STRING_LENGTH, b));
  }
  else if (id == SK_ID_V_SPT || id == SK_ID_C_SPT)
  {
    // SK_ID_*_SPT(x, y) ---> SK_SUFFIX_REM(x, (str.len y))
    id = SK_SUFFIX_REM;
    b = nm->mkNode(STRING_LENGTH, b);
  }
  else if (id == SK_ID_V_SPT_REV || id == SK_ID_C_SPT_REV)
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
  else if (id == SK_FIRST_CTN_PRE)
  {
    // SK_FIRST_CTN_PRE(x,y) ---> SK_PREFIX(x, indexof(x,y,0))
    id = SK_PREFIX;
    b = nm->mkNode(STRING_STRIDOF, a, b, d_zero);
  }

  if (id == SK_ID_V_UNIFIED_SPT || id == SK_ID_V_UNIFIED_SPT_REV)
  {
    bool isRev = (id == SK_ID_V_UNIFIED_SPT_REV);
    Node la = nm->mkNode(STRING_LENGTH, a);
    Node lb = nm->mkNode(STRING_LENGTH, b);
    Node ta = isRev ? utils::mkPrefix(a, nm->mkNode(MINUS, la, lb))
                    : utils::mkSuffix(a, lb);
    Node tb = isRev ? utils::mkPrefix(b, nm->mkNode(MINUS, lb, la))
                    : utils::mkSuffix(b, la);
    id = SK_PURIFY;
    // SK_ID_V_UNIFIED_SPT(x,y) --->
    //   ite(len(x) >= len(y), substr(x,0,str.len(y)), substr(y,0,str.len(x))
    a = nm->mkNode(ITE, nm->mkNode(GEQ, la, lb), ta, tb);
    b = Node::null();
  }

  // now, eliminate prefix/suffix_rem in terms of purify
  if (id == SK_PREFIX)
  {
    // SK_PREFIX(x,y) ---> SK_PURIFY(substr(x,0,y))
    id = SK_PURIFY;
    a = utils::mkPrefix(a, b);
    b = Node::null();
  }
  else if (id == SK_SUFFIX_REM)
  {
    // SK_SUFFIX_REM(x,y) ---> SK_PURIFY(substr(x,y,str.len(x)-y))
    id = SK_PURIFY;
    a = utils::mkSuffix(a, b);
    b = Node::null();
  }

  a = a.isNull() ? a : Rewriter::rewrite(a);
  b = b.isNull() ? b : Rewriter::rewrite(b);

  Trace("skolem-cache") << "normalizeStringSkolem end: (" << id << ", " << a
                        << ", " << b << ")" << std::endl;
  return std::make_tuple(id, a, b);
}

Node SkolemCache::mkIndexVar(Node t)
{
  IndexVarAttribute iva;
  if (t.hasAttribute(iva))
  {
    return t.getAttribute(iva);
  }
  NodeManager* nm = NodeManager::currentNM();
  Node v = nm->mkBoundVar(nm->integerType());
  t.setAttribute(iva, v);
  return v;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
