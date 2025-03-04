/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Util functions for theory strings.
 */

#include "theory/strings/theory_strings_utils.h"

#include <sstream>

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/sequence.h"
#include "expr/skolem_manager.h"
#include "options/strings_options.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/rewriter.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/strings_entail.h"
#include "theory/strings/word.h"
#include "util/rational.h"
#include "util/regexp.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {
namespace utils {

uint32_t getDefaultAlphabetCardinality()
{
  // 3*16^4 = 196608 values in the SMT-LIB standard for Unicode strings
  Assert(196608 <= String::num_codes());
  return 196608;
}

Node mkAnd(NodeManager* nm, const std::vector<Node>& a)
{
  std::vector<Node> au;
  for (const Node& ai : a)
  {
    if (std::find(au.begin(), au.end(), ai) == au.end())
    {
      au.push_back(ai);
    }
  }
  if (au.empty())
  {
    return nm->mkConst(true);
  }
  else if (au.size() == 1)
  {
    return au[0];
  }
  return nm->mkNode(Kind::AND, au);
}

void flattenOp(Kind k, Node n, std::vector<Node>& conj)
{
  if (n.getKind() != k)
  {
    // easy case, just add to conj if non-duplicate
    if (std::find(conj.begin(), conj.end(), n) == conj.end())
    {
      conj.push_back(n);
    }
    return;
  }
  // otherwise, traverse
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited.insert(cur);
      if (cur.getKind() == k)
      {
        // Add in reverse order, so that we traverse left to right.
        // This is important so that explantaions aren't reversed when they
        // are flattened, which is important for proofs involving substitutions.
        std::vector<Node> newChildren;
        newChildren.insert(newChildren.end(), cur.begin(), cur.end());
        visit.insert(visit.end(), newChildren.rbegin(), newChildren.rend());
      }
      else if (std::find(conj.begin(), conj.end(), cur) == conj.end())
      {
        conj.push_back(cur);
      }
    }
  } while (!visit.empty());
}

void getConcat(Node n, std::vector<Node>& c)
{
  Kind k = n.getKind();
  if (k == Kind::STRING_CONCAT || k == Kind::REGEXP_CONCAT)
  {
    for (const Node& nc : n)
    {
      c.push_back(nc);
    }
  }
  else
  {
    c.push_back(n);
  }
}

Node mkConcat(const std::vector<Node>& c, TypeNode tn)
{
  Assert(tn.isStringLike() || tn.isRegExp());
  if (c.size() == 1)
  {
    return c[0];
  }
  NodeManager* nm = NodeManager::currentNM();
  if (c.empty())
  {
    if (tn.isRegExp())
    {
      TypeNode stn = nm->stringType();
      Node emp = Word::mkEmptyWord(stn);
      return nm->mkNode(Kind::STRING_TO_REGEXP, emp);
    }
    return Word::mkEmptyWord(tn);
  }
  Kind k = tn.isStringLike() ? Kind::STRING_CONCAT : Kind::REGEXP_CONCAT;
  return nm->mkNode(k, c);
}

Node mkPrefix(Node t, Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(Kind::STRING_SUBSTR, t, nm->mkConstInt(Rational(0)), n);
}

Node mkSuffix(Node t, Node n)
{
  return NodeManager::mkNode(
      Kind::STRING_SUBSTR,
      t,
      n,
      NodeManager::mkNode(
          Kind::SUB, NodeManager::mkNode(Kind::STRING_LENGTH, t), n));
}

Node mkPrefixExceptLen(Node t, Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Node lent = nm->mkNode(Kind::STRING_LENGTH, t);
  return nm->mkNode(Kind::STRING_SUBSTR,
                    t,
                    nm->mkConstInt(Rational(0)),
                    nm->mkNode(Kind::SUB, lent, n));
}

Node mkSuffixOfLen(Node t, Node n)
{
  Node lent = NodeManager::mkNode(Kind::STRING_LENGTH, t);
  return NodeManager::mkNode(
      Kind::STRING_SUBSTR, t, NodeManager::mkNode(Kind::SUB, lent, n), n);
}

Node mkUnit(TypeNode tn, Node n)
{
  if (tn.isString())
  {
    return NodeManager::mkNode(Kind::STRING_UNIT, n);
  }
  Assert(tn.isSequence());
  return NodeManager::mkNode(Kind::SEQ_UNIT, n);
}

Node getConstantComponent(Node t)
{
  if (t.getKind() == Kind::STRING_TO_REGEXP)
  {
    return t[0].isConst() ? t[0] : Node::null();
  }
  return t.isConst() ? t : Node::null();
}

Node getConstantEndpoint(Node e, bool isSuf)
{
  Kind ek = e.getKind();
  if (ek == Kind::STRING_IN_REGEXP)
  {
    e = e[1];
    ek = e.getKind();
  }
  if (ek == Kind::STRING_CONCAT || ek == Kind::REGEXP_CONCAT)
  {
    return getConstantComponent(e[isSuf ? e.getNumChildren() - 1 : 0]);
  }
  return getConstantComponent(e);
}

Node decomposeSubstrChain(Node s, std::vector<Node>& ss, std::vector<Node>& ls)
{
  Assert(ss.empty());
  Assert(ls.empty());
  while (s.getKind() == Kind::STRING_SUBSTR)
  {
    ss.push_back(s[1]);
    ls.push_back(s[2]);
    s = s[0];
  }
  std::reverse(ss.begin(), ss.end());
  std::reverse(ls.begin(), ls.end());
  return s;
}

Node mkSubstrChain(Node base,
                   const std::vector<Node>& ss,
                   const std::vector<Node>& ls)
{
  for (unsigned i = 0, size = ss.size(); i < size; i++)
  {
    base = NodeManager::mkNode(Kind::STRING_SUBSTR, base, ss[i], ls[i]);
  }
  return base;
}

Node mkConcatForConstSequence(const Node& c)
{
  Assert(c.getKind() == Kind::CONST_SEQUENCE);
  const std::vector<Node>& charVec = c.getConst<Sequence>().getVec();
  std::vector<Node> vec;
  for (const Node& cc : charVec)
  {
    vec.push_back(NodeManager::mkNode(Kind::SEQ_UNIT, cc));
  }
  return mkConcat(vec, c.getType());
}

std::pair<bool, std::vector<Node> > collectEmptyEqs(Node x)
{
  // Collect the equalities of the form (= x "") (sorted)
  std::set<TNode> emptyNodes;
  bool allEmptyEqs = true;
  if (x.getKind() == Kind::EQUAL)
  {
    if (Word::isEmpty(x[0]))
    {
      emptyNodes.insert(x[1]);
    }
    else if (Word::isEmpty(x[1]))
    {
      emptyNodes.insert(x[0]);
    }
    else
    {
      allEmptyEqs = false;
    }
  }
  else if (x.getKind() == Kind::AND)
  {
    for (const Node& c : x)
    {
      if (c.getKind() != Kind::EQUAL)
      {
        allEmptyEqs = false;
        continue;
      }

      if (Word::isEmpty(c[0]))
      {
        emptyNodes.insert(c[1]);
      }
      else if (Word::isEmpty(c[1]))
      {
        emptyNodes.insert(c[0]);
      }
      else
      {
        allEmptyEqs = false;
      }
    }
  }

  if (emptyNodes.size() == 0)
  {
    allEmptyEqs = false;
  }

  return std::make_pair(
      allEmptyEqs, std::vector<Node>(emptyNodes.begin(), emptyNodes.end()));
}

bool isConstantLike(Node n)
{
  return n.isConst() || n.getKind() == Kind::SEQ_UNIT
         || n.getKind() == Kind::STRING_UNIT;
}

bool isCharacterRange(TNode t)
{
  Assert(t.getKind() == Kind::REGEXP_RANGE);
  for (size_t i = 0; i < 2; i++)
  {
    if (!t[i].isConst() || t[i].getConst<String>().size() != 1)
    {
      return false;
    }
  }
  return true;
}

bool isUnboundedWildcard(const std::vector<Node>& rs, size_t start)
{
  size_t i = start;
  while (i < rs.size() && rs[i].getKind() == Kind::REGEXP_ALLCHAR)
  {
    i++;
  }

  if (i >= rs.size())
  {
    return false;
  }

  return rs[i].getKind() == Kind::REGEXP_STAR
         && rs[i][0].getKind() == Kind::REGEXP_ALLCHAR;
}

bool isSimpleRegExp(Node r)
{
  Assert(r.getType().isRegExp());

  std::vector<Node> v;
  utils::getConcat(r, v);
  for (const Node& n : v)
  {
    if (n.getKind() == Kind::STRING_TO_REGEXP)
    {
      if (!n[0].isConst())
      {
        return false;
      }
    }
    else if (n.getKind() != Kind::REGEXP_ALLCHAR
             && (n.getKind() != Kind::REGEXP_STAR
                 || n[0].getKind() != Kind::REGEXP_ALLCHAR))
    {
      return false;
    }
  }
  return true;
}

void getRegexpComponents(Node r, std::vector<Node>& result)
{
  Assert(r.getType().isRegExp());

  if (r.getKind() == Kind::REGEXP_CONCAT)
  {
    for (const Node& n : r)
    {
      getRegexpComponents(n, result);
    }
  }
  else if (r.getKind() == Kind::STRING_TO_REGEXP && r[0].isConst())
  {
    size_t rlen = Word::getLength(r[0]);
    for (size_t i = 0; i < rlen; i++)
    {
      result.push_back(NodeManager::mkNode(Kind::STRING_TO_REGEXP,
                                           Word::substr(r[0], i, 1)));
    }
  }
  else
  {
    result.push_back(r);
  }
}

void printConcat(std::ostream& out, std::vector<Node>& n)
{
  for (unsigned i = 0, nsize = n.size(); i < nsize; i++)
  {
    if (i > 0)
    {
      out << " ++ ";
    }
    out << n[i];
  }
}

void printConcatTrace(std::vector<Node>& n, const char* c)
{
  std::stringstream ss;
  printConcat(ss, n);
  Trace(c) << ss.str();
}

bool isStringKind(Kind k)
{
  return k == Kind::STRING_STOI || k == Kind::STRING_ITOS
         || k == Kind::STRING_TO_LOWER || k == Kind::STRING_TO_UPPER
         || k == Kind::STRING_LEQ || k == Kind::STRING_LT
         || k == Kind::STRING_FROM_CODE || k == Kind::STRING_TO_CODE;
}

bool isRegExpKind(Kind k)
{
  return k == Kind::REGEXP_NONE || k == Kind::REGEXP_ALL
         || k == Kind::REGEXP_ALLCHAR || k == Kind::STRING_TO_REGEXP
         || k == Kind::REGEXP_CONCAT || k == Kind::REGEXP_UNION
         || k == Kind::REGEXP_INTER || k == Kind::REGEXP_STAR
         || k == Kind::REGEXP_PLUS || k == Kind::REGEXP_OPT
         || k == Kind::REGEXP_RANGE || k == Kind::REGEXP_LOOP
         || k == Kind::REGEXP_RV || k == Kind::REGEXP_COMPLEMENT;
}

TypeNode getOwnerStringType(Node n)
{
  TypeNode tn;
  Kind k = n.getKind();
  if (k == Kind::STRING_INDEXOF || k == Kind::STRING_INDEXOF_RE
      || k == Kind::STRING_LENGTH || k == Kind::STRING_CONTAINS
      || k == Kind::SEQ_NTH || k == Kind::STRING_PREFIX
      || k == Kind::STRING_SUFFIX)
  {
    // owning string type is the type of first argument
    tn = n[0].getType();
  }
  else if (isStringKind(k))
  {
    tn = NodeManager::currentNM()->stringType();
  }
  else
  {
    tn = n.getType();
  }
  // otherwise return null
  return tn;
}

unsigned getRepeatAmount(TNode node)
{
  Assert(node.getKind() == Kind::REGEXP_REPEAT);
  return node.getOperator().getConst<RegExpRepeat>().d_repeatAmount;
}

unsigned getLoopMaxOccurrences(TNode node)
{
  Assert(node.getKind() == Kind::REGEXP_LOOP);
  return node.getOperator().getConst<RegExpLoop>().d_loopMaxOcc;
}

unsigned getLoopMinOccurrences(TNode node)
{
  Assert(node.getKind() == Kind::REGEXP_LOOP);
  return node.getOperator().getConst<RegExpLoop>().d_loopMinOcc;
}

Node mkForallInternal(NodeManager* nm, Node bvl, Node body)
{
  return quantifiers::BoundedIntegers::mkBoundedForall(nm, bvl, body);
}

/**
 * Mapping to the variable used for binding the witness term for the abstract
 * value below.
 */
struct StringValueForLengthVarAttributeId
{
};
typedef expr::Attribute<StringValueForLengthVarAttributeId, Node>
    StringValueForLengthVarAttribute;

Node mkAbstractStringValueForLength(Node n, Node len, size_t id)
{
  NodeManager* nm = NodeManager::currentNM();
  BoundVarManager* bvm = nm->getBoundVarManager();
  Node cacheVal = BoundVarManager::getCacheValue(n, len);
  Node v = bvm->mkBoundVar<StringValueForLengthVarAttribute>(
      cacheVal, "s", n.getType());
  Node pred = nm->mkNode(Kind::STRING_LENGTH, v).eqNode(len);
  // return (witness ((v String)) (= (str.len v) len))
  Node bvl = nm->mkNode(Kind::BOUND_VAR_LIST, v);
  std::stringstream ss;
  ss << "w" << id;
  return quantifiers::mkNamedQuant(Kind::WITNESS, bvl, pred, ss.str());
}

Node mkCodeRange(Node t, uint32_t alphaCard)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(
      Kind::AND,
      nm->mkNode(Kind::GEQ, t, nm->mkConstInt(Rational(0))),
      nm->mkNode(Kind::LT, t, nm->mkConstInt(Rational(alphaCard))));
}

}  // namespace utils
}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
