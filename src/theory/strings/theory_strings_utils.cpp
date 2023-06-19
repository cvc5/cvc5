/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

Node mkAnd(const std::vector<Node>& a)
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
    return NodeManager::currentNM()->mkConst(true);
  }
  else if (au.size() == 1)
  {
    return au[0];
  }
  return NodeManager::currentNM()->mkNode(AND, au);
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
  if (k == STRING_CONCAT || k == REGEXP_CONCAT)
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
  if (c.empty())
  {
    Assert(tn.isStringLike());
    return Word::mkEmptyWord(tn);
  }
  else if (c.size() == 1)
  {
    return c[0];
  }
  Kind k = tn.isStringLike() ? STRING_CONCAT : REGEXP_CONCAT;
  return NodeManager::currentNM()->mkNode(k, c);
}

Node mkPrefix(Node t, Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(STRING_SUBSTR, t, nm->mkConstInt(Rational(0)), n);
}

Node mkSuffix(Node t, Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(
      STRING_SUBSTR, t, n, nm->mkNode(SUB, nm->mkNode(STRING_LENGTH, t), n));
}

Node mkUnit(TypeNode tn, Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  if (tn.isString())
  {
    return nm->mkNode(STRING_UNIT, n);
  }
  Assert(tn.isSequence());
  return nm->mkNode(SEQ_UNIT, n);
}

Node getConstantComponent(Node t)
{
  if (t.getKind() == STRING_TO_REGEXP)
  {
    return t[0].isConst() ? t[0] : Node::null();
  }
  return t.isConst() ? t : Node::null();
}

Node getConstantEndpoint(Node e, bool isSuf)
{
  Kind ek = e.getKind();
  if (ek == STRING_IN_REGEXP)
  {
    e = e[1];
    ek = e.getKind();
  }
  if (ek == STRING_CONCAT || ek == REGEXP_CONCAT)
  {
    return getConstantComponent(e[isSuf ? e.getNumChildren() - 1 : 0]);
  }
  return getConstantComponent(e);
}

Node decomposeSubstrChain(Node s, std::vector<Node>& ss, std::vector<Node>& ls)
{
  Assert(ss.empty());
  Assert(ls.empty());
  while (s.getKind() == STRING_SUBSTR)
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
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, size = ss.size(); i < size; i++)
  {
    base = nm->mkNode(STRING_SUBSTR, base, ss[i], ls[i]);
  }
  return base;
}

Node mkConcatForConstSequence(const Node& c)
{
  Assert(c.getKind() == CONST_SEQUENCE);
  const std::vector<Node>& charVec = c.getConst<Sequence>().getVec();
  std::vector<Node> vec;
  NodeManager* nm = NodeManager::currentNM();
  for (size_t i = 0, size = charVec.size(); i < size; i++)
  {
    vec.push_back(nm->mkNode(SEQ_UNIT, charVec[size - (i + 1)]));
  }
  return mkConcat(vec, c.getType());
}

std::pair<bool, std::vector<Node> > collectEmptyEqs(Node x)
{
  // Collect the equalities of the form (= x "") (sorted)
  std::set<TNode> emptyNodes;
  bool allEmptyEqs = true;
  if (x.getKind() == EQUAL)
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
  else if (x.getKind() == AND)
  {
    for (const Node& c : x)
    {
      if (c.getKind() != EQUAL)
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
  return n.isConst() || n.getKind() == SEQ_UNIT || n.getKind() == STRING_UNIT;
}

bool isCharacterRange(TNode t)
{
  Assert(t.getKind() == REGEXP_RANGE);
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
  while (i < rs.size() && rs[i].getKind() == REGEXP_ALLCHAR)
  {
    i++;
  }

  if (i >= rs.size())
  {
    return false;
  }

  return rs[i].getKind() == REGEXP_STAR && rs[i][0].getKind() == REGEXP_ALLCHAR;
}

bool isSimpleRegExp(Node r)
{
  Assert(r.getType().isRegExp());

  std::vector<Node> v;
  utils::getConcat(r, v);
  for (const Node& n : v)
  {
    if (n.getKind() == STRING_TO_REGEXP)
    {
      if (!n[0].isConst())
      {
        return false;
      }
    }
    else if (n.getKind() != REGEXP_ALLCHAR
             && (n.getKind() != REGEXP_STAR
                 || n[0].getKind() != REGEXP_ALLCHAR))
    {
      return false;
    }
  }
  return true;
}

void getRegexpComponents(Node r, std::vector<Node>& result)
{
  Assert(r.getType().isRegExp());

  NodeManager* nm = NodeManager::currentNM();
  if (r.getKind() == REGEXP_CONCAT)
  {
    for (const Node& n : r)
    {
      getRegexpComponents(n, result);
    }
  }
  else if (r.getKind() == STRING_TO_REGEXP && r[0].isConst())
  {
    size_t rlen = Word::getLength(r[0]);
    for (size_t i = 0; i < rlen; i++)
    {
      result.push_back(nm->mkNode(STRING_TO_REGEXP, Word::substr(r[0], i, 1)));
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
  return k == STRING_STOI || k == STRING_ITOS || k == STRING_TO_LOWER
         || k == STRING_TO_UPPER || k == STRING_LEQ || k == STRING_LT
         || k == STRING_FROM_CODE || k == STRING_TO_CODE;
}

bool isRegExpKind(Kind k)
{
  return k == REGEXP_NONE || k == REGEXP_ALL || k == REGEXP_ALLCHAR
         || k == STRING_TO_REGEXP || k == REGEXP_CONCAT || k == REGEXP_UNION
         || k == REGEXP_INTER || k == REGEXP_STAR || k == REGEXP_PLUS
         || k == REGEXP_OPT || k == REGEXP_RANGE || k == REGEXP_LOOP
         || k == REGEXP_RV || k == REGEXP_COMPLEMENT;
}

TypeNode getOwnerStringType(Node n)
{
  TypeNode tn;
  Kind k = n.getKind();
  if (k == STRING_INDEXOF || k == STRING_INDEXOF_RE || k == STRING_LENGTH
      || k == STRING_CONTAINS || k == SEQ_NTH || k == STRING_PREFIX
      || k == STRING_SUFFIX)
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
  AlwaysAssert(tn.isStringLike())
      << "Unexpected term in getOwnerStringType : " << n << ", type " << tn;
  return tn;
}

unsigned getRepeatAmount(TNode node)
{
  Assert(node.getKind() == REGEXP_REPEAT);
  return node.getOperator().getConst<RegExpRepeat>().d_repeatAmount;
}

unsigned getLoopMaxOccurrences(TNode node)
{
  Assert(node.getKind() == REGEXP_LOOP);
  return node.getOperator().getConst<RegExpLoop>().d_loopMaxOcc;
}

unsigned getLoopMinOccurrences(TNode node)
{
  Assert(node.getKind() == REGEXP_LOOP);
  return node.getOperator().getConst<RegExpLoop>().d_loopMinOcc;
}

Node mkForallInternal(Node bvl, Node body)
{
  return quantifiers::BoundedIntegers::mkBoundedForall(bvl, body);
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
  Node pred = nm->mkNode(STRING_LENGTH, v).eqNode(len);
  // return (witness ((v String)) (= (str.len v) len))
  Node bvl = nm->mkNode(BOUND_VAR_LIST, v);
  std::stringstream ss;
  ss << "w" << id;
  return quantifiers::mkNamedQuant(WITNESS, bvl, pred, ss.str());
}

Node mkCodeRange(Node t, uint32_t alphaCard)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(AND,
                    nm->mkNode(GEQ, t, nm->mkConstInt(Rational(0))),
                    nm->mkNode(LT, t, nm->mkConstInt(Rational(alphaCard))));
}

}  // namespace utils
}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
