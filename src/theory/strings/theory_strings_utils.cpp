/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Util functions for theory strings.
 */

#include "theory/strings/theory_strings_utils.h"

#include <sstream>

#include "expr/bound_var_manager.h"
#include "expr/sequence.h"
#include "expr/skolem_manager.h"
#include "expr/sort_to_term.h"
#include "options/strings_options.h"
#include "proof/valid_witness_proof_generator.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/rewriter.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/regexp_entail.h"
#include "theory/strings/skolem_cache.h"
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
  NodeManager* nm = tn.getNodeManager();
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
  NodeManager* nm = t.getNodeManager();
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
  NodeManager* nm = t.getNodeManager();
  Node lent = nm->mkNode(Kind::STRING_LENGTH, t);
  return nm->mkNode(
      Kind::STRING_SUBSTR,
      {t, nm->mkConstInt(Rational(0)), nm->mkNode(Kind::SUB, lent, n)});
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

void printConcatTrace(std::vector<Node>& n, CVC5_UNUSED const char* c)
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
    tn = n.getNodeManager()->stringType();
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

Node mkAbstractStringValueForLength(Node n, Node len, size_t id)
{
  NodeManager* nm = n.getNodeManager();
  Node tn = nm->mkConst(SortToTerm(n.getType()));
  Node idn = nm->mkConstInt(Rational(id));
  Node w = ValidWitnessProofGenerator::mkWitness(
      nm, ProofRule::EXISTS_STRING_LENGTH, {tn, len, idn});
  return w;
}

Node mkCodeRange(Node t, uint32_t alphaCard)
{
  NodeManager* nm = t.getNodeManager();
  return nm->mkNode(
      Kind::AND,
      {nm->mkNode(Kind::GEQ, t, nm->mkConstInt(Rational(0))),
       nm->mkNode(Kind::LT, t, nm->mkConstInt(Rational(alphaCard)))});
}

Node eagerReduce(Node t, SkolemCache* sc, uint32_t alphaCard)
{
  NodeManager* nm = t.getNodeManager();
  Node lemma;
  Kind tk = t.getKind();
  if (tk == Kind::STRING_TO_CODE)
  {
    // ite( str.len(s)==1, 0 <= str.code(s) < |A|, str.code(s)=-1 )
    Node len = nm->mkNode(Kind::STRING_LENGTH, t[0]);
    Node code_len = len.eqNode(nm->mkConstInt(Rational(1)));
    Node code_eq_neg1 = t.eqNode(nm->mkConstInt(Rational(-1)));
    Node code_range = mkCodeRange(t, alphaCard);
    lemma = nm->mkNode(Kind::ITE, code_len, code_range, code_eq_neg1);
  }
  else if (tk == Kind::SEQ_NTH)
  {
    if (t[0].getType().isString())
    {
      Node s = t[0];
      Node n = t[1];
      // start point is greater than or equal zero
      Node c1 = nm->mkNode(Kind::GEQ, n, nm->mkConstInt(0));
      // start point is less than end of string
      Node c2 = nm->mkNode(Kind::GT, nm->mkNode(Kind::STRING_LENGTH, s), n);
      // check whether this application of seq.nth is defined.
      Node cond = nm->mkNode(Kind::AND, c1, c2);
      Node code_range = mkCodeRange(t, alphaCard);
      // the lemma for `seq.nth`
      lemma = nm->mkNode(
          Kind::ITE, cond, code_range, t.eqNode(nm->mkConstInt(Rational(-1))));
      // IF: n >=0 AND n < len( s )
      // THEN: 0 <= (seq.nth s n) < |A|
      // ELSE: (seq.nth s n) = -1
    }
  }
  else if (tk == Kind::STRING_INDEXOF || tk == Kind::STRING_INDEXOF_RE)
  {
    // (and
    //   (or (= (f x y n) (- 1)) (>= (f x y n) n))
    //   (<= (f x y n) (str.len x)))
    //
    // where f in { str.indexof, str.indexof_re }
    Node l = nm->mkNode(Kind::STRING_LENGTH, t[0]);
    lemma = nm->mkNode(Kind::AND,
                       {nm->mkNode(Kind::OR,
                                   {t.eqNode(nm->mkConstInt(Rational(-1))),
                                    nm->mkNode(Kind::GEQ, t, t[2])}),
                        nm->mkNode(Kind::LEQ, t, l)});
  }
  else if (tk == Kind::STRING_STOI)
  {
    // (>= (str.to_int x) (- 1))
    lemma = nm->mkNode(Kind::GEQ, t, nm->mkConstInt(Rational(-1)));
  }
  else if (tk == Kind::STRING_CONTAINS)
  {
    // ite( (str.contains s r), (= s (str.++ sk1 r sk2)), (not (= s r)))
    Node sk1 =
        sc->mkSkolemCached(t[0], t[1], SkolemCache::SK_FIRST_CTN_PRE, "sc1");
    Node sk2 =
        sc->mkSkolemCached(t[0], t[1], SkolemCache::SK_FIRST_CTN_POST, "sc2");
    lemma = t[0].eqNode(nm->mkNode(Kind::STRING_CONCAT, sk1, t[1], sk2));
    lemma = nm->mkNode(Kind::ITE, t, lemma, t[0].eqNode(t[1]).notNode());
  }
  else if (tk == Kind::STRING_IN_REGEXP)
  {
    // for (str.in_re t R), if R has a fixed length L, then we infer the lemma:
    // (str.in_re t R) => (= (str.len t) L).
    Node len = RegExpEntail::getFixedLengthForRegexp(t[1]);
    if (!len.isNull())
    {
      lemma = nm->mkNode(
          Kind::IMPLIES, t, nm->mkNode(Kind::STRING_LENGTH, t[0]).eqNode(len));
    }
  }
  else if (tk == Kind::STRING_FROM_CODE)
  {
    // str.from_code(t) ---> ite(0 <= t < |A|, t = str.to_code(k), k = "")
    Node k = sc->mkSkolemCached(t, SkolemCache::SK_PURIFY, "kFromCode");
    Node tc = t[0];
    Node card = nm->mkConstInt(Rational(alphaCard));
    Node cond = nm->mkNode(Kind::AND,
                           {nm->mkNode(Kind::LEQ, nm->mkConstInt(0), tc),
                            nm->mkNode(Kind::LT, tc, card)});
    Node emp = Word::mkEmptyWord(t.getType());
    lemma = nm->mkNode(
        Kind::ITE,
        {cond, tc.eqNode(nm->mkNode(Kind::STRING_TO_CODE, k)), k.eqNode(emp)});
  }
  return lemma;
}

Node lengthPositive(Node t)
{
  NodeManager* nm = t.getNodeManager();
  Node zero = nm->mkConstInt(Rational(0));
  Node emp = Word::mkEmptyWord(t.getType());
  Node tlen = nm->mkNode(Kind::STRING_LENGTH, t);
  Node tlenEqZero = tlen.eqNode(zero);
  Node tEqEmp = t.eqNode(emp);
  Node caseEmpty = nm->mkNode(Kind::AND, tlenEqZero, tEqEmp);
  Node caseNEmpty = nm->mkNode(Kind::GT, tlen, zero);
  // (or (and (= (str.len t) 0) (= t "")) (> (str.len t) 0))
  return nm->mkNode(Kind::OR, caseEmpty, caseNEmpty);
}

Node getConcatConclusion(NodeManager* nm,
                         Node x,
                         Node y,
                         ProofRule rule,
                         bool isRev,
                         SkolemCache* skc,
                         std::vector<Node>& newSkolems)
{
  Trace("strings-csolver") << "getConcatConclusion: " << x << " " << y << " "
                           << rule << " " << isRev << std::endl;
  Node conc;
  if (rule == ProofRule::CONCAT_SPLIT || rule == ProofRule::CONCAT_LPROP)
  {
    Node sk = skc->mkSkolemCached(x,
                                  y,
                                  isRev ? SkolemCache::SK_ID_V_UNIFIED_SPT_REV
                                        : SkolemCache::SK_ID_V_UNIFIED_SPT,
                                  "v_spt");
    newSkolems.push_back(sk);
    Node eq1 = x.eqNode(isRev ? nm->mkNode(Kind::STRING_CONCAT, sk, y)
                              : nm->mkNode(Kind::STRING_CONCAT, y, sk));

    if (rule == ProofRule::CONCAT_LPROP)
    {
      conc = eq1;
    }
    else
    {
      Node eq2 = y.eqNode(isRev ? nm->mkNode(Kind::STRING_CONCAT, sk, x)
                                : nm->mkNode(Kind::STRING_CONCAT, x, sk));
      conc = nm->mkNode(Kind::OR, eq1, eq2);
    }
    // we can assume its length is greater than zero
    Node emp = Word::mkEmptyWord(sk.getType());
    conc = nm->mkNode(Kind::AND,
                      {conc,
                       sk.eqNode(emp).negate(),
                       nm->mkNode(Kind::GT,
                                  {nm->mkNode(Kind::STRING_LENGTH, sk),
                                   nm->mkConstInt(Rational(0))})});
  }
  else if (rule == ProofRule::CONCAT_CSPLIT)
  {
    Assert(y.isConst());
    size_t yLen = Word::getLength(y);
    Node firstChar =
        yLen == 1 ? y : (isRev ? Word::suffix(y, 1) : Word::prefix(y, 1));
    Node sk = skc->mkSkolemCached(
        x,
        isRev ? SkolemCache::SK_ID_VC_SPT_REV : SkolemCache::SK_ID_VC_SPT,
        "c_spt");
    newSkolems.push_back(sk);
    conc = x.eqNode(isRev ? nm->mkNode(Kind::STRING_CONCAT, sk, firstChar)
                          : nm->mkNode(Kind::STRING_CONCAT, firstChar, sk));
  }
  else if (rule == ProofRule::CONCAT_CPROP)
  {
    // expect (str.++ z d) and c
    Assert(x.getKind() == Kind::STRING_CONCAT && x.getNumChildren() == 2);
    Node z = x[isRev ? 1 : 0];
    Node d = x[isRev ? 0 : 1];
    Assert(d.isConst());
    Node c = y;
    Assert(c.isConst());
    size_t p = getSufficientNonEmptyOverlap(c, d, isRev);
    Node rp = nm->mkConstInt(p);
    Node preC = (isRev ? mkSuffixOfLen(c, rp) : mkPrefix(c, rp));
    Node sk = skc->mkSkolemCached(
        z,
        preC,
        isRev ? SkolemCache::SK_ID_C_SPT_REV : SkolemCache::SK_ID_C_SPT,
        "c_spt");
    newSkolems.push_back(sk);
    conc = z.eqNode(isRev ? nm->mkNode(Kind::STRING_CONCAT, sk, preC)
                          : nm->mkNode(Kind::STRING_CONCAT, preC, sk));
  }

  return conc;
}

size_t getSufficientNonEmptyOverlap(Node c, Node d, bool isRev)
{
  Assert(c.isConst() && c.getType().isStringLike());
  Assert(d.isConst() && d.getType().isStringLike());
  size_t p;
  size_t p2;
  size_t cLen = Word::getLength(c);
  if (isRev)
  {
    // Since non-empty, we start with character 1
    Node c1 = Word::prefix(c, cLen - 1);
    p = cLen - Word::roverlap(c1, d);
    p2 = Word::rfind(c1, d);
  }
  else
  {
    Node c1 = Word::substr(c, 1);
    p = cLen - Word::overlap(c1, d);
    p2 = Word::find(c1, d);
  }
  return p2 == std::string::npos ? p : (p > p2 + 1 ? p2 + 1 : p);
}

Node getDecomposeConclusion(NodeManager* nm,
                            Node x,
                            Node l,
                            bool isRev,
                            SkolemCache* skc,
                            std::vector<Node>& newSkolems)
{
  Assert(l.getType().isInteger());
  Node n =
      isRev ? nm->mkNode(Kind::SUB, nm->mkNode(Kind::STRING_LENGTH, x), l) : l;
  Node sk1 = skc->mkSkolemCached(x, n, SkolemCache::SK_PREFIX, "dc_spt1");
  newSkolems.push_back(sk1);
  Node sk2 = skc->mkSkolemCached(x, n, SkolemCache::SK_SUFFIX_REM, "dc_spt2");
  newSkolems.push_back(sk2);
  Node conc = x.eqNode(nm->mkNode(Kind::STRING_CONCAT, sk1, sk2));
  // add the length constraint to the conclusion
  Node lc = nm->mkNode(Kind::STRING_LENGTH, isRev ? sk2 : sk1).eqNode(l);
  return nm->mkNode(Kind::AND, conc, lc);
}

Node getExtensionalityConclusion(NodeManager* nm,
                                 const Node& a,
                                 const Node& b,
                                 SkolemCache* skc)
{
  Node k = skc->mkSkolemFun(nm, SkolemId::STRINGS_DEQ_DIFF, a, b);
  // we could use seq.nth instead of substr
  Node ss1, ss2;
  if (a.getType().isString())
  {
    // substring of length 1
    Node one = nm->mkConstInt(Rational(1));
    ss1 = nm->mkNode(Kind::STRING_SUBSTR, a, k, one);
    ss2 = nm->mkNode(Kind::STRING_SUBSTR, b, k, one);
  }
  else
  {
    // as an optimization, for sequences, use seq.nth
    ss1 = nm->mkNode(Kind::SEQ_NTH, a, k);
    ss2 = nm->mkNode(Kind::SEQ_NTH, b, k);
  }

  // disequality between nth/substr
  Node conc1 = ss1.eqNode(ss2).negate();

  // The skolem k is in the bounds of at least
  // one string/sequence
  Node len1 = nm->mkNode(Kind::STRING_LENGTH, a);
  Node len2 = nm->mkNode(Kind::STRING_LENGTH, b);
  Node zero = nm->mkConstInt(Rational(0));
  Node conc2 = nm->mkNode(Kind::LEQ, zero, k);
  Node conc3 = nm->mkNode(Kind::LT, k, len1);
  Node lenDeq = nm->mkNode(Kind::EQUAL, len1, len2).negate();

  std::vector<Node> concs = {conc1, conc2, conc3};
  return nm->mkNode(Kind::OR, lenDeq, nm->mkAnd(concs));
}

}  // namespace utils
}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
