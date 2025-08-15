/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of term registry for the theory of strings.
 */

#include "theory/strings/term_registry.h"

#include "options/smt_options.h"
#include "options/strings_options.h"
#include "printer/smt2/smt2_printer.h"
#include "smt/logic_exception.h"
#include "theory/rewriter.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/regexp_entail.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "theory/theory.h"
#include "util/rational.h"
#include "util/string.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

TermRegistry::TermRegistry(Env& env,
                           Theory& t,
                           SolverState& s,
                           SequencesStatistics& statistics)
    : EnvObj(env),
      d_theory(t),
      d_state(s),
      d_im(nullptr),
      d_statistics(statistics),
      d_hasStrCode(false),
      d_hasSeqUpdate(false),
      d_skCache(nodeManager(), env.getRewriter()),
      d_aent(nodeManager(), env.getRewriter()),
      d_functionsTerms(context()),
      d_inputVars(userContext()),
      d_preregisteredTerms(context()),
      d_registeredTerms(userContext()),
      d_registeredTypes(userContext()),
      d_proxyVar(userContext()),
      d_proxyVarToLength(userContext()),
      d_lengthLemmaTermsCache(userContext()),
      d_epg(
          env.isTheoryProofProducing() ? new EagerProofGenerator(
              env, userContext(), "strings::TermRegistry::EagerProofGenerator")
                                       : nullptr),
      d_inFullEffortCheck(false)
{
  NodeManager* nm = nodeManager();
  d_zero = nm->mkConstInt(Rational(0));
  d_one = nm->mkConstInt(Rational(1));
  d_negOne = nm->mkConstInt(Rational(-1));
  Assert(options().strings.stringsAlphaCard <= String::num_codes());
  d_alphaCard = options().strings.stringsAlphaCard;
}

TermRegistry::~TermRegistry() {}

uint32_t TermRegistry::getAlphabetCardinality() const { return d_alphaCard; }

void TermRegistry::finishInit(InferenceManager* im) { d_im = im; }

Node TermRegistry::eagerReduce(Node t, SkolemCache* sc, uint32_t alphaCard)
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
    Node code_range = utils::mkCodeRange(t, alphaCard);
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
      Node code_range = utils::mkCodeRange(t, alphaCard);
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
                       nm->mkNode(Kind::OR,
                                  t.eqNode(nm->mkConstInt(Rational(-1))),
                                  nm->mkNode(Kind::GEQ, t, t[2])),
                       nm->mkNode(Kind::LEQ, t, l));
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
                           nm->mkNode(Kind::LEQ, nm->mkConstInt(0), tc),
                           nm->mkNode(Kind::LT, tc, card));
    Node emp = Word::mkEmptyWord(t.getType());
    lemma = nm->mkNode(Kind::ITE,
                       cond,
                       tc.eqNode(nm->mkNode(Kind::STRING_TO_CODE, k)),
                       k.eqNode(emp));
  }
  return lemma;
}

Node TermRegistry::lengthPositive(Node t)
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

void TermRegistry::preRegisterTerm(TNode n)
{
  if (d_preregisteredTerms.find(n) != d_preregisteredTerms.end())
  {
    return;
  }
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  d_preregisteredTerms.insert(n);
  Trace("strings-preregister")
      << "TheoryString::preregister : " << n << std::endl;
  // check for logic exceptions
  Kind k = n.getKind();
  if (k == Kind::EQUAL && n[0].getType().isRegExp())
  {
    // if an equality between regular expressions was introduced during solving,
    // e.g. by theory combination, we send the equivalance for its quantified
    // reduction here, e.g.
    // (R1 = R2) = (forall s. (s in R1) = (s in R2)).
    Node res =
        d_env.getRewriter()->rewriteViaRule(ProofRewriteRule::RE_EQ_ELIM, n);
    Node lem = nodeManager()->mkNode(Kind::EQUAL, n, res);
    d_im->lemma(lem, InferenceId::STRINGS_RE_EQ_ELIM_EQUIV);
  }
  if (k == Kind::STRING_IN_REGEXP)
  {
    d_im->preferPhase(n, true);
  }
  else if (k == Kind::STRING_TO_CODE)
  {
    d_hasStrCode = true;
  }
  else if (k == Kind::SEQ_NTH || k == Kind::STRING_UPDATE)
  {
    d_hasSeqUpdate = true;
  }
  else if (k == Kind::CONST_SEQUENCE)
  {
    // If we are a constant sequence that has "nested" constant sequences
    // implicitly, e.g. for sequences of sequences, then we must ensure that
    // all subterms of this constant are also considered as terms by the
    // solver. Otherwise, these terms would be hidden inside of the sequence
    // constant. To do so, we ensure a purify skolem is introduced for each
    // subterm. For example, for the sequence constant t:
    //   (str.++ (as seq.empty (Seq Int)) (seq.unit (str.++ 0 1)))
    // We add the lemma:
    //   k1 = (as seq.empty (Seq Int)) ^ k2 = (seq.unit (str.++ 0 1)) ^
    //   t = (str.++ k1 k2).
    // The right hand sides of the first two equalties will lead to
    // preregistering these sequence constants in the same way.
    // These lemmas can be justified trivially by MACRO_SR_PRED_INTRO.
    Node nc = utils::mkConcatForConstSequence(n);
    Kind nck = nc.getKind();
    if (nck != Kind::CONST_SEQUENCE)
    {
      std::vector<Node> eqs;
      std::vector<Node> children;
      for (const Node& ncc : nc)
      {
        if (ncc.getKind() == Kind::CONST_SEQUENCE)
        {
          Node skolem = SkolemManager::mkPurifySkolem(ncc);
          children.push_back(skolem);
          eqs.push_back(skolem.eqNode(ncc));
        }
        else
        {
          children.push_back(ncc);
        }
      }
      Node ret = nodeManager()->mkNode(nck, children);
      eqs.push_back(n.eqNode(ret));
      Node lem = nodeManager()->mkAnd(eqs);
      Trace("strings-preregister")
          << "Const sequence lemma: " << lem << std::endl;
      d_im->lemma(lem, InferenceId::STRINGS_CONST_SEQ_PURIFY);
    }
  }
  if (options().strings.stringEagerReg)
  {
    registerTerm(n);
  }
  TypeNode tn = n.getType();
  registerType(tn);
  if (tn.isRegExp() && n.isVar())
  {
    std::stringstream ss;
    ss << "Regular expression variables are not supported.";
    throw LogicException(ss.str());
  }
  if (tn.isBoolean())
  {
    // All kinds that we do congruence over that may return a Boolean go here
    if (k == Kind::STRING_CONTAINS || k == Kind::STRING_LEQ
        || k == Kind::SEQ_NTH || k == Kind::EQUAL)
    {
      // Get triggered for both equal and dis-equal
      d_state.addEqualityEngineTriggerPredicate(n);
    }
  }
  else
  {
    // Function applications/predicates
    ee->addTerm(n);
  }
  // Set d_functionsTerms stores all function applications that are
  // relevant to theory combination. Notice that this is a subset of
  // the applications whose kinds are function kinds in the equality
  // engine. This means it does not include applications of operators
  // like re.++, which is not a function kind in the equality engine.
  // Concatenation terms do not need to be considered here because
  // their arguments have string type and do not introduce any shared
  // terms.
  if (n.hasOperator() && ee->isFunctionKind(k)
      && kindToTheoryId(k) == THEORY_STRINGS && k != Kind::STRING_CONCAT
      && k != Kind::STRING_IN_REGEXP)
  {
    d_functionsTerms.push_back(n);
  }
}

void TermRegistry::preRegisterInputVar(TNode n) { d_inputVars.insert(n); }

void TermRegistry::registerSubterms(Node n)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (d_registeredTerms.find(cur) == d_registeredTerms.end())
    {
      registerTermInternal(cur);
      Kind k = cur.getKind();
      // only traverse beneath operators belonging to strings
      if (k == Kind::EQUAL || theory::kindToTheoryId(k) == THEORY_STRINGS)
      {
        // strings does not have any closure kinds
        Assert (!cur.isClosure());
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  } while (!visit.empty());
}

void TermRegistry::registerTerm(Node n)
{
  if (d_registeredTerms.find(n) != d_registeredTerms.end())
  {
    return;
  }
  registerTermInternal(n);
}

void TermRegistry::registerTermInternal(Node n)
{
  Assert(d_registeredTerms.find(n) == d_registeredTerms.end());
  Trace("strings-register")
      << "TheoryStrings::registerTermInternal() " << n << std::endl;
  d_registeredTerms.insert(n);
  // ensure the type is registered
  TypeNode tn = n.getType();
  TrustNode regTermLem;
  if (tn.isStringLike())
  {
    // register length information:
    //  for variables, split on empty vs positive length
    //  for concat/const/replace, introduce proxy var and state length relation
    regTermLem = getRegisterTermLemma(n);
  }
  else
  {
    // we don't send out eager reduction lemma for str.contains currently
    bool doEagerReduce = true;
    Kind k = n.getKind();
    if (k == Kind::STRING_CONTAINS)
    {
      doEagerReduce = false;
    }
    else if (k == Kind::STRING_TO_CODE)
    {
      // code for proxy are implied
      Node c = SkolemManager::getOriginalForm(n[0]);
      doEagerReduce = !c.isConst();
    }
    if (doEagerReduce)
    {
      regTermLem = eagerReduceTrusted(n);
    }
  }
  if (!regTermLem.isNull())
  {
    Trace("strings-lemma") << "Strings::Lemma REG-TERM : " << regTermLem
                           << std::endl;
    Trace("strings-assert")
        << "(assert " << regTermLem.getNode() << ")" << std::endl;
    d_im->trustedLemma(regTermLem, InferenceId::STRINGS_REGISTER_TERM);
  }
}

TrustNode TermRegistry::eagerReduceTrusted(const Node& n)
{
  TrustNode regTermLem;
  Node eagerRedLemma = eagerReduce(n, &d_skCache, d_alphaCard);
  if (!eagerRedLemma.isNull())
  {
    if (d_epg != nullptr)
    {
      regTermLem = d_epg->mkTrustNode(
          eagerRedLemma, ProofRule::STRING_EAGER_REDUCTION, {}, {n});
    }
    else
    {
      regTermLem = TrustNode::mkTrustLemma(eagerRedLemma, nullptr);
    }
  }
  return regTermLem;
}

void TermRegistry::registerType(TypeNode tn)
{
  if (d_registeredTypes.find(tn) != d_registeredTypes.end())
  {
    return;
  }
  d_registeredTypes.insert(tn);
  if (tn.isStringLike())
  {
    // preregister the empty word for the type
    Node emp = Word::mkEmptyWord(tn);
    // always preregister and register unconditionally eagerly
    preRegisterTerm(emp);
    registerTerm(emp);
  }
}

TrustNode TermRegistry::getRegisterTermLemma(Node n)
{
  Assert(n.getType().isStringLike());
  NodeManager* nm = nodeManager();
  // register length information:
  //  for variables, split on empty vs positive length
  //  for concat/const/replace, introduce proxy var and state length relation
  Node lsum;
  Kind nk = n.getKind();
  if (nk != Kind::STRING_CONCAT && !n.isConst())
  {
    Node lsumb = nm->mkNode(Kind::STRING_LENGTH, n);
    lsum = rewrite(lsumb);
    // can register length term if it does not rewrite
    if (lsum == lsumb)
    {
      registerTermAtomic(n, LENGTH_SPLIT);
      return TrustNode::null();
    }
  }
  Node sk = d_skCache.mkSkolemCached(n, SkolemCache::SK_PURIFY, "lsym");
  Node eq = rewrite(sk.eqNode(n));
  d_proxyVar[n] = sk;
  // If we are introducing a proxy for a constant or concat term, we do not
  // need to send lemmas about its length, since its length is already
  // implied.
  if (n.isConst() || nk == Kind::STRING_CONCAT)
  {
    // do not send length lemma for sk.
    registerTermAtomic(sk, LENGTH_IGNORE);
  }
  Node skl = nm->mkNode(Kind::STRING_LENGTH, sk);
  if (nk == Kind::STRING_CONCAT)
  {
    std::vector<Node> nodeVec;
    NodeNodeMap::const_iterator itl;
    for (const Node& nc : n)
    {
      itl = d_proxyVarToLength.find(nc);
      if (itl != d_proxyVarToLength.end())
      {
        nodeVec.push_back(itl->second);
      }
      else
      {
        Node lni = nm->mkNode(Kind::STRING_LENGTH, nc);
        nodeVec.push_back(lni);
      }
    }
    lsum = nm->mkNode(Kind::ADD, nodeVec);
    lsum = rewrite(lsum);
  }
  else if (n.isConst())
  {
    lsum = nm->mkConstInt(Rational(Word::getLength(n)));
  }
  Assert(!lsum.isNull());
  d_proxyVarToLength[sk] = lsum;
  Node ceq = rewrite(skl.eqNode(lsum));

  Node ret = nm->mkNode(Kind::AND, eq, ceq);

  // it is a simple rewrite to justify this
  if (d_epg != nullptr)
  {
    return d_epg->mkTrustNode(ret, ProofRule::MACRO_SR_PRED_INTRO, {}, {ret});
  }
  return TrustNode::mkTrustLemma(ret, nullptr);
}

void TermRegistry::registerTermAtomic(Node n, LengthStatus s)
{
  if (d_lengthLemmaTermsCache.find(n) != d_lengthLemmaTermsCache.end())
  {
    return;
  }
  d_lengthLemmaTermsCache.insert(n);

  if (s == LENGTH_IGNORE)
  {
    // ignore it
    return;
  }
  std::map<Node, bool> reqPhase;
  TrustNode lenLem = getRegisterTermAtomicLemma(n, s, reqPhase);
  if (!lenLem.isNull())
  {
    Trace("strings-lemma") << "Strings::Lemma REGISTER-TERM-ATOMIC : " << lenLem
                           << std::endl;
    Trace("strings-assert")
        << "(assert " << lenLem.getNode() << ")" << std::endl;
    d_im->trustedLemma(lenLem, InferenceId::STRINGS_REGISTER_TERM_ATOMIC);
  }
  for (const std::pair<const Node, bool>& rp : reqPhase)
  {
    d_im->preferPhase(rp.first, rp.second);
  }
}

SkolemCache* TermRegistry::getSkolemCache() { return &d_skCache; }

const context::CDList<TNode>& TermRegistry::getFunctionTerms() const
{
  return d_functionsTerms;
}

const context::CDHashSet<Node>& TermRegistry::getInputVars() const
{
  return d_inputVars;
}

bool TermRegistry::hasStringCode() const { return d_hasStrCode; }

bool TermRegistry::hasSeqUpdate() const { return d_hasSeqUpdate; }

bool TermRegistry::isHandledUpdateOrSubstr(Node n)
{
  Assert(n.getKind() == Kind::STRING_UPDATE
         || n.getKind() == Kind::STRING_SUBSTR);
  NodeManager* nm = nodeManager();
  Node lenN = n[2];
  if (n.getKind() == Kind::STRING_UPDATE)
  {
    lenN = nm->mkNode(Kind::STRING_LENGTH, n[2]);
  }
  Node one = nm->mkConstInt(Rational(1));
  return d_aent.checkEq(lenN, one);
}

Node TermRegistry::getUpdateBase(Node n)
{
  while (n.getKind() == Kind::STRING_UPDATE)
  {
    n = n[0];
  }
  return n;
}

TrustNode TermRegistry::getRegisterTermAtomicLemma(
    Node n, LengthStatus s, std::map<Node, bool>& reqPhase)
{
  if (n.isConst())
  {
    // No need to send length for constant terms. This case may be triggered
    // for cases where the skolem cache automatically replaces a skolem by
    // a constant.
    return TrustNode::null();
  }
  Assert(n.getType().isStringLike());
  NodeManager* nm = nodeManager();
  Node n_len = nm->mkNode(Kind::STRING_LENGTH, n);
  Node emp = Word::mkEmptyWord(n.getType());
  if (s == LENGTH_GEQ_ONE)
  {
    Node neq_empty = n.eqNode(emp).negate();
    Node len_n_gt_z = nm->mkNode(Kind::GT, n_len, d_zero);
    Node len_geq_one = nm->mkNode(Kind::AND, neq_empty, len_n_gt_z);
    Trace("strings-lemma") << "Strings::Lemma SK-GEQ-ONE : " << len_geq_one
                           << std::endl;
    Trace("strings-assert") << "(assert " << len_geq_one << ")" << std::endl;
    return TrustNode::mkTrustLemma(len_geq_one, nullptr);
  }

  if (s == LENGTH_ONE)
  {
    Node len_one = n_len.eqNode(d_one);
    Trace("strings-lemma") << "Strings::Lemma SK-ONE : " << len_one
                           << std::endl;
    Trace("strings-assert") << "(assert " << len_one << ")" << std::endl;
    return TrustNode::mkTrustLemma(len_one, nullptr);
  }
  Assert(s == LENGTH_SPLIT);

  // get the positive length lemma
  Node lenLemma = lengthPositive(n);
  // split whether the string is empty
  Node n_len_eq_z = n_len.eqNode(d_zero);
  Node n_len_eq_z_2 = n.eqNode(emp);
  Node case_empty = nm->mkNode(Kind::AND, n_len_eq_z, n_len_eq_z_2);
  Node case_emptyr = rewrite(case_empty);
  if (!case_emptyr.isConst())
  {
    // prefer trying the empty case first
    // notice that preferPhase must only be called on rewritten literals that
    // occur in the CNF stream.
    n_len_eq_z = rewrite(n_len_eq_z);
    Assert(!n_len_eq_z.isConst());
    reqPhase[n_len_eq_z] = true;
    n_len_eq_z_2 = rewrite(n_len_eq_z_2);
    Assert(!n_len_eq_z_2.isConst());
    reqPhase[n_len_eq_z_2] = true;
  }
  else
  {
    // If n = "" ---> true or len( n ) = 0 ----> true, then we expect that
    // n ---> "". Since this method is only called on non-constants n, it must
    // be that n = "" ^ len( n ) = 0 does not rewrite to true.
    Assert(!case_emptyr.getConst<bool>());
  }

  if (d_epg != nullptr)
  {
    return d_epg->mkTrustNode(lenLemma, ProofRule::STRING_LENGTH_POS, {}, {n});
  }
  return TrustNode::mkTrustLemma(lenLemma, nullptr);
}

Node TermRegistry::getSymbolicDefinition(Node n, std::vector<Node>& exp) const
{
  if (n.getNumChildren() == 0)
  {
    Node pn = getProxyVariableFor(n);
    if (pn.isNull())
    {
      return Node::null();
    }
    Node eq = n.eqNode(pn);
    eq = rewrite(eq);
    if (std::find(exp.begin(), exp.end(), eq) == exp.end())
    {
      exp.push_back(eq);
    }
    return pn;
  }
  std::vector<Node> children;
  if (n.getMetaKind() == metakind::PARAMETERIZED)
  {
    children.push_back(n.getOperator());
  }
  for (const Node& nc : n)
  {
    if (n.getType().isRegExp())
    {
      children.push_back(nc);
    }
    else
    {
      Node ns = getSymbolicDefinition(nc, exp);
      if (ns.isNull())
      {
        return Node::null();
      }
      else
      {
        children.push_back(ns);
      }
    }
  }
  return nodeManager()->mkNode(n.getKind(), children);
}

Node TermRegistry::getProxyVariableFor(Node n) const
{
  NodeNodeMap::const_iterator it = d_proxyVar.find(n);
  if (it != d_proxyVar.end())
  {
    return (*it).second;
  }
  return Node::null();
}

Node TermRegistry::ensureProxyVariableFor(Node n)
{
  Node proxy = getProxyVariableFor(n);
  if (proxy.isNull())
  {
    registerTerm(n);
    proxy = getProxyVariableFor(n);
  }
  Assert(!proxy.isNull());
  return proxy;
}

void TermRegistry::removeProxyEqs(Node n, std::vector<Node>& unproc) const
{
  if (n.getKind() == Kind::AND)
  {
    for (const Node& nc : n)
    {
      removeProxyEqs(nc, unproc);
    }
    return;
  }
  Trace("strings-subs-proxy") << "Input : " << n << std::endl;
  Node ns = rewrite(n);
  if (ns.getKind() == Kind::EQUAL)
  {
    for (size_t i = 0; i < 2; i++)
    {
      // determine whether this side has a proxy variable
      if (d_proxyVar.find(ns[i]) != d_proxyVar.end())
      {
        if (getProxyVariableFor(ns[1 - i]) == ns[i])
        {
          Trace("strings-subs-proxy")
              << "...trivial definition via " << ns[i] << std::endl;
          // it is a trivial equality, e.g. between a proxy variable
          // and its definition
          return;
        }
      }
    }
  }
  if (!n.isConst() || !n.getConst<bool>())
  {
    Trace("strings-subs-proxy") << "...unprocessed" << std::endl;
    unproc.push_back(n);
  }
}

void TermRegistry::notifyStartFullEffortCheck()
{
  d_inFullEffortCheck = true;
  d_relevantTerms.clear();
  // get the asserted terms
  std::set<Kind> irrKinds;
  d_theory.collectAssertedTerms(d_relevantTerms, true, irrKinds);
  // also, get the additionally relevant terms
  d_theory.computeRelevantTerms(d_relevantTerms);
}

void TermRegistry::notifyEndFullEffortCheck() { d_inFullEffortCheck = false; }

const std::set<Node>& TermRegistry::getRelevantTermSet() const
{
  // must be in full effort check for relevant terms to be valid
  Assert(d_inFullEffortCheck);
  return d_relevantTerms;
}

Node TermRegistry::mkNConcat(Node n1, Node n2) const
{
  return rewrite(NodeManager::mkNode(Kind::STRING_CONCAT, n1, n2));
}

Node TermRegistry::mkNConcat(Node n1, Node n2, Node n3) const
{
  return rewrite(NodeManager::mkNode(Kind::STRING_CONCAT, n1, n2, n3));
}

Node TermRegistry::mkNConcat(const std::vector<Node>& c, TypeNode tn) const
{
  return rewrite(utils::mkConcat(c, tn));
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
