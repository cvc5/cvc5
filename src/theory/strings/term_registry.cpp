/*********************                                                        */
/*! \file term_registry.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of term registry for the theory of strings.
 **/

#include "theory/strings/term_registry.h"

#include "expr/attribute.h"
#include "options/strings_options.h"
#include "smt/logic_exception.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

struct StringsProxyVarAttributeId
{
};
typedef expr::Attribute<StringsProxyVarAttributeId, bool>
    StringsProxyVarAttribute;

TermRegistry::TermRegistry(context::Context* c,
                           context::UserContext* u,
                           eq::EqualityEngine& ee,
                           OutputChannel& out,
                           SequencesStatistics& statistics)
    : d_ee(ee),
      d_out(out),
      d_statistics(statistics),
      d_hasStrCode(false),
      d_functionsTerms(c),
      d_inputVars(u),
      d_preregisteredTerms(u),
      d_registeredTerms(u),
      d_registeredTypes(u),
      d_proxyVar(u),
      d_proxyVarToLength(u),
      d_lengthLemmaTermsCache(u)
{
  NodeManager* nm = NodeManager::currentNM();
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
  d_negOne = NodeManager::currentNM()->mkConst(Rational(-1));
  d_cardSize = utils::getAlphabetCardinality();
}

TermRegistry::~TermRegistry() {}

void TermRegistry::preRegisterTerm(TNode n)
{
  if (d_preregisteredTerms.find(n) != d_preregisteredTerms.end())
  {
    return;
  }
  d_preregisteredTerms.insert(n);
  Trace("strings-preregister")
      << "TheoryString::preregister : " << n << std::endl;
  // check for logic exceptions
  Kind k = n.getKind();
  if (!options::stringExp())
  {
    if (k == STRING_STRIDOF || k == STRING_ITOS || k == STRING_STOI
        || k == STRING_STRREPL || k == STRING_STRREPLALL || k == STRING_STRCTN
        || k == STRING_LEQ || k == STRING_TOLOWER || k == STRING_TOUPPER
        || k == STRING_REV)
    {
      std::stringstream ss;
      ss << "Term of kind " << k
         << " not supported in default mode, try --strings-exp";
      throw LogicException(ss.str());
    }
  }
  if (k == EQUAL)
  {
    if (n[0].getType().isRegExp())
    {
      std::stringstream ss;
      ss << "Equality between regular expressions is not supported";
      throw LogicException(ss.str());
    }
    d_ee.addTriggerEquality(n);
    return;
  }
  else if (k == STRING_IN_REGEXP)
  {
    d_out.requirePhase(n, true);
    d_ee.addTriggerPredicate(n);
    d_ee.addTerm(n[0]);
    d_ee.addTerm(n[1]);
    return;
  }
  else if (k == STRING_TO_CODE)
  {
    d_hasStrCode = true;
  }
  registerTerm(n, 0);
  TypeNode tn = n.getType();
  if (tn.isRegExp() && n.isVar())
  {
    std::stringstream ss;
    ss << "Regular expression variables are not supported.";
    throw LogicException(ss.str());
  }
  if (tn.isString())
  {
    // all characters of constants should fall in the alphabet
    if (n.isConst())
    {
      std::vector<unsigned> vec = n.getConst<String>().getVec();
      for (unsigned u : vec)
      {
        if (u >= d_cardSize)
        {
          std::stringstream ss;
          ss << "Characters in string \"" << n
             << "\" are outside of the given alphabet.";
          throw LogicException(ss.str());
        }
      }
    }
    d_ee.addTerm(n);
  }
  else if (tn.isBoolean())
  {
    // Get triggered for both equal and dis-equal
    d_ee.addTriggerPredicate(n);
  }
  else
  {
    // Function applications/predicates
    d_ee.addTerm(n);
  }
  // Set d_functionsTerms stores all function applications that are
  // relevant to theory combination. Notice that this is a subset of
  // the applications whose kinds are function kinds in the equality
  // engine. This means it does not include applications of operators
  // like re.++, which is not a function kind in the equality engine.
  // Concatenation terms do not need to be considered here because
  // their arguments have string type and do not introduce any shared
  // terms.
  if (n.hasOperator() && d_ee.isFunctionKind(k) && k != STRING_CONCAT)
  {
    d_functionsTerms.push_back(n);
  }
  if (options::stringFMF())
  {
    if (tn.isStringLike())
    {
      // Our decision strategy will minimize the length of this term if it is a
      // variable but not an internally generated Skolem, or a term that does
      // not belong to this theory.
      if (n.isVar() ? !d_skCache.isSkolem(n)
                    : kindToTheoryId(k) != THEORY_STRINGS)
      {
        d_inputVars.insert(n);
        Trace("strings-preregister") << "input variable: " << n << std::endl;
      }
    }
  }
}

void TermRegistry::registerTerm(Node n, int effort)
{
  TypeNode tn = n.getType();
  bool do_register = true;
  if (!tn.isStringLike())
  {
    if (options::stringEagerLen())
    {
      do_register = effort == 0;
    }
    else
    {
      do_register = effort > 0 || n.getKind() != STRING_CONCAT;
    }
  }
  if (!do_register)
  {
    return;
  }
  if (d_registeredTerms.find(n) != d_registeredTerms.end())
  {
    return;
  }
  d_registeredTerms.insert(n);
  // ensure the type is registered
  registerType(tn);
  NodeManager* nm = NodeManager::currentNM();
  Debug("strings-register") << "TheoryStrings::registerTerm() " << n
                            << ", effort = " << effort << std::endl;
  Node regTermLem;
  if (tn.isStringLike())
  {
    // register length information:
    //  for variables, split on empty vs positive length
    //  for concat/const/replace, introduce proxy var and state length relation
    regTermLem = getRegisterTermLemma(n);
  }
  else if (n.getKind() == STRING_TO_CODE)
  {
    // ite( str.len(s)==1, 0 <= str.code(s) < |A|, str.code(s)=-1 )
    Node code_len = utils::mkNLength(n[0]).eqNode(d_one);
    Node code_eq_neg1 = n.eqNode(d_negOne);
    Node code_range = nm->mkNode(
        AND,
        nm->mkNode(GEQ, n, d_zero),
        nm->mkNode(
            LT, n, nm->mkConst(Rational(utils::getAlphabetCardinality()))));
    regTermLem = nm->mkNode(ITE, code_len, code_range, code_eq_neg1);
  }
  else if (n.getKind() == STRING_STRIDOF)
  {
    Node len = utils::mkNLength(n[0]);
    regTermLem = nm->mkNode(AND,
                            nm->mkNode(GEQ, n, nm->mkConst(Rational(-1))),
                            nm->mkNode(LEQ, n, len));
  }
  else if (n.getKind() == STRING_STOI)
  {
    regTermLem = nm->mkNode(GEQ, n, nm->mkConst(Rational(-1)));
  }
  if (!regTermLem.isNull())
  {
    Trace("strings-lemma") << "Strings::Lemma REG-TERM : " << regTermLem
                           << std::endl;
    Trace("strings-assert") << "(assert " << regTermLem << ")" << std::endl;
    ++(d_statistics.d_lemmasRegisterTerm);
    d_out.lemma(regTermLem);
  }
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
    if (!d_ee.hasTerm(emp))
    {
      preRegisterTerm(emp);
    }
  }
}

Node TermRegistry::getRegisterTermLemma(Node n)
{
  Assert(n.getType().isStringLike());
  NodeManager* nm = NodeManager::currentNM();
  // register length information:
  //  for variables, split on empty vs positive length
  //  for concat/const/replace, introduce proxy var and state length relation
  Node lsum;
  if (n.getKind() != STRING_CONCAT && !n.isConst())
  {
    Node lsumb = nm->mkNode(STRING_LENGTH, n);
    lsum = Rewriter::rewrite(lsumb);
    // can register length term if it does not rewrite
    if (lsum == lsumb)
    {
      registerTermAtomic(n, LENGTH_SPLIT);
      return Node::null();
    }
  }
  Node sk = d_skCache.mkSkolemCached(n, SkolemCache::SK_PURIFY, "lsym");
  StringsProxyVarAttribute spva;
  sk.setAttribute(spva, true);
  Node eq = Rewriter::rewrite(sk.eqNode(n));
  d_proxyVar[n] = sk;
  // If we are introducing a proxy for a constant or concat term, we do not
  // need to send lemmas about its length, since its length is already
  // implied.
  if (n.isConst() || n.getKind() == STRING_CONCAT)
  {
    // do not send length lemma for sk.
    registerTermAtomic(sk, LENGTH_IGNORE);
  }
  Node skl = nm->mkNode(STRING_LENGTH, sk);
  if (n.getKind() == STRING_CONCAT)
  {
    std::vector<Node> nodeVec;
    for (const Node& nc : n)
    {
      if (nc.getAttribute(StringsProxyVarAttribute()))
      {
        Assert(d_proxyVarToLength.find(nc) != d_proxyVarToLength.end());
        nodeVec.push_back(d_proxyVarToLength[nc]);
      }
      else
      {
        Node lni = nm->mkNode(STRING_LENGTH, nc);
        nodeVec.push_back(lni);
      }
    }
    lsum = nm->mkNode(PLUS, nodeVec);
    lsum = Rewriter::rewrite(lsum);
  }
  else if (n.isConst())
  {
    lsum = nm->mkConst(Rational(Word::getLength(n)));
  }
  Assert(!lsum.isNull());
  d_proxyVarToLength[sk] = lsum;
  Node ceq = Rewriter::rewrite(skl.eqNode(lsum));

  return nm->mkNode(AND, eq, ceq);
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
  Node lenLem = getRegisterTermAtomicLemma(n, s, reqPhase);
  if (!lenLem.isNull())
  {
    Trace("strings-lemma") << "Strings::Lemma REGISTER-TERM-ATOMIC : " << lenLem
                           << std::endl;
    Trace("strings-assert") << "(assert " << lenLem << ")" << std::endl;
    ++(d_statistics.d_lemmasRegisterTermAtomic);
    d_out.lemma(lenLem);
  }
  for (const std::pair<const Node, bool>& rp : reqPhase)
  {
    d_out.requirePhase(rp.first, rp.second);
  }
}

SkolemCache* TermRegistry::getSkolemCache() { return &d_skCache; }

const context::CDList<TNode>& TermRegistry::getFunctionTerms() const
{
  return d_functionsTerms;
}

const context::CDHashSet<Node, NodeHashFunction>& TermRegistry::getInputVars()
    const
{
  return d_inputVars;
}

bool TermRegistry::hasStringCode() const { return d_hasStrCode; }

Node TermRegistry::getRegisterTermAtomicLemma(Node n,
                                              LengthStatus s,
                                              std::map<Node, bool>& reqPhase)
{
  if (n.isConst())
  {
    // No need to send length for constant terms. This case may be triggered
    // for cases where the skolem cache automatically replaces a skolem by
    // a constant.
    return Node::null();
  }
  Assert(n.getType().isStringLike());
  NodeManager* nm = NodeManager::currentNM();
  Node n_len = nm->mkNode(kind::STRING_LENGTH, n);
  Node emp = Word::mkEmptyWord(n.getType());
  if (s == LENGTH_GEQ_ONE)
  {
    Node neq_empty = n.eqNode(emp).negate();
    Node len_n_gt_z = nm->mkNode(GT, n_len, d_zero);
    Node len_geq_one = nm->mkNode(AND, neq_empty, len_n_gt_z);
    Trace("strings-lemma") << "Strings::Lemma SK-GEQ-ONE : " << len_geq_one
                           << std::endl;
    Trace("strings-assert") << "(assert " << len_geq_one << ")" << std::endl;
    return len_geq_one;
  }

  if (s == LENGTH_ONE)
  {
    Node len_one = n_len.eqNode(d_one);
    Trace("strings-lemma") << "Strings::Lemma SK-ONE : " << len_one
                           << std::endl;
    Trace("strings-assert") << "(assert " << len_one << ")" << std::endl;
    return len_one;
  }
  Assert(s == LENGTH_SPLIT);

  std::vector<Node> lems;
  // split whether the string is empty
  Node n_len_eq_z = n_len.eqNode(d_zero);
  Node n_len_eq_z_2 = n.eqNode(emp);
  Node case_empty = nm->mkNode(AND, n_len_eq_z, n_len_eq_z_2);
  case_empty = Rewriter::rewrite(case_empty);
  Node case_nempty = nm->mkNode(GT, n_len, d_zero);
  if (!case_empty.isConst())
  {
    Node lem = nm->mkNode(OR, case_empty, case_nempty);
    lems.push_back(lem);
    // prefer trying the empty case first
    // notice that requirePhase must only be called on rewritten literals that
    // occur in the CNF stream.
    n_len_eq_z = Rewriter::rewrite(n_len_eq_z);
    Assert(!n_len_eq_z.isConst());
    reqPhase[n_len_eq_z] = true;
    n_len_eq_z_2 = Rewriter::rewrite(n_len_eq_z_2);
    Assert(!n_len_eq_z_2.isConst());
    reqPhase[n_len_eq_z_2] = true;
  }
  else if (!case_empty.getConst<bool>())
  {
    // the rewriter knows that n is non-empty
    lems.push_back(case_nempty);
  }
  else
  {
    // If n = "" ---> true or len( n ) = 0 ----> true, then we expect that
    // n ---> "". Since this method is only called on non-constants n, it must
    // be that n = "" ^ len( n ) = 0 does not rewrite to true.
    Assert(false);
  }

  if (lems.empty())
  {
    return Node::null();
  }
  return lems.size() == 1 ? lems[0] : nm->mkNode(AND, lems);
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
    eq = Rewriter::rewrite(eq);
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
  return NodeManager::currentNM()->mkNode(n.getKind(), children);
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

void TermRegistry::inferSubstitutionProxyVars(Node n,
                                              std::vector<Node>& vars,
                                              std::vector<Node>& subs,
                                              std::vector<Node>& unproc) const
{
  if (n.getKind() == AND)
  {
    for (const Node& nc : n)
    {
      inferSubstitutionProxyVars(nc, vars, subs, unproc);
    }
    return;
  }
  if (n.getKind() == EQUAL)
  {
    Node ns = n.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
    ns = Rewriter::rewrite(ns);
    if (ns.getKind() == EQUAL)
    {
      Node s;
      Node v;
      for (unsigned i = 0; i < 2; i++)
      {
        Node ss;
        // determine whether this side has a proxy variable
        if (ns[i].getAttribute(StringsProxyVarAttribute()))
        {
          // it is a proxy variable
          ss = ns[i];
        }
        else if (ns[i].isConst())
        {
          ss = getProxyVariableFor(ns[i]);
        }
        if (!ss.isNull())
        {
          v = ns[1 - i];
          // if the other side is a constant or variable
          if (v.getNumChildren() == 0)
          {
            if (s.isNull())
            {
              s = ss;
            }
            else
            {
              // both sides of the equality correspond to a proxy variable
              if (ss == s)
              {
                // it is a trivial equality, e.g. between a proxy variable
                // and its definition
                return;
              }
              else
              {
                // equality between proxy variables, non-trivial
                s = Node::null();
              }
            }
          }
        }
      }
      if (!s.isNull())
      {
        // the equality can be turned into a substitution
        subs.push_back(s);
        vars.push_back(v);
        return;
      }
    }
    else
    {
      n = ns;
    }
  }
  if (!n.isConst() || !n.getConst<bool>())
  {
    unproc.push_back(n);
  }
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
