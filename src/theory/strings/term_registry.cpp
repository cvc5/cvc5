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

#include "theory/strings/word.h"
#include "smt/logic_exception.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/rewriter.h"
#include "expr/attribute.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

struct StringsProxyVarAttributeId {};
typedef expr::Attribute< StringsProxyVarAttributeId, bool > StringsProxyVarAttribute;

TermRegistry::TermRegistry(context::Context* c, context::UserContext* u, eq::EqualityEngine& ee,
                   OutputChannel& out,
                   SequencesStatistics& statistics)
    : d_ee(ee),
      d_out(out),
      d_statistics(statistics),
      d_functionsTerms(c),
      d_pregistered_terms_cache(u),
      d_registered_terms_cache(u),
      d_registeredTypesCache(u)
{
  
}

TermRegistry::~TermRegistry() {

}

void TermRegistry::preRegisterTerm(TNode n) {
  if( d_pregistered_terms_cache.find(n) != d_pregistered_terms_cache.end() ) {
    return;
  }
  d_pregistered_terms_cache.insert(n);
  Trace("strings-preregister")
      << "TheoryString::preregister : " << n << std::endl;
  //check for logic exceptions
  Kind k = n.getKind();
  if( !options::stringExp() ){
    if (k == STRING_STRIDOF || k == STRING_ITOS
        || k == STRING_STOI || k == STRING_STRREPL
        || k == STRING_STRREPLALL || k == STRING_STRCTN
        || k == STRING_LEQ || k == STRING_TOLOWER || k == STRING_TOUPPER
        || k == STRING_REV)
    {
      std::stringstream ss;
      ss << "Term of kind " << k
          << " not supported in default mode, try --strings-exp";
      throw LogicException(ss.str());
    }
  }
  switch (k)
  {
    case EQUAL: {
      d_equalityEngine.addTriggerEquality(n);
      break;
    }
    case STRING_IN_REGEXP: {
      d_out->requirePhase(
      d_equalityEngine.addTriggerPredicate(n);
      d_equalityEngine.addTerm(n[0]);
      d_equalityEngine.addTerm(n[1]);
      break;
    }
    default: {
      registerTerm(n, 0);
      TypeNode tn = n.getType();
      if (tn.isRegExp() && n.isVar())
      {
        std::stringstream ss;
        ss << "Regular expression variables are not supported.";
        throw LogicException(ss.str());
      }
      if( tn.isString() ) {
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
        d_equalityEngine.addTerm(n);
      } else if (tn.isBoolean()) {
        // Get triggered for both equal and dis-equal
        d_equalityEngine.addTriggerPredicate(n);
      } else {
        // Function applications/predicates
        d_equalityEngine.addTerm(n);
      }
      // Set d_functionsTerms stores all function applications that are
      // relevant to theory combination. Notice that this is a subset of
      // the applications whose kinds are function kinds in the equality
      // engine. This means it does not include applications of operators
      // like re.++, which is not a function kind in the equality engine.
      // Concatenation terms do not need to be considered here because
      // their arguments have string type and do not introduce any shared
      // terms.
      if (n.hasOperator() && d_equalityEngine.isFunctionKind(k)
          && k != STRING_CONCAT)
      {
        d_functionsTerms.push_back( n );
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
  if (d_registered_terms_cache.find(n) != d_registered_terms_cache.end())
  {
    return;
  }
  d_registered_terms_cache.insert(n);
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
    regTermLem = d_im.registerTerm(n);
  }
  else if (n.getKind() == STRING_TO_CODE)
  {
    d_has_str_code = true;
    // ite( str.len(s)==1, 0 <= str.code(s) < |A|, str.code(s)=-1 )
    Node code_len = utils::mkNLength(n[0]).eqNode(d_one);
    Node code_eq_neg1 = n.eqNode(d_neg_one);
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
  if (!regTermLem.isNull())
  {
    Trace("strings-lemma") << "Strings::Lemma REG-TERM : " << regTermLem
                           << std::endl;
    Trace("strings-assert") << "(assert " << regTermLem << ")" << std::endl;
    ++(d_statistics.d_lemmasRegisterTerm);
    d_out->lemma(regTermLem);
  }
}

void TermRegistry::registerType(TypeNode tn)
{
  if (d_registeredTypesCache.find(tn) != d_registeredTypesCache.end())
  {
    return;
  }
  d_registeredTypesCache.insert(tn);
  if (tn.isStringLike())
  {
    // preregister the empty word for the type
    Node emp = Word::mkEmptyWord(tn);
    if (!d_equalityEngine.hasTerm(emp))
    {
      preRegisterTerm(emp);
    }
  }
}


Node TermRegistry::registerTerm(Node n)
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

Node TermRegistry::getRegisterTermAtomicLemma(
    Node n, LengthStatus s, std::map<Node, bool>& reqPhase)
{
  NodeManager* nm = NodeManager::currentNM();
  Node n_len = nm->mkNode(kind::STRING_LENGTH, n);

  if (s == LENGTH_GEQ_ONE)
  {
    Node neq_empty = n.eqNode(d_emptyString).negate();
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
  Node n_len_eq_z_2 = n.eqNode(d_emptyString);
  Node case_empty = nm->mkNode(AND, n_len_eq_z, n_len_eq_z_2);
  case_empty = Rewriter::rewrite(case_empty);
  Node case_nempty = nm->mkNode(GT, n_len, d_zero);
  if (!case_empty.isConst())
  {
    Node lem = nm->mkNode(OR, case_empty, case_nempty);
    lems.push_back(lem);
    Trace("strings-lemma") << "Strings::Lemma LENGTH >= 0 : " << lem
                           << std::endl;
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
    Trace("strings-lemma") << "Strings::Lemma LENGTH > 0 (non-empty): "
                           << case_nempty << std::endl;
    lems.push_back(case_nempty);
  }
  else
  {
    // If n = "" ---> true or len( n ) = 0 ----> true, then we expect that
    // n ---> "". Since this method is only called on non-constants n, it must
    // be that n = "" ^ len( n ) = 0 does not rewrite to true.
    Assert(false);
  }

  // additionally add len( x ) >= 0 ?
  if (options::stringLenGeqZ())
  {
    Node n_len_geq = nm->mkNode(kind::GEQ, n_len, d_zero);
    n_len_geq = Rewriter::rewrite(n_len_geq);
    lems.push_back(n_len_geq);
  }

  if (lems.empty())
  {
    return Node::null();
  }
  return lems.size() == 1 ? lems[0] : nm->mkNode(AND, lems);
}

Node TermRegistry::getSymbolicDefinition(Node n,
                                             std::vector<Node>& exp) const
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

void TermRegistry::inferSubstitutionProxyVars(
    Node n,
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
  if (n != d_true)
  {
    unproc.push_back(n);
  }
}


}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
