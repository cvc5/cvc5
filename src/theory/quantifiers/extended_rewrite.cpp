/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of extended rewriting techniques.
 */

#include "theory/quantifiers/extended_rewrite.h"

#include <sstream>

#include "theory/arith/arith_msum.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/sequences_rewriter.h"
#include "theory/strings/word.h"
#include "theory/theory.h"

using namespace cvc5::internal::kind;
using namespace std;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

struct ExtRewriteAttributeId
{
};
typedef expr::Attribute<ExtRewriteAttributeId, Node> ExtRewriteAttribute;

struct ExtRewriteAggAttributeId
{
};
typedef expr::Attribute<ExtRewriteAggAttributeId, Node> ExtRewriteAggAttribute;

ExtendedRewriter::ExtendedRewriter(Rewriter& rew, bool aggr)
    : d_rew(rew), d_aggr(aggr)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_intZero = NodeManager::currentNM()->mkConstInt(Rational(0));
}

void ExtendedRewriter::setCache(Node n, Node ret) const
{
  if (d_aggr)
  {
    ExtRewriteAggAttribute erga;
    n.setAttribute(erga, ret);
  }
  else
  {
    ExtRewriteAttribute era;
    n.setAttribute(era, ret);
  }
}

Node ExtendedRewriter::getCache(Node n) const
{
  if (d_aggr)
  {
    if (n.hasAttribute(ExtRewriteAggAttribute()))
    {
      return n.getAttribute(ExtRewriteAggAttribute());
    }
  }
  else
  {
    if (n.hasAttribute(ExtRewriteAttribute()))
    {
      return n.getAttribute(ExtRewriteAttribute());
    }
  }
  return Node::null();
}

bool ExtendedRewriter::addToChildren(Node nc,
                                     std::vector<Node>& children,
                                     bool dropDup) const
{
  // If the operator is non-additive, do not consider duplicates
  if (dropDup
      && std::find(children.begin(), children.end(), nc) != children.end())
  {
    return false;
  }
  children.push_back(nc);
  return true;
}

Node ExtendedRewriter::extendedRewrite(Node n) const
{
  n = d_rew.rewrite(n);

  // has it already been computed?
  Node ncache = getCache(n);
  if (!ncache.isNull())
  {
    return ncache;
  }

  Node ret = n;
  NodeManager* nm = NodeManager::currentNM();

  //--------------------pre-rewrite
  if (d_aggr)
  {
    Node pre_new_ret;
    if (ret.getKind() == IMPLIES)
    {
      pre_new_ret = nm->mkNode(OR, ret[0].negate(), ret[1]);
      debugExtendedRewrite(ret, pre_new_ret, "IMPLIES elim");
    }
    else if (ret.getKind() == XOR)
    {
      pre_new_ret = nm->mkNode(EQUAL, ret[0].negate(), ret[1]);
      debugExtendedRewrite(ret, pre_new_ret, "XOR elim");
    }
    else if (ret.getKind() == NOT)
    {
      pre_new_ret = extendedRewriteNnf(ret);
      debugExtendedRewrite(ret, pre_new_ret, "NNF");
    }
    if (!pre_new_ret.isNull())
    {
      ret = extendedRewrite(pre_new_ret);

      Trace("q-ext-rewrite-debug")
          << "...ext-pre-rewrite : " << n << " -> " << pre_new_ret << std::endl;
      setCache(n, ret);
      return ret;
    }
  }
  //--------------------end pre-rewrite

  //--------------------rewrite children
  if (n.getNumChildren() > 0)
  {
    std::vector<Node> children;
    if (n.getMetaKind() == metakind::PARAMETERIZED)
    {
      children.push_back(n.getOperator());
    }
    Kind k = n.getKind();
    bool childChanged = false;
    bool isNonAdditive = TermUtil::isNonAdditive(k);
    // We flatten associative operators below, which requires k to be n-ary.
    bool isAssoc = TermUtil::isAssoc(k, true);
    for (unsigned i = 0; i < n.getNumChildren(); i++)
    {
      Node nc = extendedRewrite(n[i]);
      childChanged = nc != n[i] || childChanged;
      if (isAssoc && nc.getKind() == n.getKind())
      {
        for (const Node& ncc : nc)
        {
          if (!addToChildren(ncc, children, isNonAdditive))
          {
            childChanged = true;
          }
        }
      }
      else if (!addToChildren(nc, children, isNonAdditive))
      {
        childChanged = true;
      }
    }
    Assert(!children.empty());
    // Some commutative operators have rewriters that are agnostic to order,
    // thus, we sort here.
    if (TermUtil::isComm(k) && (d_aggr || children.size() <= 5))
    {
      childChanged = true;
      std::sort(children.begin(), children.end());
    }
    if (childChanged)
    {
      if (isNonAdditive && children.size() == 1)
      {
        // we may have subsumed children down to one
        ret = children[0];
      }
      else if (isAssoc
               && children.size() > kind::metakind::getMaxArityForKind(k))
      {
        Assert(kind::metakind::getMaxArityForKind(k) >= 2);
        // kind may require binary construction
        ret = children[0];
        for (unsigned i = 1, nchild = children.size(); i < nchild; i++)
        {
          ret = nm->mkNode(k, ret, children[i]);
        }
      }
      else
      {
        ret = nm->mkNode(k, children);
      }
    }
  }
  ret = d_rew.rewrite(ret);
  //--------------------end rewrite children

  // now, do extended rewrite
  Trace("q-ext-rewrite-debug") << "Do extended rewrite on : " << ret
                               << " (from " << n << ")" << std::endl;
  Node new_ret;

  //---------------------- theory-independent post-rewriting
  if (ret.getKind() == ITE)
  {
    new_ret = extendedRewriteIte(ITE, ret);
  }
  else if (ret.getKind() == AND || ret.getKind() == OR)
  {
    new_ret = extendedRewriteAndOr(ret);
  }
  else if (ret.getKind() == EQUAL)
  {
    new_ret = extendedRewriteEqChain(EQUAL, AND, OR, NOT, ret);
    debugExtendedRewrite(ret, new_ret, "Bool eq-chain simplify");
  }
  Assert(new_ret.isNull() || new_ret != ret);
  if (new_ret.isNull() && ret.getKind() != ITE)
  {
    // simple ITE pulling
    new_ret = extendedRewritePullIte(ITE, ret);
  }
  //----------------------end theory-independent post-rewriting

  //----------------------theory-specific post-rewriting
  if (new_ret.isNull())
  {
    TheoryId tid;
    if (ret.getKind() == ITE)
    {
      tid = Theory::theoryOf(ret.getType());
    }
    else
    {
      tid = Theory::theoryOf(ret);
    }
    Trace("q-ext-rewrite-debug") << "theoryOf( " << ret << " )= " << tid
                                 << std::endl;
    switch (tid)
    {
      case THEORY_STRINGS: new_ret = extendedRewriteStrings(ret); break;
      case THEORY_SETS: new_ret = extendedRewriteSets(ret); break;
      default: break;
    }
  }
  //----------------------end theory-specific post-rewriting

  //----------------------aggressive rewrites
  if (new_ret.isNull() && d_aggr)
  {
    new_ret = extendedRewriteAggr(ret);
  }
  //----------------------end aggressive rewrites

  setCache(n, ret);
  if (!new_ret.isNull())
  {
    ret = extendedRewrite(new_ret);
  }
  Trace("q-ext-rewrite-debug") << "...ext-rewrite : " << n << " -> " << ret
                               << std::endl;
  if (TraceIsOn("q-ext-rewrite-nf"))
  {
    if (n == ret)
    {
      Trace("q-ext-rewrite-nf") << "ext-rew normal form : " << n << std::endl;
    }
  }
  setCache(n, ret);
  return ret;
}

Node ExtendedRewriter::extendedRewriteAggr(Node n) const
{
  Node new_ret;
  Trace("q-ext-rewrite-debug2")
      << "Do aggressive rewrites on " << n << std::endl;
  bool polarity = n.getKind() != NOT;
  Node ret_atom = n.getKind() == NOT ? n[0] : n;
  if ((ret_atom.getKind() == EQUAL && ret_atom[0].getType().isRealOrInt())
      || ret_atom.getKind() == GEQ)
  {
    // ITE term removal in polynomials
    // e.g. ite( x=0, x, y ) = x+1 ---> ( x=0 ^ y = x+1 )
    Trace("q-ext-rewrite-debug2")
        << "Compute monomial sum " << ret_atom << std::endl;
    // compute monomial sum
    std::map<Node, Node> msum;
    if (ArithMSum::getMonomialSumLit(ret_atom, msum))
    {
      for (std::map<Node, Node>::iterator itm = msum.begin(); itm != msum.end();
           ++itm)
      {
        Node v = itm->first;
        Trace("q-ext-rewrite-debug2")
            << itm->first << " * " << itm->second << std::endl;
        if (v.getKind() == ITE)
        {
          Node veq;
          int res = ArithMSum::isolate(v, msum, veq, ret_atom.getKind());
          if (res != 0)
          {
            Trace("q-ext-rewrite-debug")
                << "  have ITE relation, solved form : " << veq << std::endl;
            // try pulling ITE
            new_ret = extendedRewritePullIte(ITE, veq);
            if (!new_ret.isNull())
            {
              if (!polarity)
              {
                new_ret = new_ret.negate();
              }
              break;
            }
          }
          else
          {
            Trace("q-ext-rewrite-debug")
                << "  failed to isolate " << v << " in " << n << std::endl;
          }
        }
      }
    }
    else
    {
      Trace("q-ext-rewrite-debug")
          << "  failed to get monomial sum of " << n << std::endl;
    }
  }
  // TODO (#1706) : conditional rewriting, condition merging
  return new_ret;
}

Node ExtendedRewriter::extendedRewriteIte(Kind itek, Node n, bool full) const
{
  Assert(n.getKind() == itek);
  Assert(n[1] != n[2]);

  NodeManager* nm = NodeManager::currentNM();

  Trace("ext-rew-ite") << "Rewrite ITE : " << n << std::endl;

  Node flip_cond;
  if (n[0].getKind() == NOT)
  {
    flip_cond = n[0][0];
  }
  else if (n[0].getKind() == OR)
  {
    // a | b ---> ~( ~a & ~b )
    flip_cond = TermUtil::simpleNegate(n[0]);
  }
  if (!flip_cond.isNull())
  {
    Node new_ret = nm->mkNode(ITE, flip_cond, n[2], n[1]);
    // only print debug trace if full=true
    if (full)
    {
      debugExtendedRewrite(n, new_ret, "ITE flip");
    }
    return new_ret;
  }
  // Boolean true/false return
  TypeNode tn = n.getType();
  if (tn.isBoolean())
  {
    for (unsigned i = 1; i <= 2; i++)
    {
      if (n[i].isConst())
      {
        Node cond = i == 1 ? n[0] : n[0].negate();
        Node other = n[i == 1 ? 2 : 1];
        Kind retk = AND;
        if (n[i].getConst<bool>())
        {
          retk = OR;
        }
        else
        {
          cond = cond.negate();
        }
        Node new_ret = nm->mkNode(retk, cond, other);
        if (full)
        {
          // ite( A, true, B ) ---> A V B
          // ite( A, false, B ) ---> ~A /\ B
          // ite( A, B,  true ) ---> ~A V B
          // ite( A, B, false ) ---> A /\ B
          debugExtendedRewrite(n, new_ret, "ITE const return");
        }
        return new_ret;
      }
    }
  }

  // get entailed equalities in the condition
  std::vector<Node> eq_conds;
  Kind ck = n[0].getKind();
  if (ck == EQUAL)
  {
    eq_conds.push_back(n[0]);
  }
  else if (ck == AND)
  {
    for (const Node& cn : n[0])
    {
      if (cn.getKind() == EQUAL)
      {
        eq_conds.push_back(cn);
      }
    }
  }

  Node new_ret;
  Node b;
  Node e;
  Node t1 = n[1];
  Node t2 = n[2];
  std::stringstream ss_reason;

  for (const Node& eq : eq_conds)
  {
    // simple invariant ITE
    for (unsigned i = 0; i <= 1; i++)
    {
      // ite( x = y ^ C, y, x ) ---> x
      // this is subsumed by the rewrites below
      if (t2 == eq[i] && t1 == eq[1 - i])
      {
        new_ret = t2;
        ss_reason << "ITE simple rev subs";
        break;
      }
    }
    if (!new_ret.isNull())
    {
      break;
    }
  }
  if (new_ret.isNull())
  {
    // merging branches
    for (unsigned i = 1; i <= 2; i++)
    {
      if (n[i].getKind() == ITE)
      {
        Node no = n[3 - i];
        for (unsigned j = 1; j <= 2; j++)
        {
          if (n[i][j] == no)
          {
            // e.g.
            // ite( C1, ite( C2, t1, t2 ), t1 ) ----> ite( C1 ^ ~C2, t2, t1 )
            Node nc1 = i == 2 ? n[0].negate() : n[0];
            Node nc2 = j == 1 ? n[i][0].negate() : n[i][0];
            Node new_cond = nm->mkNode(AND, nc1, nc2);
            new_ret = nm->mkNode(ITE, new_cond, n[i][3 - j], no);
            ss_reason << "ITE merge branch";
            break;
          }
        }
      }
      if (!new_ret.isNull())
      {
        break;
      }
    }
  }

  if (new_ret.isNull() && d_aggr)
  {
    // If x is less than t based on an ordering, then we use { x -> t } as a
    // substitution to the children of ite( x = t ^ C, s, t ) below.
    Subs subs;
    inferSubstitution(n[0], subs, true);

    if (!subs.empty())
    {
      // reverse substitution to opposite child
      // r{ x -> t } = s  implies  ite( x=t ^ C, s, r ) ---> r
      // We can use ordinary substitute since the result of the substitution
      // is not being returned. In other words, nn is only being used to query
      // whether the second branch is a generalization of the first.
      Node nn = subs.apply(t2);
      if (nn != t2)
      {
        nn = d_rew.rewrite(nn);
        if (nn == t1)
        {
          new_ret = t2;
          ss_reason << "ITE rev subs";
        }
      }

      // ite( x=t ^ C, s, r ) ---> ite( x=t ^ C, s{ x -> t }, r )
      // must use partial substitute here, to avoid substitution into witness
      std::map<Kind, bool> rkinds;
      nn = partialSubstitute(t1, subs, rkinds);
      nn = d_rew.rewrite(nn);
      if (nn != t1)
      {
        // If full=false, then we've duplicated a term u in the children of n.
        // For example, when ITE pulling, we have n is of the form:
        //   ite( C, f( u, t1 ), f( u, t2 ) )
        // We must show that at least one copy of u dissappears in this case.
        if (nn == t2)
        {
          new_ret = nn;
          ss_reason << "ITE subs invariant";
        }
        else if (full || nn.isConst())
        {
          new_ret = nm->mkNode(itek, n[0], nn, t2);
          ss_reason << "ITE subs";
        }
      }
    }
    if (new_ret.isNull())
    {
      // ite( C, t, s ) ----> ite( C, t, s { C -> false } )
      // use partial substitute to avoid substitution into witness
      std::map<Node, Node> assign;
      assign[n[0]] = d_false;
      std::map<Kind, bool> rkinds;
      Node nn = partialSubstitute(t2, assign, rkinds);
      if (nn != t2)
      {
        nn = d_rew.rewrite(nn);
        if (nn == t1)
        {
          new_ret = nn;
          ss_reason << "ITE subs invariant false";
        }
        else if (full || nn.isConst())
        {
          new_ret = nm->mkNode(itek, n[0], t1, nn);
          ss_reason << "ITE subs false";
        }
      }
    }
  }

  // only print debug trace if full=true
  if (!new_ret.isNull() && full)
  {
    debugExtendedRewrite(n, new_ret, ss_reason.str().c_str());
  }

  return new_ret;
}

Node ExtendedRewriter::extendedRewriteAndOr(Node n) const
{
  // all the below rewrites are aggressive
  if (!d_aggr)
  {
    return Node::null();
  }
  Node new_ret;
  // we allow substitutions to recurse over any kind, except WITNESS which is
  // managed by partialSubstitute.
  std::map<Kind, bool> bcp_kinds;
  new_ret = extendedRewriteBcp(AND, OR, NOT, bcp_kinds, n);
  if (!new_ret.isNull())
  {
    debugExtendedRewrite(n, new_ret, "Bool bcp");
    return new_ret;
  }
  // factoring
  new_ret = extendedRewriteFactoring(AND, OR, NOT, n);
  if (!new_ret.isNull())
  {
    debugExtendedRewrite(n, new_ret, "Bool factoring");
    return new_ret;
  }

  // equality resolution
  new_ret = extendedRewriteEqRes(AND, OR, EQUAL, NOT, bcp_kinds, n, false);
  debugExtendedRewrite(n, new_ret, "Bool eq res");
  return new_ret;
}

Node ExtendedRewriter::extendedRewritePullIte(Kind itek, Node n) const
{
  Assert(n.getKind() != ITE);
  if (n.isClosure())
  {
    // don't pull ITE out of quantifiers
    return n;
  }
  NodeManager* nm = NodeManager::currentNM();
  TypeNode tn = n.getType();
  std::vector<Node> children;
  bool hasOp = (n.getMetaKind() == metakind::PARAMETERIZED);
  if (hasOp)
  {
    children.push_back(n.getOperator());
  }
  unsigned nchildren = n.getNumChildren();
  for (unsigned i = 0; i < nchildren; i++)
  {
    children.push_back(n[i]);
  }
  std::map<unsigned, std::map<unsigned, Node> > ite_c;
  for (unsigned i = 0; i < nchildren; i++)
  {
    // these rewrites in this loop are currently classified as not aggressive,
    // although in previous versions they were classified as aggressive. These
    // are shown to help in some Kind2 problems.
    if (n[i].getKind() == itek)
    {
      unsigned ii = hasOp ? i + 1 : i;
      for (unsigned j = 0; j < 2; j++)
      {
        children[ii] = n[i][j + 1];
        Node pull = nm->mkNode(n.getKind(), children);
        Node pullr = d_rew.rewrite(pull);
        children[ii] = n[i];
        ite_c[i][j] = pullr;
      }
      if (ite_c[i][0] == ite_c[i][1])
      {
        // ITE dual invariance
        // f( t1..s1..tn ) ---> t  and  f( t1..s2..tn ) ---> t implies
        // f( t1..ite( A, s1, s2 )..tn ) ---> t
        debugExtendedRewrite(n, ite_c[i][0], "ITE dual invariant");
        return ite_c[i][0];
      }
      if (nchildren == 2 && (n[1 - i].isVar() || n[1 - i].isConst())
          && !n[1 - i].getType().isBoolean() && tn.isBoolean())
      {
        // always pull variable or constant with binary (theory) predicate
        // e.g. P( x, ite( A, t1, t2 ) ) ---> ite( A, P( x, t1 ), P( x, t2 ) )
        Node new_ret = nm->mkNode(ITE, n[i][0], ite_c[i][0], ite_c[i][1]);
        debugExtendedRewrite(n, new_ret, "ITE pull var predicate");
        return new_ret;
      }
      for (unsigned j = 0; j < 2; j++)
      {
        Node pullr = ite_c[i][j];
        if (pullr.isConst() || pullr == n[i][j + 1])
        {
          // ITE single child elimination
          // f( t1..s1..tn ) ---> t  where t is a constant or s1 itself
          // implies
          // f( t1..ite( A, s1, s2 )..tn ) ---> ite( A, t, f( t1..s2..tn ) )
          Node new_ret;
          if (tn.isBoolean() && pullr.isConst())
          {
            // remove false/true child immediately
            bool pol = pullr.getConst<bool>();
            std::vector<Node> new_children;
            new_children.push_back((j == 0) == pol ? n[i][0]
                                                    : n[i][0].negate());
            new_children.push_back(ite_c[i][1 - j]);
            new_ret = nm->mkNode(pol ? OR : AND, new_children);
            debugExtendedRewrite(n, new_ret, "ITE Bool single elim");
          }
          else
          {
            new_ret = nm->mkNode(itek, n[i][0], ite_c[i][0], ite_c[i][1]);
            debugExtendedRewrite(n, new_ret, "ITE single elim");
          }
          return new_ret;
        }
      }
    }
  }
  if (d_aggr)
  {
    for (std::pair<const unsigned, std::map<unsigned, Node> >& ip : ite_c)
    {
      Node nite = n[ip.first];
      Assert(nite.getKind() == itek);
      // now, simply pull the ITE and try ITE rewrites
      Node pull_ite = nm->mkNode(itek, nite[0], ip.second[0], ip.second[1]);
      pull_ite = d_rew.rewrite(pull_ite);
      if (pull_ite.getKind() == ITE)
      {
        Node new_pull_ite = extendedRewriteIte(itek, pull_ite, false);
        if (!new_pull_ite.isNull())
        {
          debugExtendedRewrite(n, new_pull_ite, "ITE pull rewrite");
          return new_pull_ite;
        }
      }
      else
      {
        // A general rewrite could eliminate the ITE by pulling.
        // An example is:
        //   ~( ite( C, ~x, ~ite( C, y, x ) ) ) --->
        //   ite( C, ~~x, ite( C, y, x ) ) --->
        //   x
        // where ~ is bitvector negation.
        debugExtendedRewrite(n, pull_ite, "ITE pull basic elim");
        return pull_ite;
      }
    }
  }

  return Node::null();
}

Node ExtendedRewriter::extendedRewriteNnf(Node ret) const
{
  Assert(ret.getKind() == NOT);

  Kind nk = ret[0].getKind();
  bool neg_ch = false;
  bool neg_ch_1 = false;
  if (nk == AND || nk == OR)
  {
    neg_ch = true;
    nk = nk == AND ? OR : AND;
  }
  else if (nk == IMPLIES)
  {
    neg_ch = true;
    neg_ch_1 = true;
    nk = AND;
  }
  else if (nk == ITE)
  {
    neg_ch = true;
    neg_ch_1 = true;
  }
  else if (nk == XOR)
  {
    nk = EQUAL;
  }
  else if (nk == EQUAL && ret[0][0].getType().isBoolean())
  {
    neg_ch_1 = true;
  }
  else
  {
    return Node::null();
  }

  std::vector<Node> new_children;
  for (unsigned i = 0, nchild = ret[0].getNumChildren(); i < nchild; i++)
  {
    Node c = ret[0][i];
    c = (i == 0 ? neg_ch_1 : false) != neg_ch ? c.negate() : c;
    new_children.push_back(c);
  }
  return NodeManager::currentNM()->mkNode(nk, new_children);
}

Node ExtendedRewriter::extendedRewriteBcp(Kind andk,
                                          Kind ork,
                                          Kind notk,
                                          std::map<Kind, bool>& bcp_kinds,
                                          Node ret) const
{
  Kind k = ret.getKind();
  Assert(k == andk || k == ork);
  Trace("ext-rew-bcp") << "BCP: **** INPUT: " << ret << std::endl;

  NodeManager* nm = NodeManager::currentNM();

  TypeNode tn = ret.getType();
  Node truen = TermUtil::mkTypeMaxValue(tn);
  Node falsen = TermUtil::mkTypeValue(tn, 0);

  // terms to process
  std::vector<Node> to_process;
  for (const Node& cn : ret)
  {
    to_process.push_back(cn);
  }
  // the processing terms
  std::vector<Node> clauses;
  // the terms we have propagated information to
  std::unordered_set<Node> prop_clauses;
  // the assignment
  std::map<Node, Node> assign;
  std::vector<Node> avars;
  std::vector<Node> asubs;

  Kind ok = k == andk ? ork : andk;
  // global polarity : when k=ork, everything is negated
  bool gpol = k == andk;

  do
  {
    // process the current nodes
    while (!to_process.empty())
    {
      std::vector<Node> new_to_process;
      for (const Node& cn : to_process)
      {
        Trace("ext-rew-bcp-debug") << "process " << cn << std::endl;
        Kind cnk = cn.getKind();
        bool pol = cnk != notk;
        Node cln = cnk == notk ? cn[0] : cn;
        Assert(cln.getKind() != notk);
        if ((pol && cln.getKind() == k) || (!pol && cln.getKind() == ok))
        {
          // flatten
          for (const Node& ccln : cln)
          {
            Node lccln = pol ? ccln : TermUtil::mkNegate(notk, ccln);
            new_to_process.push_back(lccln);
          }
        }
        else
        {
          // add it to the assignment
          Node val = gpol == pol ? truen : falsen;
          std::map<Node, Node>::iterator it = assign.find(cln);
          Trace("ext-rew-bcp") << "BCP: assign " << cln << " -> " << val
                               << std::endl;
          if (it != assign.end())
          {
            if (val != it->second)
            {
              Trace("ext-rew-bcp") << "BCP: conflict!" << std::endl;
              // a conflicting assignment: we are done
              return gpol ? falsen : truen;
            }
          }
          else
          {
            assign[cln] = val;
            avars.push_back(cln);
            asubs.push_back(val);
          }

          // also, treat it as clause if possible
          if (cln.getNumChildren() > 0
              && (bcp_kinds.empty()
                  || bcp_kinds.find(cln.getKind()) != bcp_kinds.end()))
          {
            if (std::find(clauses.begin(), clauses.end(), cn) == clauses.end()
                && prop_clauses.find(cn) == prop_clauses.end())
            {
              Trace("ext-rew-bcp") << "BCP: new clause: " << cn << std::endl;
              clauses.push_back(cn);
            }
          }
        }
      }
      to_process.clear();
      to_process.insert(
          to_process.end(), new_to_process.begin(), new_to_process.end());
    }

    // apply substitution to all subterms of clauses
    std::vector<Node> new_clauses;
    for (const Node& c : clauses)
    {
      bool cpol = c.getKind() != notk;
      Node ca = c.getKind() == notk ? c[0] : c;
      bool childChanged = false;
      std::vector<Node> ccs_children;
      for (const Node& cc : ca)
      {
        // always use partial substitute, to avoid substitution in witness
        Trace("ext-rew-bcp-debug") << "...do partial substitute" << std::endl;
        // substitution is only applicable to compatible kinds in bcp_kinds
        Node ccs = partialSubstitute(cc, assign, bcp_kinds);
        childChanged = childChanged || ccs != cc;
        ccs_children.push_back(ccs);
      }
      if (childChanged)
      {
        if (ca.getMetaKind() == metakind::PARAMETERIZED)
        {
          ccs_children.insert(ccs_children.begin(), ca.getOperator());
        }
        Node ccs = nm->mkNode(ca.getKind(), ccs_children);
        ccs = cpol ? ccs : TermUtil::mkNegate(notk, ccs);
        Trace("ext-rew-bcp") << "BCP: propagated " << c << " -> " << ccs
                             << std::endl;
        ccs = d_rew.rewrite(ccs);
        Trace("ext-rew-bcp") << "BCP: rewritten to " << ccs << std::endl;
        to_process.push_back(ccs);
        // store this as a node that propagation touched. This marks c so that
        // it will not be included in the final construction.
        prop_clauses.insert(ca);
      }
      else
      {
        new_clauses.push_back(c);
      }
    }
    clauses.clear();
    clauses.insert(clauses.end(), new_clauses.begin(), new_clauses.end());
  } while (!to_process.empty());

  // remake the node
  if (!prop_clauses.empty())
  {
    std::vector<Node> children;
    for (std::pair<const Node, Node>& l : assign)
    {
      Node a = l.first;
      // if propagation did not touch a
      if (prop_clauses.find(a) == prop_clauses.end())
      {
        Assert(l.second == truen || l.second == falsen);
        Node ln = (l.second == truen) == gpol ? a : TermUtil::mkNegate(notk, a);
        children.push_back(ln);
      }
    }
    Node new_ret = children.size() == 1 ? children[0] : nm->mkNode(k, children);
    Trace("ext-rew-bcp") << "BCP: **** OUTPUT: " << new_ret << std::endl;
    return new_ret;
  }

  return Node::null();
}

Node ExtendedRewriter::extendedRewriteFactoring(Kind andk,
                                                Kind ork,
                                                Kind notk,
                                                Node n) const
{
  Trace("ext-rew-factoring") << "Factoring: *** INPUT: " << n << std::endl;
  NodeManager* nm = NodeManager::currentNM();

  Kind nk = n.getKind();
  Assert(nk == andk || nk == ork);
  Kind onk = nk == andk ? ork : andk;
  // count the number of times atoms occur
  std::map<Node, std::vector<Node> > lit_to_cl;
  std::map<Node, std::vector<Node> > cl_to_lits;
  for (const Node& nc : n)
  {
    Kind nck = nc.getKind();
    if (nck == onk)
    {
      for (const Node& ncl : nc)
      {
        if (std::find(lit_to_cl[ncl].begin(), lit_to_cl[ncl].end(), nc)
            == lit_to_cl[ncl].end())
        {
          lit_to_cl[ncl].push_back(nc);
          cl_to_lits[nc].push_back(ncl);
        }
      }
    }
    else
    {
      lit_to_cl[nc].push_back(nc);
      cl_to_lits[nc].push_back(nc);
    }
  }
  // get the maximum shared literal to factor
  unsigned max_size = 0;
  Node flit;
  for (const std::pair<const Node, std::vector<Node> >& ltc : lit_to_cl)
  {
    if (ltc.second.size() > max_size)
    {
      max_size = ltc.second.size();
      flit = ltc.first;
    }
  }
  if (max_size > 1)
  {
    // do the factoring
    std::vector<Node> children;
    std::vector<Node> fchildren;
    std::map<Node, std::vector<Node> >::iterator itl = lit_to_cl.find(flit);
    std::vector<Node>& cls = itl->second;
    for (const Node& nc : n)
    {
      if (std::find(cls.begin(), cls.end(), nc) == cls.end())
      {
        children.push_back(nc);
      }
      else
      {
        // rebuild
        std::vector<Node>& lits = cl_to_lits[nc];
        std::vector<Node>::iterator itlfl =
            std::find(lits.begin(), lits.end(), flit);
        Assert(itlfl != lits.end());
        lits.erase(itlfl);
        // rebuild
        if (!lits.empty())
        {
          Node new_cl = lits.size() == 1 ? lits[0] : nm->mkNode(onk, lits);
          fchildren.push_back(new_cl);
        }
      }
    }
    // rebuild the factored children
    Assert(!fchildren.empty());
    Node fcn = fchildren.size() == 1 ? fchildren[0] : nm->mkNode(nk, fchildren);
    children.push_back(nm->mkNode(onk, flit, fcn));
    Node ret = children.size() == 1 ? children[0] : nm->mkNode(nk, children);
    Trace("ext-rew-factoring") << "Factoring: *** OUTPUT: " << ret << std::endl;
    return ret;
  }
  else
  {
    Trace("ext-rew-factoring") << "Factoring: no change" << std::endl;
  }
  return Node::null();
}

Node ExtendedRewriter::extendedRewriteEqRes(Kind andk,
                                            Kind ork,
                                            Kind eqk,
                                            Kind notk,
                                            std::map<Kind, bool>& bcp_kinds,
                                            Node n,
                                            bool isXor) const
{
  Assert(n.getKind() == andk || n.getKind() == ork);
  Trace("ext-rew-eqres") << "Eq res: **** INPUT: " << n << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  Kind nk = n.getKind();
  bool gpol = (nk == andk);
  for (unsigned i = 0, nchild = n.getNumChildren(); i < nchild; i++)
  {
    Node lit = n[i];
    if (lit.getKind() == eqk)
    {
      // eq is the equality we are basing a substitution on
      Node eq;
      if (gpol == isXor)
      {
        // can only turn disequality into equality if types are the same
        if (lit[1].getType() == lit.getType())
        {
          // t != s ---> ~t = s
          if (lit[1].getKind() == notk && lit[0].getKind() != notk)
          {
            eq = nm->mkNode(EQUAL, lit[0], TermUtil::mkNegate(notk, lit[1]));
          }
          else
          {
            eq = nm->mkNode(EQUAL, TermUtil::mkNegate(notk, lit[0]), lit[1]);
          }
        }
      }
      else
      {
        eq = eqk == EQUAL ? lit : nm->mkNode(EQUAL, lit[0], lit[1]);
      }
      if (!eq.isNull())
      {
        // see if it corresponds to a substitution
        Subs subs;
        if (inferSubstitution(eq, subs))
        {
          Assert(subs.size() == 1);
          std::vector<Node> children;
          bool childrenChanged = false;
          // apply to all other children
          for (unsigned j = 0; j < nchild; j++)
          {
            Node ccs = n[j];
            if (i != j)
            {
              // Substitution is only applicable to compatible kinds. We always
              // use the partialSubstitute method to avoid substitution into
              // witness terms.
              ccs = partialSubstitute(ccs, subs, bcp_kinds);
              childrenChanged = childrenChanged || n[j] != ccs;
            }
            children.push_back(ccs);
          }
          if (childrenChanged)
          {
            return nm->mkNode(nk, children);
          }
        }
      }
    }
  }

  return Node::null();
}

/** sort pairs by their second (unsigned) argument */
static bool sortPairSecond(const std::pair<Node, unsigned>& a,
                           const std::pair<Node, unsigned>& b)
{
  return (a.second < b.second);
}

/** A simple subsumption trie used to compute pairwise list subsets */
class SimpSubsumeTrie
{
 public:
  /** the children of this node */
  std::map<Node, SimpSubsumeTrie> d_children;
  /** the term at this node */
  Node d_data;
  /** add term to the trie
   *
   * This adds term c to this trie, whose atom list is alist. This adds terms
   * s to subsumes such that the atom list of s is a subset of the atom list
   * of c. For example, say:
   *   c1.alist = { A }
   *   c2.alist = { C }
   *   c3.alist = { B, C }
   *   c4.alist = { A, B, D }
   *   c5.alist = { A, B, C }
   * If these terms are added in the order c1, c2, c3, c4, c5, then:
   *   addTerm c1 results in subsumes = {}
   *   addTerm c2 results in subsumes = {}
   *   addTerm c3 results in subsumes = { c2 }
   *   addTerm c4 results in subsumes = { c1 }
   *   addTerm c5 results in subsumes = { c1, c2, c3 }
   * Notice that the intended use case of this trie is to add term t before t'
   * only when size( t.alist ) <= size( t'.alist ).
   *
   * The last two arguments describe the state of the path [t0...tn] we
   * have followed in the trie during the recursive call.
   * If doAdd = true,
   *   then n+1 = index and alist[1]...alist[n] = t1...tn. If index=alist.size()
   *   we add c as the current node of this trie.
   * If doAdd = false,
   *   then t1...tn occur in alist.
   */
  void addTerm(Node c,
               std::vector<Node>& alist,
               std::vector<Node>& subsumes,
               unsigned index = 0,
               bool doAdd = true)
  {
    if (!d_data.isNull())
    {
      subsumes.push_back(d_data);
    }
    if (doAdd)
    {
      if (index == alist.size())
      {
        d_data = c;
        return;
      }
    }
    // try all children where we have this atom
    for (std::pair<const Node, SimpSubsumeTrie>& cp : d_children)
    {
      if (std::find(alist.begin(), alist.end(), cp.first) != alist.end())
      {
        cp.second.addTerm(c, alist, subsumes, 0, false);
      }
    }
    if (doAdd)
    {
      d_children[alist[index]].addTerm(c, alist, subsumes, index + 1, doAdd);
    }
  }
};

Node ExtendedRewriter::extendedRewriteEqChain(
    Kind eqk, Kind andk, Kind ork, Kind notk, Node ret, bool isXor) const
{
  Assert(ret.getKind() == eqk);

  // this rewrite is aggressive; it in fact has the precondition that other
  // aggressive rewrites (including BCP) have been applied.
  if (!d_aggr)
  {
    return Node::null();
  }

  NodeManager* nm = NodeManager::currentNM();

  TypeNode tn = ret[0].getType();

  // sort/cancelling for Boolean EQUAL/XOR-chains
  Trace("ext-rew-eqchain") << "Eq-Chain : " << ret << std::endl;

  // get the children on either side
  bool gpol = true;
  std::vector<Node> children;
  for (unsigned r = 0, size = ret.getNumChildren(); r < size; r++)
  {
    Node curr = ret[r];
    // assume, if necessary, right associative
    while (curr.getKind() == eqk && curr[0].getType() == tn)
    {
      children.push_back(curr[0]);
      curr = curr[1];
    }
    children.push_back(curr);
  }

  std::map<Node, bool> cstatus;
  // add children to status
  for (const Node& c : children)
  {
    Node a = c;
    if (a.getKind() == notk)
    {
      gpol = !gpol;
      a = a[0];
    }
    Trace("ext-rew-eqchain") << "...child : " << a << std::endl;
    std::map<Node, bool>::iterator itc = cstatus.find(a);
    if (itc == cstatus.end())
    {
      cstatus[a] = true;
    }
    else
    {
      // cancels
      cstatus.erase(a);
      if (isXor)
      {
        gpol = !gpol;
      }
    }
  }
  Trace("ext-rew-eqchain") << "Global polarity : " << gpol << std::endl;

  if (cstatus.empty())
  {
    return TermUtil::mkTypeConst(ret.getType(), gpol);
  }

  children.clear();

  // compute the atoms of each child
  Trace("ext-rew-eqchain") << "eqchain-simplify: begin\n";
  Trace("ext-rew-eqchain") << "  eqchain-simplify: get atoms...\n";
  std::map<Node, std::map<Node, bool> > atoms;
  std::map<Node, std::vector<Node> > alist;
  std::vector<std::pair<Node, unsigned> > atom_count;
  for (std::pair<const Node, bool>& cp : cstatus)
  {
    if (!cp.second)
    {
      // already eliminated
      continue;
    }
    Node c = cp.first;
    Kind ck = c.getKind();
    Trace("ext-rew-eqchain") << "  process c = " << c << std::endl;
    if (ck == andk || ck == ork)
    {
      for (unsigned j = 0, nchild = c.getNumChildren(); j < nchild; j++)
      {
        Node cl = c[j];
        bool pol = cl.getKind() != notk;
        Node ca = pol ? cl : cl[0];
        bool newVal = (ck == andk ? !pol : pol);
        Trace("ext-rew-eqchain")
            << "  atoms(" << c << ", " << ca << ") = " << newVal << std::endl;
        Assert(atoms[c].find(ca) == atoms[c].end());
        // polarity is flipped when we are AND
        atoms[c][ca] = newVal;
        alist[c].push_back(ca);

        // if this already exists as a child of the equality chain, eliminate.
        // this catches cases like ( x & y ) = ( ( x & y ) | z ), where we
        // consider ( x & y ) a unit, whereas below it is expanded to
        // ~( ~x | ~y ).
        std::map<Node, bool>::iterator itc = cstatus.find(ca);
        if (itc != cstatus.end() && itc->second)
        {
          // cancel it
          cstatus[ca] = false;
          cstatus[c] = false;
          // make new child
          // x = ( y | ~x ) ---> y & x
          // x = ( y | x ) ---> ~y | x
          // x = ( y & x ) ---> y | ~x
          // x = ( y & ~x ) ---> ~y & ~x
          std::vector<Node> new_children;
          for (unsigned k = 0, nchildc = c.getNumChildren(); k < nchildc; k++)
          {
            if (j != k)
            {
              new_children.push_back(c[k]);
            }
          }
          Node nc[2];
          nc[0] = c[j];
          nc[1] = new_children.size() == 1 ? new_children[0]
                                           : nm->mkNode(ck, new_children);
          // negate the proper child
          unsigned nindex = (ck == andk) == pol ? 0 : 1;
          nc[nindex] = TermUtil::mkNegate(notk, nc[nindex]);
          Kind nk = pol ? ork : andk;
          // store as new child
          children.push_back(nm->mkNode(nk, nc[0], nc[1]));
          if (isXor)
          {
            gpol = !gpol;
          }
          break;
        }
      }
    }
    else
    {
      bool pol = ck != notk;
      Node ca = pol ? c : c[0];
      atoms[c][ca] = pol;
      Trace("ext-rew-eqchain")
          << "  atoms(" << c << ", " << ca << ") = " << pol << std::endl;
      alist[c].push_back(ca);
    }
    atom_count.push_back(std::pair<Node, unsigned>(c, alist[c].size()));
  }
  // sort the atoms in each atom list
  for (std::map<Node, std::vector<Node> >::iterator it = alist.begin();
       it != alist.end();
       ++it)
  {
    std::sort(it->second.begin(), it->second.end());
  }
  // check subsumptions
  // sort by #atoms
  std::sort(atom_count.begin(), atom_count.end(), sortPairSecond);
  if (TraceIsOn("ext-rew-eqchain"))
  {
    for (const std::pair<Node, unsigned>& ac : atom_count)
    {
      Trace("ext-rew-eqchain") << "  eqchain-simplify: " << ac.first << " has "
                               << ac.second << " atoms." << std::endl;
    }
    Trace("ext-rew-eqchain") << "  eqchain-simplify: compute subsumptions...\n";
  }
  SimpSubsumeTrie sst;
  for (std::pair<const Node, bool>& cp : cstatus)
  {
    if (!cp.second)
    {
      // already eliminated
      continue;
    }
    Node c = cp.first;
    std::map<Node, std::map<Node, bool> >::iterator itc = atoms.find(c);
    Assert(itc != atoms.end());
    Trace("ext-rew-eqchain") << "  - add term " << c << " with atom list "
                             << alist[c] << "...\n";
    std::vector<Node> subsumes;
    sst.addTerm(c, alist[c], subsumes);
    for (const Node& cc : subsumes)
    {
      if (!cstatus[cc])
      {
        // subsumes a child that was already eliminated
        continue;
      }
      Trace("ext-rew-eqchain") << "  eqchain-simplify: " << c << " subsumes "
                               << cc << std::endl;
      // for each of the atoms in cc
      std::map<Node, std::map<Node, bool> >::iterator itcc = atoms.find(cc);
      Assert(itcc != atoms.end());
      std::vector<Node> common_children;
      std::vector<Node> diff_children;
      for (const std::pair<const Node, bool>& ap : itcc->second)
      {
        // compare the polarity
        Node a = ap.first;
        bool polcc = ap.second;
        Assert(itc->second.find(a) != itc->second.end());
        bool polc = itc->second[a];
        Trace("ext-rew-eqchain") << "    eqchain-simplify: atom " << a
                                 << " has polarities : " << polc << " " << polcc
                                 << "\n";
        Node lit = polc ? a : TermUtil::mkNegate(notk, a);
        if (polc != polcc)
        {
          diff_children.push_back(lit);
        }
        else
        {
          common_children.push_back(lit);
        }
      }
      std::vector<Node> rem_children;
      for (const std::pair<const Node, bool>& ap : itc->second)
      {
        Node a = ap.first;
        if (atoms[cc].find(a) == atoms[cc].end())
        {
          bool polc = ap.second;
          rem_children.push_back(polc ? a : TermUtil::mkNegate(notk, a));
        }
      }
      Trace("ext-rew-eqchain")
          << "    #common/diff/rem: " << common_children.size() << "/"
          << diff_children.size() << "/" << rem_children.size() << "\n";
      bool do_rewrite = false;
      if (common_children.empty() && itc->second.size() == itcc->second.size()
          && itcc->second.size() == 2)
      {
        // x | y = ~x | ~y ---> ~( x = y )
        do_rewrite = true;
        children.push_back(diff_children[0]);
        children.push_back(diff_children[1]);
        gpol = !gpol;
        Trace("ext-rew-eqchain") << "    apply 2-child all-diff\n";
      }
      else if (common_children.empty() && diff_children.size() == 1)
      {
        do_rewrite = true;
        // x = ( ~x | y ) ---> ~( ~x | ~y )
        Node remn = rem_children.size() == 1 ? rem_children[0]
                                             : nm->mkNode(ork, rem_children);
        remn = TermUtil::mkNegate(notk, remn);
        children.push_back(nm->mkNode(ork, diff_children[0], remn));
        if (!isXor)
        {
          gpol = !gpol;
        }
        Trace("ext-rew-eqchain") << "    apply unit resolution\n";
      }
      else if (diff_children.size() == 1
               && itc->second.size() == itcc->second.size())
      {
        // ( x | y | z ) = ( x | ~y | z ) ---> ( x | z )
        do_rewrite = true;
        Assert(!common_children.empty());
        Node comn = common_children.size() == 1
                        ? common_children[0]
                        : nm->mkNode(ork, common_children);
        children.push_back(comn);
        if (isXor)
        {
          gpol = !gpol;
        }
        Trace("ext-rew-eqchain") << "    apply resolution\n";
      }
      else if (diff_children.empty())
      {
        do_rewrite = true;
        if (rem_children.empty())
        {
          // x | y = x | y ---> true
          // this can happen if we have ( ~x & ~y ) = ( x | y )
          children.push_back(TermUtil::mkTypeMaxValue(tn));
          if (isXor)
          {
            gpol = !gpol;
          }
          Trace("ext-rew-eqchain") << "    apply cancel\n";
        }
        else
        {
          // x | y = ( x | y | z ) ---> ( x | y | ~z )
          Node remn = rem_children.size() == 1 ? rem_children[0]
                                               : nm->mkNode(ork, rem_children);
          remn = TermUtil::mkNegate(notk, remn);
          Node comn = common_children.size() == 1
                          ? common_children[0]
                          : nm->mkNode(ork, common_children);
          children.push_back(nm->mkNode(ork, comn, remn));
          if (isXor)
          {
            gpol = !gpol;
          }
          Trace("ext-rew-eqchain") << "    apply subsume\n";
        }
      }
      if (do_rewrite)
      {
        // eliminate the children, reverse polarity as needed
        for (unsigned r = 0; r < 2; r++)
        {
          Node c_rem = r == 0 ? c : cc;
          cstatus[c_rem] = false;
          if (c_rem.getKind() == andk)
          {
            gpol = !gpol;
          }
        }
        break;
      }
    }
  }
  Trace("ext-rew-eqchain") << "eqchain-simplify: finish" << std::endl;

  // sorted right associative chain
  bool has_nvar = false;
  unsigned nvar_index = 0;
  for (std::pair<const Node, bool>& cp : cstatus)
  {
    if (cp.second)
    {
      if (!cp.first.isVar())
      {
        has_nvar = true;
        nvar_index = children.size();
      }
      children.push_back(cp.first);
    }
  }
  std::sort(children.begin(), children.end());

  Node new_ret;
  if (!gpol)
  {
    // negate the constant child if it exists
    unsigned nindex = has_nvar ? nvar_index : 0;
    children[nindex] = TermUtil::mkNegate(notk, children[nindex]);
  }
  new_ret = children.back();
  unsigned index = children.size() - 1;
  while (index > 0)
  {
    index--;
    new_ret = nm->mkNode(eqk, children[index], new_ret);
  }
  new_ret = d_rew.rewrite(new_ret);
  if (new_ret != ret)
  {
    return new_ret;
  }
  return Node::null();
}

Node ExtendedRewriter::partialSubstitute(
    Node n,
    const std::map<Node, Node>& assign,
    const std::map<Kind, bool>& rkinds) const
{
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::map<Node, Node>::const_iterator ita;
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
      ita = assign.find(cur);
      if (ita != assign.end())
      {
        visited[cur] = ita->second;
      }
      else
      {
        // If rkinds is non-empty, then can only recurse on its kinds.
        // We also always disallow substitution into witness. Notice that
        // we disallow witness here, due to unsoundness when applying contextual
        // substitutions over witness terms (see #4620).
        Kind k = cur.getKind();
        if (k != WITNESS && (rkinds.empty() || rkinds.find(k) != rkinds.end()))
        {
          visited[cur] = Node::null();
          visit.push_back(cur);
          for (const Node& cn : cur)
          {
            visit.push_back(cn);
          }
        }
        else
        {
          visited[cur] = cur;
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = NodeManager::currentNM()->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node ExtendedRewriter::partialSubstitute(
    Node n, const Subs& subs, const std::map<Kind, bool>& rkinds) const
{
  std::map<Node, Node> assign;
  for (size_t i = 0, nvars = subs.size(); i < nvars; i++)
  {
    assign[subs.d_vars[i]] = subs.d_subs[i];
  }
  return partialSubstitute(n, assign, rkinds);
}

Node ExtendedRewriter::solveEquality(Node n) const
{
  // TODO (#1706) : implement
  Assert(n.getKind() == EQUAL);

  return Node::null();
}

bool ExtendedRewriter::inferSubstitution(Node n, Subs& subs, bool usePred) const
{
  if (n.getKind() == AND)
  {
    bool ret = false;
    for (const Node& nc : n)
    {
      bool cret = inferSubstitution(nc, subs, usePred);
      ret = ret || cret;
    }
    return ret;
  }
  if (n.getKind() == EQUAL)
  {
    // see if it can be put into form x = y
    Node slv_eq = solveEquality(n);
    if (!slv_eq.isNull())
    {
      n = slv_eq;
    }
    Node v[2];
    for (unsigned i = 0; i < 2; i++)
    {
      if (n[i].isConst())
      {
        subs.add(n[1 - i], n[i]);
        return true;
      }
      if (n[i].isVar())
      {
        v[i] = n[i];
      }
      else if (TermUtil::isNegate(n[i].getKind()) && n[i][0].isVar())
      {
        v[i] = n[i][0];
      }
    }
    for (unsigned i = 0; i < 2; i++)
    {
      TNode r1 = v[i];
      Node r2 = v[1 - i];
      if (r1.isVar() && ((r2.isVar() && r1 < r2) || r2.isConst()))
      {
        r2 = n[1 - i];
        if (v[i] != n[i])
        {
          Assert(TermUtil::isNegate(n[i].getKind()));
          r2 = TermUtil::mkNegate(n[i].getKind(), r2);
        }
        if (!subs.contains(r1))
        {
          subs.add(r1, r2);
          return true;
        }
      }
    }
  }
  if (usePred)
  {
    bool negated = n.getKind() == NOT;
    Node var = negated ? n[0] : n;
    Node s = NodeManager::currentNM()->mkConst(!negated);
    subs.add(var, s);
    return true;
  }
  return false;
}

Node ExtendedRewriter::extendedRewriteStrings(const Node& node) const
{
  Trace("q-ext-rewrite-debug")
      << "Extended rewrite strings : " << node << std::endl;

  Kind k = node.getKind();
  if (k == EQUAL)
  {
    strings::SequencesRewriter sr(&d_rew, nullptr);
    return sr.rewriteEqualityExt(node);
  }
  else if (k == STRING_SUBSTR)
  {
    NodeManager* nm = NodeManager::currentNM();
    Node tot_len = d_rew.rewrite(nm->mkNode(STRING_LENGTH, node[0]));
    strings::ArithEntail aent(&d_rew);
    // (str.substr s x y) --> "" if x < len(s) |= 0 >= y
    Node n1_lt_tot_len = d_rew.rewrite(nm->mkNode(LT, node[1], tot_len));
    if (aent.checkWithAssumption(n1_lt_tot_len, d_intZero, node[2], false))
    {
      Node ret = strings::Word::mkEmptyWord(node.getType());
      debugExtendedRewrite(node, ret, "SS_START_ENTAILS_ZERO_LEN");
      return ret;
    }

    // (str.substr s x y) --> "" if 0 < y |= x >= str.len(s)
    Node non_zero_len = d_rew.rewrite(nm->mkNode(LT, d_intZero, node[2]));
    if (aent.checkWithAssumption(non_zero_len, node[1], tot_len, false))
    {
      Node ret = strings::Word::mkEmptyWord(node.getType());
      debugExtendedRewrite(node, ret, "SS_NON_ZERO_LEN_ENTAILS_OOB");
      return ret;
    }
    // (str.substr s x y) --> "" if x >= 0 |= 0 >= str.len(s)
    Node geq_zero_start = d_rew.rewrite(nm->mkNode(GEQ, node[1], d_intZero));
    if (aent.checkWithAssumption(geq_zero_start, d_intZero, tot_len, false))
    {
      Node ret = strings::Word::mkEmptyWord(node.getType());
      debugExtendedRewrite(node, ret, "SS_GEQ_ZERO_START_ENTAILS_EMP_S");
      return ret;
    }
  }

  return Node::null();
}

Node ExtendedRewriter::extendedRewriteSets(const Node& node) const
{
  if (node.getKind() == SET_MINUS && node[1].getKind() == SET_MINUS
      && node[1][0] == node[0])
  {
    // Note this cannot be a rewrite rule or a ppRewrite, since it impacts the
    // cardinality graph. In particular, if we internally inspect (set.minus A
    // (setminus A B)), for instance if we are splitting the Venn regions of A
    // and (set.minus A B), then we should not transform this to an intersection
    // term. (set.minus A (set.minus A B)) = (set.inter A B)
    NodeManager* nm = NodeManager::currentNM();
    Node ret = nm->mkNode(SET_INTER, node[0], node[1][1]);
    debugExtendedRewrite(node, ret, "SET_MINUS_MINUS");
    return ret;
  }
  return Node::null();
}

void ExtendedRewriter::debugExtendedRewrite(Node n,
                                            Node ret,
                                            const char* c) const
{
  Assert(ret.isNull() || n.getType().isComparableTo(ret.getType()))
      << "Extended rewrite does not preserve type: " << n << " --> " << ret;
  if (TraceIsOn("q-ext-rewrite"))
  {
    if (!ret.isNull())
    {
      Trace("q-ext-rewrite-apply") << "sygus-extr : apply " << c << std::endl;
      Trace("q-ext-rewrite") << "sygus-extr : " << c << " : " << n
                             << " rewrites to " << ret << std::endl;
    }
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
