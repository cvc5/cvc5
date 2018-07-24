/*********************                                                        */
/*! \file extended_rewrite.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of extended rewriting techniques
 **/

#include "theory/quantifiers/extended_rewrite.h"

#include "options/quantifiers_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

struct ExtRewriteAttributeId
{
};
typedef expr::Attribute<ExtRewriteAttributeId, Node> ExtRewriteAttribute;

ExtendedRewriter::ExtendedRewriter(bool aggr) : d_aggr(aggr)
{
}

void ExtendedRewriter::setCache(Node n, Node ret)
{
  ExtRewriteAttribute era;
  n.setAttribute(era, ret);
}

bool ExtendedRewriter::addToChildren(Node nc,
                                     std::vector<Node>& children,
                                     bool dropDup)
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

Node ExtendedRewriter::extendedRewrite(Node n)
{
  n = Rewriter::rewrite(n);
  if (!options::sygusExtRew())
  {
    return n;
  }

  // has it already been computed?
  if (n.hasAttribute(ExtRewriteAttribute()))
  {
    return n.getAttribute(ExtRewriteAttribute());
  }

  Node ret = n;
  NodeManager* nm = NodeManager::currentNM();

  //--------------------pre-rewrite
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

    Trace("q-ext-rewrite-debug") << "...ext-pre-rewrite : " << n << " -> "
                                 << pre_new_ret << std::endl;
    setCache(n, ret);
    return ret;
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
    bool isAssoc = TermUtil::isAssoc(k);
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
      else
      {
        ret = nm->mkNode(k, children);
      }
    }
  }
  ret = Rewriter::rewrite(ret);
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
    Trace("q-ext-rewrite-debug")
        << "theoryOf( " << ret << " )= " << tid << std::endl;
    if (tid == THEORY_ARITH)
    {
      new_ret = extendedRewriteArith(ret);
    }
    else if (tid == THEORY_BV)
    {
      new_ret = extendedRewriteBv(ret);
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
  setCache(n, ret);
  return ret;
}

Node ExtendedRewriter::extendedRewriteAggr(Node n)
{
  Node new_ret;
  Trace("q-ext-rewrite-debug2")
      << "Do aggressive rewrites on " << n << std::endl;
  bool polarity = n.getKind() != NOT;
  Node ret_atom = n.getKind() == NOT ? n[0] : n;
  if ((ret_atom.getKind() == EQUAL && ret_atom[0].getType().isReal())
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

Node ExtendedRewriter::extendedRewriteIte(Kind itek, Node n, bool full)
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

  if (new_ret.isNull() && d_aggr)
  {
    // If x is less than t based on an ordering, then we use { x -> t } as a
    // substitution to the children of ite( x = t ^ C, s, t ) below.
    std::vector<Node> vars;
    std::vector<Node> subs;
    for (const Node& eq : eq_conds)
    {
      inferSubstitution(eq, vars, subs);
    }

    if (!vars.empty())
    {
      // reverse substitution to opposite child
      // r{ x -> t } = s  implies  ite( x=t ^ C, s, r ) ---> r
      Node nn =
          t2.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      if (nn != t2)
      {
        nn = Rewriter::rewrite(nn);
        if (nn == t1)
        {
          new_ret = t2;
          ss_reason << "ITE rev subs";
        }
      }

      // ite( x=t ^ C, s, r ) ---> ite( x=t ^ C, s{ x -> t }, r )
      nn = t1.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      if (nn != t1)
      {
        // If full=false, then we've duplicated a term u in the children of n.
        // For example, when ITE pulling, we have n is of the form:
        //   ite( C, f( u, t1 ), f( u, t2 ) )
        // We must show that at least one copy of u dissappears in this case.
        nn = Rewriter::rewrite(nn);
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
  }

  // only print debug trace if full=true
  if (!new_ret.isNull() && full)
  {
    debugExtendedRewrite(n, new_ret, ss_reason.str().c_str());
  }

  return new_ret;
}

Node ExtendedRewriter::extendedRewriteAndOr(Node n)
{
  Node new_ret;
  // all kinds are legal to substitute over : hence we give the empty map
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

Node ExtendedRewriter::extendedRewritePullIte(Kind itek, Node n)
{
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
    if (n[i].getKind() == itek)
    {
      unsigned ii = hasOp ? i + 1 : i;
      for (unsigned j = 0; j < 2; j++)
      {
        children[ii] = n[i][j + 1];
        Node pull = nm->mkNode(n.getKind(), children);
        Node pullr = Rewriter::rewrite(pull);
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
      else if (d_aggr)
      {
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
            if (tn.isBoolean())
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
  }

  for (std::pair<const unsigned, std::map<unsigned, Node> >& ip : ite_c)
  {
    Node nite = n[ip.first];
    Assert(nite.getKind() == itek);
    // now, simply pull the ITE and try ITE rewrites
    Node pull_ite = nm->mkNode(itek, nite[0], ip.second[0], ip.second[1]);
    pull_ite = Rewriter::rewrite(pull_ite);
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

  return Node::null();
}

Node ExtendedRewriter::extendedRewriteNnf(Node ret)
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

Node ExtendedRewriter::extendedRewriteBcp(
    Kind andk, Kind ork, Kind notk, std::map<Kind, bool>& bcp_kinds, Node ret)
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
  std::unordered_set<Node, NodeHashFunction> prop_clauses;
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
              & (bcp_kinds.empty()
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
        Node ccs = cc;
        if (bcp_kinds.empty())
        {
          Trace("ext-rew-bcp-debug") << "...do ordinary substitute"
                                     << std::endl;
          ccs = cc.substitute(
              avars.begin(), avars.end(), asubs.begin(), asubs.end());
        }
        else
        {
          Trace("ext-rew-bcp-debug") << "...do partial substitute" << std::endl;
          // substitution is only applicable to compatible kinds
          ccs = partialSubstitute(ccs, assign, bcp_kinds);
        }
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
        ccs = Rewriter::rewrite(ccs);
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
                                                Node n)
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
                                            bool isXor)
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
        std::vector<Node> vars;
        std::vector<Node> subs;
        if (inferSubstitution(eq, vars, subs))
        {
          Assert(vars.size() == 1);
          std::vector<Node> children;
          bool childrenChanged = false;
          // apply to all other children
          for (unsigned j = 0; j < nchild; j++)
          {
            Node ccs = n[j];
            if (i != j)
            {
              if (bcp_kinds.empty())
              {
                ccs = ccs.substitute(
                    vars.begin(), vars.end(), subs.begin(), subs.end());
              }
              else
              {
                std::map<Node, Node> assign;
                // vars.size()==subs.size()==1
                assign[vars[0]] = subs[0];
                // substitution is only applicable to compatible kinds
                ccs = partialSubstitute(ccs, assign, bcp_kinds);
              }
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
    Kind eqk, Kind andk, Kind ork, Kind notk, Node ret, bool isXor)
{
  Assert(ret.getKind() == eqk);

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
    return TermUtil::mkTypeConst(tn, gpol);
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
    if (ck == andk || ck == ork)
    {
      for (unsigned j = 0, nchild = c.getNumChildren(); j < nchild; j++)
      {
        Node cl = c[j];
        bool pol = cl.getKind() != notk;
        Node ca = pol ? cl : cl[0];
        Assert(atoms[c].find(ca) == atoms[c].end());
        // polarity is flipped when we are AND
        atoms[c][ca] = (ck == andk ? !pol : pol);
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
          for (unsigned k = 0, nchild = c.getNumChildren(); k < nchild; k++)
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
  if (Trace.isOn("ext-rew-eqchain"))
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
  new_ret = Rewriter::rewrite(new_ret);
  if (new_ret != ret)
  {
    return new_ret;
  }
  return Node::null();
}

Node ExtendedRewriter::partialSubstitute(Node n,
                                         std::map<Node, Node>& assign,
                                         std::map<Kind, bool>& rkinds)
{
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
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
      std::map<Node, Node>::iterator it = assign.find(cur);
      if (it != assign.end())
      {
        visited[cur] = it->second;
      }
      else
      {
        // can only recurse on these kinds
        Kind k = cur.getKind();
        if (rkinds.find(k) != rkinds.end())
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

Node ExtendedRewriter::solveEquality(Node n)
{
  Assert(n.getKind() == EQUAL);

  if (n[0].getType().isBitVector())
  {
    for (unsigned i = 0; i < 2; i++)
    {
      if (isConstBv(n[1 - i], false))
      {
        // (bvadd x (bvneg y)) = 0 ---> x = y
        if (n[i].getKind() == BITVECTOR_PLUS && n[i].getNumChildren() == 2)
        {
          for (unsigned j = 0; j < 2; j++)
          {
            if (n[i][j].isVar() && n[i][1 - j].getKind() == BITVECTOR_NEG
                && n[i][1 - j][0].isVar())
            {
              return n[i][j].eqNode(n[i][1 - j][0]);
            }
          }
        }
      }
    }
  }

  return Node::null();
}

bool ExtendedRewriter::inferSubstitution(Node n,
                                         std::vector<Node>& vars,
                                         std::vector<Node>& subs)
{
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
        vars.push_back(n[1 - i]);
        subs.push_back(n[i]);
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
        // TODO (#1706) : union find
        if (std::find(vars.begin(), vars.end(), r1) == vars.end())
        {
          vars.push_back(r1);
          subs.push_back(r2);
          return true;
        }
      }
    }
  }
  return false;
}

Node ExtendedRewriter::extendedRewriteArith(Node ret)
{
  Kind k = ret.getKind();
  NodeManager* nm = NodeManager::currentNM();
  Node new_ret;
  if (k == DIVISION || k == INTS_DIVISION || k == INTS_MODULUS)
  {
    // rewrite as though total
    std::vector<Node> children;
    bool all_const = true;
    for (unsigned i = 0, size = ret.getNumChildren(); i < size; i++)
    {
      if (ret[i].isConst())
      {
        children.push_back(ret[i]);
      }
      else
      {
        all_const = false;
        break;
      }
    }
    if (all_const)
    {
      Kind new_k = (ret.getKind() == DIVISION ? DIVISION_TOTAL
                                              : (ret.getKind() == INTS_DIVISION
                                                     ? INTS_DIVISION_TOTAL
                                                     : INTS_MODULUS_TOTAL));
      new_ret = nm->mkNode(new_k, children);
      debugExtendedRewrite(ret, new_ret, "total-interpretation");
    }
  }
  return new_ret;
}

Node ExtendedRewriter::extendedRewriteBv(Node ret)
{
  if (Trace.isOn("q-ext-rewrite-bv"))
  {
    Trace("q-ext-rewrite-bv") << "Extended rewrite bv : ";
    Trace("q-ext-rewrite-bv") << ret << std::endl;
  }
  Kind k = ret.getKind();
  NodeManager* nm = NodeManager::currentNM();
  Node new_ret;
  if (k == EQUAL)
  {
    // splicing
    if (ret[0].getKind() == BITVECTOR_CONCAT
        || ret[1].getKind() == BITVECTOR_CONCAT)
    {
      // get spliced forms
      std::vector<Node> v1;
      std::vector<Node> v2;
      spliceBv(ret[0], ret[1], v1, v2);
      Assert(v1.size() > 1);
      Assert(v1.size() == v2.size());
      unsigned nconst_count = 0;
      int nconst_index = -1;
      bool vs_changed = false;
      for (unsigned i = 0, size = v1.size(); i < size; i++)
      {
        Node eeq = v1[i].eqNode(v2[i]);
        eeq = Rewriter::rewrite(eeq);
        if (eeq.isConst())
        {
          if (!eeq.getConst<bool>())
          {
            new_ret = eeq;
            debugExtendedRewrite(ret, new_ret, "CONCAT eq false");
            return new_ret;
          }
        }
        else
        {
          nconst_count++;
          nconst_index = i;
        }
        for (unsigned j = 0; j < 2; j++)
        {
          Node v = j == 0 ? v1[i] : v2[i];
          Node vo = j == 0 ? v2[i] : v1[i];
          // should we negate both?
          if (v.getKind() == BITVECTOR_NOT && vo.isConst())
          {
            v = v[0];
            vo = TermUtil::mkNegate(BITVECTOR_NOT, vo);
            vo = Rewriter::rewrite(vo);
            vs_changed = true;
          }
          v1[i] = j == 0 ? v : vo;
          v2[i] = j == 0 ? vo : v;
        }
      }
      if (nconst_count == 1)
      {
        new_ret = v1[nconst_index].eqNode(v2[nconst_index]);
        debugExtendedRewrite(ret, new_ret, "CONCAT eq true");
        return new_ret;
      }
      if (vs_changed)
      {
        Node v1n = nm->mkNode(BITVECTOR_CONCAT, v1);
        Node v2n = nm->mkNode(BITVECTOR_CONCAT, v2);
        new_ret = v1n.eqNode(v2n);
        debugExtendedRewrite(ret, new_ret, "CONCAT mod component");
        return new_ret;
      }
    }

    Assert(ret[0].getType().isBitVector());
    bool hasZero = false;
    bool hasConst = false;
    unsigned cindex = 0;
    for (unsigned i = 0; i < 2; i++)
    {
      if (ret[i].isConst())
      {
        hasConst = true;
        cindex = i;
        if (isConstBv(ret[i], false))
        {
          hasZero = true;
          break;
        }
      }
    }
    if (hasConst)
    {
      // these can be flipped
      Kind nck = ret[1 - cindex].getKind();
      if (nck == BITVECTOR_NOT || nck == BITVECTOR_NEG)
      {
        new_ret = ret[1 - cindex][0].eqNode(nm->mkNode(nck, ret[cindex]));
        debugExtendedRewrite(ret, new_ret, "EQUAL const");
        return new_ret;
      }
    }
    new_ret = ret;
    Node bv_zero = mkConstBv(ret[0], false);
    for (unsigned i = 0; i < 2; i++)
    {
      if (ret[1 - i] != bv_zero)
      {
        Node slv_ret = TermUtil::mkNegate(BITVECTOR_NEG, ret[1 - i]);
        if (ret[i] != bv_zero)
        {
          slv_ret = nm->mkNode(BITVECTOR_PLUS, ret[i], slv_ret);
        }
        // FIXME : avoid this call?
        slv_ret = extendedRewrite(slv_ret);
        slv_ret = slv_ret.eqNode(bv_zero);
        slv_ret = Rewriter::rewrite(slv_ret);
        if (slv_ret.isConst())
        {
          new_ret = slv_ret;
          break;
        }
        if (d_aggr)
        {
          if ((!hasZero && i == 0) || slv_ret < new_ret)
          {
            new_ret = slv_ret;
          }
        }
      }
    }
    if (new_ret == ret)
    {
      new_ret = Node::null();
    }
    debugExtendedRewrite(ret, new_ret, "BV-eq-solve");
  }
  else if (k == ITE)
  {
    if (ret[0].getKind() == EQUAL && ret[0][0].getType().isBitVector())
    {
      for (unsigned i = 0; i < 2; i++)
      {
        Node ct = ret[0][i];
        Node cto = ret[0][1 - i];
        if (ct.isConst() && bv::utils::getSize(ct) == 1)
        {
          // do they differ by exactly one bit?
          std::vector<Node> rcc;
          int diff_index = spliceBvConstBit(ret[1], ret[2], rcc);
          if (diff_index >= 0)
          {
            Node rpl = rcc[diff_index] == ct
                           ? cto
                           : TermUtil::mkNegate(BITVECTOR_NOT, cto);
            rcc[diff_index] = rpl;
            new_ret =
                rcc.size() == 1 ? rcc[0] : nm->mkNode(BITVECTOR_CONCAT, rcc);
            debugExtendedRewrite(ret, new_ret, "BV 1bit ITE");
          }
        }
        else if (ct.getKind() == BITVECTOR_EXTRACT)
        {
          Node cte = ct[0];
          if (cte == ret[1] || cte == ret[2])
          {
            // get the other branch
            Node ob = ret[cte == ret[1] ? 2 : 1];
            // get the extension of the extract
            std::vector<Node> exs;
            exs.push_back(ct);
            Node ext = extendBv(cte, exs);
            Assert(ext.getType() == ob.getType());
            // now, splice the other branch
            std::vector<Node> extc;
            std::vector<Node> obc;
            spliceBv(ext, ob, extc, obc);
            if (obc.size() == 2 && (cto == obc[0] || cto == obc[1]))
            {
              unsigned cflip_index = cto == obc[0] ? 1 : 0;
              if (obc[cflip_index].isConst()
                  && bv::utils::getSize(obc[cflip_index]) == 1)
              {
                obc[cflip_index] =
                    TermUtil::mkNegate(BITVECTOR_NOT, obc[cflip_index]);
                Node new_eq = cte.eqNode(nm->mkNode(BITVECTOR_CONCAT, obc));
                new_ret = nm->mkNode(ITE, new_eq, ret[1], ret[2]);
                debugExtendedRewrite(ret, new_ret, "BV 1bit exrem ITE");
              }
            }
          }
        }
      }
    }
  }
  else if (k == BITVECTOR_AND || k == BITVECTOR_OR)
  {
    new_ret = rewriteBvBool(ret);
  }
  else if (k == BITVECTOR_XOR)
  {
    new_ret = extendedRewriteEqChain(
        BITVECTOR_XOR, BITVECTOR_AND, BITVECTOR_OR, BITVECTOR_NOT, ret, true);
    debugExtendedRewrite(ret, new_ret, "XOR chain simplify");
  }
  else if (k == BITVECTOR_ULT || k == BITVECTOR_SLT)
  {
    Node zero = mkConstBv(ret[0], false);
    if (ret[0] == TermUtil::mkNegate(BITVECTOR_NEG, ret[1]))
    {
      // t <_u -t ---> 0 <_s t
      // t <_s -t ---> 0 <_s -t
      new_ret =
          nm->mkNode(BITVECTOR_SLT, zero, ret[k == BITVECTOR_ULT ? 0 : 1]);
      debugExtendedRewrite(ret, new_ret, "Ineq-self-neg");
      return new_ret;
    }
    else if (ret[0] == TermUtil::mkNegate(BITVECTOR_NOT, ret[1]))
    {
      // t <_u ~t ---> ~( t <_s 0 )
      // t <_s ~t ---> ( t <_s 0 )
      new_ret = nm->mkNode(BITVECTOR_SLT, ret[0], zero);
      if (k == BITVECTOR_ULT)
      {
        new_ret = TermUtil::mkNegate(NOT, new_ret);
      }
      debugExtendedRewrite(ret, new_ret, "Ineq-self-not");
      return new_ret;
    }
    if (k == BITVECTOR_ULT)
    {
      if (bitVectorArithComp(ret[0], ret[1]))
      {
        new_ret = nm->mkConst(false);
        debugExtendedRewrite(ret, new_ret, "ULT-arith");
        return new_ret;
      }
      if (d_aggr)
      {
        if (ret[0] == zero || isConstBv(ret[1], true))
        {
          new_ret = ret[0].eqNode(ret[1]);
          new_ret = new_ret.negate();
          debugExtendedRewrite(ret, new_ret, "ULT-neq");
          return new_ret;
        }
      }
    }
    else  // k === BITVECTOR_SLT
    {
      if (ret[0] == ret[1])
      {
        new_ret = nm->mkConst(false);
        debugExtendedRewrite(ret, new_ret, "SLT-id");
        return new_ret;
      }
    }
  }
  else if (k == BITVECTOR_LSHR || k == BITVECTOR_SHL)
  {
    new_ret = rewriteBvShift(ret);
  }
  else if (k == BITVECTOR_PLUS || k == BITVECTOR_MULT)
  {
    new_ret = rewriteBvArith(ret);
  }
  else if (k == BITVECTOR_NEG)
  {
    Kind ck = ret[0].getKind();
    // miniscope
    if (ck == BITVECTOR_SHL)
    {
      new_ret = nm->mkNode(BITVECTOR_SHL,
                           TermUtil::mkNegate(BITVECTOR_NEG, ret[0][0]),
                           ret[0][1]);
      debugExtendedRewrite(ret, new_ret, "NEG-SHL-miniscope");
      return new_ret;
    }
    else if (ck == BITVECTOR_NOT)
    {
      // this should be handled by NOT-plus-miniscope below
      Assert(ret[0][0].getKind() != BITVECTOR_PLUS
             || !hasConstBvChild(ret[0][0]));
    }
    else if (ck == BITVECTOR_AND || ck == BITVECTOR_OR)
    {
      if (ret[0].getNumChildren() == 2)
      {
        std::vector<Node> children;
        for (const Node& cn : ret[0])
        {
          children.push_back(cn);
        }
        Node cplus = nm->mkNode(BITVECTOR_PLUS, children);
        cplus = Rewriter::rewrite(cplus);
        if (isConstBv(cplus, false))
        {
          // if x+y=0, then
          // -( x and y ) ---> ( x or y )
          // -( x or y ) ---> ( x and y )
          new_ret = nm->mkNode(
              ck == BITVECTOR_AND ? BITVECTOR_OR : BITVECTOR_AND, children);
          debugExtendedRewrite(ret, new_ret, "NEG-AND/OR-zero-miniscope");
          return new_ret;
        }
      }
    }
    else if (ck == BITVECTOR_CONCAT)
    {
      // negating odd numbers flips all but the lsb
      // -concat( t, 1 ) ---> concat( ~t, 1 )
      Node last_child = ret[0][ret[0].getNumChildren() - 1];
      if (last_child.isConst())
      {
        if (bv::utils::getBit(last_child, 0))
        {
          std::vector<Node> children;
          for (unsigned j = 0, size = ret[0].getNumChildren(); j < size - 1;
               j++)
          {
            children.push_back(TermUtil::mkNegate(BITVECTOR_NOT, ret[0][j]));
          }
          unsigned csize = bv::utils::getSize(last_child);
          if (csize > 1)
          {
            Node extract = bv::utils::mkExtract(last_child, csize - 1, 1);
            extract = TermUtil::mkNegate(BITVECTOR_NOT, extract);
            children.push_back(extract);
            children.push_back(bv::utils::mkOnes(1));
          }
          else
          {
            children.push_back(last_child);
          }
          new_ret = nm->mkNode(BITVECTOR_CONCAT, children);
          debugExtendedRewrite(ret, new_ret, "NEG-odd");
          return new_ret;
        }
      }
      // negating numbers with msb 1-bits flips all but the last
      // -concat( 1...11, t ) ----> concat( 0...0, -concat(1, t) )
      Node first_child = ret[0][0];
      if (first_child.isConst())
      {
        unsigned csize = bv::utils::getSize(first_child);
        int i = csize - 1;
        while (i >= 0 && bv::utils::getBit(first_child, i))
        {
          i--;
        }
        i = i + 2;
        if (i <= static_cast<int>(csize - 1))
        {
          Assert(i > 0);
          Node extract_flip = bv::utils::mkExtract(first_child, csize - 1, i);
          extract_flip = TermUtil::mkNegate(BITVECTOR_NOT, extract_flip);
          std::vector<Node> nchildren;
          nchildren.push_back(bv::utils::mkExtract(first_child, i - 1, 0));
          for (unsigned j = 1, size = ret[0].getNumChildren(); j < size; j++)
          {
            nchildren.push_back(ret[0][j]);
          }
          new_ret =
              nm->mkNode(BITVECTOR_CONCAT,
                         extract_flip,
                         nm->mkNode(BITVECTOR_NEG,
                                    nm->mkNode(BITVECTOR_CONCAT, nchildren)));
          debugExtendedRewrite(ret, new_ret, "NEG-msb-1");
          return new_ret;
        }
      }
    }
    else
    {
      new_ret = normalizeBvMonomial(ret);
      debugExtendedRewrite(ret, new_ret, "NEG-mnormalize");
    }
  }
  else if (k == BITVECTOR_NOT)
  {
    // ~( x+y ) ----> -(x+y)-1
    Kind ck = ret[0].getKind();
    if (ck == BITVECTOR_PLUS && hasConstBvChild(ret[0]))
    {
      Node max_bv = mkConstBv(ret[0], true);
      Node c = TermUtil::mkNegate(BITVECTOR_NEG, ret[0]);
      new_ret = nm->mkNode(BITVECTOR_PLUS, c, max_bv);
      debugExtendedRewrite(ret, new_ret, "NOT-plus-miniscope");
      return new_ret;
    }

    // NNF
    Kind nnfk = UNDEFINED_KIND;
    bool neg_ch = true;
    bool neg_ch_1 = false;
    if (ck == BITVECTOR_CONCAT)
    {
      nnfk = ck;
    }
    else if (ck == BITVECTOR_AND)
    {
      nnfk = BITVECTOR_OR;
    }
    else if (ck == BITVECTOR_OR)
    {
      nnfk = BITVECTOR_AND;
    }
    else if (ck == BITVECTOR_XOR)
    {
      neg_ch_1 = true;
      nnfk = ck;
    }
    if (nnfk != UNDEFINED_KIND)
    {
      std::vector<Node> nnfc;
      if (ret[0].getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        nnfc.push_back(ret[0].getOperator());
      }
      for (unsigned i = 0, size = ret[0].getNumChildren(); i < size; i++)
      {
        Node c = ret[0][i];
        c = (i == 0 ? neg_ch_1 : false) != neg_ch
                ? TermUtil::mkNegate(BITVECTOR_NOT, c)
                : c;
        nnfc.push_back(c);
      }
      new_ret = nm->mkNode(nnfk, nnfc);
      debugExtendedRewrite(ret, new_ret, "NNF bv");
      return new_ret;
    }
  }
  else if (k == BITVECTOR_CONCAT)
  {
    new_ret = normalizeBvMonomial(ret);
    debugExtendedRewrite(ret, new_ret, "CONCAT-mnormalize");
  }
  else if (k == BITVECTOR_EXTRACT)
  {
    // miniscoping
    if (ret[0].getKind() == ITE)
    {
      std::vector<Node> new_children;
      for (unsigned i = 0; i < 3; i++)
      {
        Node c = i == 0 ? ret[0][i] : nm->mkNode(ret.getOperator(), ret[0][i]);
        new_children.push_back(c);
      }
      new_ret = nm->mkNode(ITE, new_children);
      debugExtendedRewrite(ret, new_ret, "EXTRACT-miniscope");
      return new_ret;
    }
    else if (ret[0].getKind() == BITVECTOR_NEG)
    {
      if (bv::utils::getExtractHigh(ret) == 0
          && bv::utils::getExtractLow(ret) == 0)
      {
        new_ret = nm->mkNode(ret.getOperator(), ret[0][0]);
        debugExtendedRewrite(ret, new_ret, "EXTRACT-NEG-0bit");
        return new_ret;
      }
    }
  }

  if (!new_ret.isNull())
  {
    return new_ret;
  }

  // all kinds k that are bitwise go here
  // k is bitwise if <k>( x, y )[n:m] = <k>( x[n:m], y[n:m] )
  if (k == BITVECTOR_AND || k == BITVECTOR_OR || k == BITVECTOR_XOR)
  {
    // concat child pulling
    unsigned nchild = ret.getNumChildren();
    std::vector<Node> children;
    children.resize(nchild);
    for (unsigned i = 0; i < nchild; i++)
    {
      if (ret[i].getKind() == BITVECTOR_CONCAT)
      {
        Trace("q-ext-rewrite-debug")
            << "Try concat pull " << i << " of " << ret << std::endl;
        std::vector<Node> new_children;
        int copy_count = 0;
        unsigned last = bv::utils::getSize(ret[i]) - 1;
        for (unsigned j = 0, sizei = ret[i].getNumChildren(); j < sizei; j++)
        {
          unsigned csize = bv::utils::getSize(ret[i][j]);
          Assert((last + 1) >= csize);
          Node eop = nm->mkConst<BitVectorExtract>(
              BitVectorExtract(last, (last + 1) - csize));
          for (unsigned l = 0; l < nchild; l++)
          {
            children[l] = l == i ? ret[i][j] : nm->mkNode(eop, ret[l]);
          }
          Node cc = nm->mkNode(k, children);
          cc = extendedRewrite(cc);
          // check if cc copies children of ret
          if (!cc.isConst() && cc != ret[i][j])
          {
            Trace("q-ext-rewrite-debug") << "...copy : " << cc << std::endl;
            copy_count++;
            if (copy_count > 1)
            {
              // do not permit more than one copy
              break;
            }
          }
          new_children.push_back(cc);
          // decrement last if not the last child
          if ((j + 1) < sizei)
          {
            Assert(last >= csize);
            last = last - csize;
          }
        }
        if (copy_count <= 1)
        {
          new_ret = nm->mkNode(BITVECTOR_CONCAT, new_children);
          debugExtendedRewrite(ret, new_ret, "CONCAT pull");
          return new_ret;
        }
        Trace("q-ext-rewrite-debug")
            << "Failed concat pull " << i << " of " << ret << std::endl;
      }
    }
  }

  return new_ret;
}

Node ExtendedRewriter::rewriteBvArith(Node ret)
{
  Trace("q-ext-rewrite-debug") << "Rewrite bv arith " << ret << std::endl;
  Kind k = ret.getKind();
  Assert(k == BITVECTOR_PLUS || k == BITVECTOR_MULT);
  NodeManager* nm = NodeManager::currentNM();
  Node new_ret;
  unsigned size = bv::utils::getSize(ret);
  Node bv_one = bv::utils::mkOne(size);
  Node bv_neg_one = bv::utils::mkOnes(size);
  if (d_aggr)
  {
    if (k == BITVECTOR_PLUS)
    {
      std::vector<Node> nconst;
      Node cc = getConstBvChild(ret, nconst);
      if (!cc.isNull() && (cc == bv_one || cc == bv_neg_one))
      {
        Node rem = nconst.size() == 1 ? nconst[0] : nm->mkNode(k, nconst);
        if (cc == bv_one)
        {
          // x+1 ---> -( ~x )
          new_ret =
              nm->mkNode(BITVECTOR_NEG, TermUtil::mkNegate(BITVECTOR_NOT, rem));
        }
        else if (cc == bv_neg_one)
        {
          // x-1 ---> ~( -x )
          new_ret =
              nm->mkNode(BITVECTOR_NOT, TermUtil::mkNegate(BITVECTOR_NEG, rem));
        }
      }
      if (!new_ret.isNull())
      {
        debugExtendedRewrite(ret, new_ret, "arith-plus-elim");
        return new_ret;
      }
    }
  }

  std::vector<Node> rchildren;
  bool rchildrenChanged = false;
  for (const Node& rc : ret)
  {
    bool isNeg = rc.getKind() == BITVECTOR_NEG;
    Node rcc = isNeg ? rc[0] : rc;
    if (rcc.getKind() == BITVECTOR_NOT)
    {
      // ~x----> -(x+1)
      rcc = nm->mkNode(BITVECTOR_PLUS, rcc[0], bv_one);
      isNeg = !isNeg;
      rchildrenChanged = true;
    }
    if (isNeg)
    {
      // negate it
      rcc = TermUtil::mkNegate(BITVECTOR_NEG, rcc);
    }
    rchildren.push_back(rcc);
  }
  if (rchildrenChanged)
  {
    new_ret = nm->mkNode(k, rchildren);
    debugExtendedRewrite(ret, new_ret, "arith-not-child");
    return new_ret;
  }

  // general monomial normalization
  new_ret = normalizeBvMonomial(ret);
  if (!new_ret.isNull())
  {
    debugExtendedRewrite(ret, new_ret, "arith-mnormalize");
    return new_ret;
  }

  if (k == BITVECTOR_PLUS)
  {
    unsigned size = ret.getNumChildren();
    for (unsigned i = 0; i < size; i++)
    {
      for (unsigned j = (i + 1); j < size; j++)
      {
        if (bitVectorDisjoint(ret[i], ret[j]))
        {
          // if we prove disjointness, PLUS turns into OR
          // ( ( x ^ y ) ---> 0 ) => ( x+y ----> x V y )
          std::vector<Node> children;
          children.push_back(nm->mkNode(BITVECTOR_OR, ret[i], ret[j]));
          for (unsigned k = 0; k < size; k++)
          {
            if (k != i && k != j)
            {
              children.push_back(ret[k]);
            }
          }
          new_ret = children.size() == 1 ? children[0]
                                         : nm->mkNode(BITVECTOR_PLUS, children);
          debugExtendedRewrite(ret, new_ret, "PLUS-disjoint");
          return new_ret;
        }
      }
    }

    // cancelling of AND/OR children, handles these cases:
    // s - ( s & t )  ---->  s & ~t
    // s - ( s | t )  ---->  -( ~s & t )
    // ( s & t ) - s  ---->  -( s & ~t )
    // ( s | t ) - s  ---->  ~s & t

    // TODO :
    // s + ( ~s | t ) = ~( -( s & t ) )
    // s + ( t | -s ) = ( s & ~-t )

    std::map<Node, bool> retc;
    for (const Node& rc : ret)
    {
      bool pol = rc.getKind() != BITVECTOR_NEG;
      Node rca = rc.getKind() == BITVECTOR_NEG ? rc[0] : rc;
      Assert(rca.getKind() != BITVECTOR_NOT);
      Assert(retc.find(rca) == retc.end());
      retc[rca] = pol;
    }
    for (std::pair<const Node, bool>& rcp : retc)
    {
      // does AND/OR occur as child of PLUS?
      Node rc = rcp.first;
      Kind rck = rc.getKind();
      if (rck == BITVECTOR_AND || rck == BITVECTOR_OR)
      {
        bool rcpol = rcp.second;
        // is there a child that cancels?
        unsigned nchild = rc.getNumChildren();
        for (unsigned j = 0; j < nchild; j++)
        {
          Node rcc = rc[j];
          // check if it occurs under ret
          std::map<Node, bool>::iterator itr = retc.find(rcc);
          if (itr != retc.end())
          {
            // with opposite polarity?
            if (rcpol != itr->second)
            {
              // collect remainder
              std::vector<Node> new_children;
              for (unsigned k = 0; k < nchild; k++)
              {
                if (k != j)
                {
                  new_children.push_back(rc[k]);
                }
              }
              Node nc[2];
              nc[0] = rc[j];
              nc[1] = new_children.size() == 1 ? new_children[0]
                                               : nm->mkNode(rck, new_children);
              // determine the index to negate
              unsigned nindex = rck == BITVECTOR_AND ? 1 : 0;
              nc[nindex] = TermUtil::mkNegate(BITVECTOR_NOT, nc[nindex]);
              // combine the children
              Node new_c = nm->mkNode(BITVECTOR_AND, nc[0], nc[1]);
              new_c = rcpol == (rck == BITVECTOR_AND)
                          ? TermUtil::mkNegate(BITVECTOR_NEG, new_c)
                          : new_c;
              retc.erase(rc);
              retc.erase(rcc);
              std::vector<Node> sum;
              for (std::pair<const Node, bool>& rcnp : retc)
              {
                Node rcn = rcnp.first;
                Node rcnn =
                    rcnp.second ? rcn : TermUtil::mkNegate(BITVECTOR_NEG, rcn);
                sum.push_back(rcnn);
              }
              sum.push_back(new_c);
              new_ret =
                  sum.size() == 1 ? sum[0] : nm->mkNode(BITVECTOR_PLUS, sum);
              debugExtendedRewrite(ret, new_ret, "PLUS-AND/OR cancel");
              return new_ret;
            }
          }
        }
      }
    }
  }
  return Node::null();
}

Node ExtendedRewriter::rewriteBvShift(Node ret)
{
  Kind k = ret.getKind();
  Assert(k == BITVECTOR_LSHR || k == BITVECTOR_SHL);
  NodeManager* nm = NodeManager::currentNM();
  Node new_ret;

  std::vector<Node> cchildren;
  Node base = decomposeRightAssocChain(k, ret, cchildren);

  if (k == BITVECTOR_LSHR)
  {
    std::vector<Node> bchildren;
    Kind bk = base.getKind();
    if (bk == BITVECTOR_OR || bk == BITVECTOR_XOR)
    {
      for (const Node& cr : base)
      {
        bchildren.push_back(cr);
      }
    }
    else
    {
      bchildren.push_back(base);
    }
    std::vector<Node> bctemp;
    bctemp.insert(bctemp.end(), bchildren.begin(), bchildren.end());
    bchildren.clear();
    bool childChanged = false;
    for (const Node& bc : bctemp)
    {
      // take into account NOT
      Node bca = bc.getKind() == BITVECTOR_NOT ? bc[0] : bc;
      bool shifted = false;
      for (const Node& cc : cchildren)
      {
        if (bitVectorArithComp(cc, bca))
        {
          shifted = true;
          break;
        }
      }
      // we are not able to shift away its 1-bits
      if (shifted)
      {
        // rewrite rule #20
        // if we shifted it away, then it might has well have been all 0's.
        Node const_bv = mkConstBv(bc, bc.getKind() == BITVECTOR_NOT);
        bchildren.push_back(const_bv);
        childChanged = true;
      }
      else
      {
        bchildren.push_back(bc);
      }
    }
    if (childChanged)
    {
      base = bchildren.size() == 1 ? bchildren[0] : nm->mkNode(bk, bchildren);
    }
  }
  new_ret = mkRightAssocChain(k, base, cchildren);
  if (new_ret != ret)
  {
    debugExtendedRewrite(ret, new_ret, "shift-sort-arith");
    return new_ret;
  }

  if (k == BITVECTOR_SHL)
  {
    new_ret = normalizeBvMonomial(ret);
    if (!new_ret.isNull())
    {
      debugExtendedRewrite(ret, new_ret, "SHL-mnormalize");
      return new_ret;
    }
  }

  return Node::null();
}

Node ExtendedRewriter::rewriteBvBool(Node ret)
{
  Kind k = ret.getKind();
  Assert(k == BITVECTOR_AND || k == BITVECTOR_OR);
  NodeManager* nm = NodeManager::currentNM();
  Node new_ret;

  bool isAnd = (k == BITVECTOR_AND);
  std::unordered_set<unsigned> drops;
  std::vector<Node> children;
  unsigned size = ret.getNumChildren();
  for (unsigned i = 0; i < size; i++)
  {
    Node cmpi = isAnd ? ret[i] : TermUtil::mkNegate(BITVECTOR_NOT, ret[i]);
    bool success = true;
    for (unsigned j = 0; j < size; j++)
    {
      if (i != j && drops.find(j) == drops.end())
      {
        if (bitVectorSubsume(ret[isAnd ? i : j], ret[isAnd ? j : i]) != 0)
        {
          drops.insert(i);
          success = false;
        }
        Node cmpj = isAnd ? ret[j] : TermUtil::mkNegate(BITVECTOR_NOT, ret[j]);
        if (i < j && bitVectorDisjoint(cmpi, cmpj))
        {
          new_ret = mkConstBv(ret, !isAnd);
          debugExtendedRewrite(ret, new_ret, "AND/OR-disjoint");
          return new_ret;
        }
      }
    }
    if (success)
    {
      children.push_back(ret[i]);
    }
  }
  Assert(!children.empty());
  if (children.size() < size)
  {
    new_ret = children.size() == 1 ? children[0] : nm->mkNode(k, children);
    debugExtendedRewrite(ret, new_ret, "AND/OR subsume");
    return new_ret;
  }

  // Boolean constraint propagation
  if (d_aggr)
  {
    // specify legal BCP kinds
    std::map<Kind, bool> bcp_kinds;
    bcp_kinds[BITVECTOR_AND] = true;
    bcp_kinds[BITVECTOR_OR] = true;
    bcp_kinds[BITVECTOR_NOT] = true;
    bcp_kinds[BITVECTOR_XOR] = true;
    new_ret = extendedRewriteBcp(
        BITVECTOR_AND, BITVECTOR_OR, BITVECTOR_NOT, bcp_kinds, ret);
    if (!new_ret.isNull())
    {
      debugExtendedRewrite(ret, new_ret, "BV bcp");
      return new_ret;
    }
    new_ret = extendedRewriteEqRes(BITVECTOR_AND,
                                   BITVECTOR_OR,
                                   BITVECTOR_XOR,
                                   BITVECTOR_NOT,
                                   bcp_kinds,
                                   ret,
                                   true);
    if (!new_ret.isNull())
    {
      debugExtendedRewrite(ret, new_ret, "BV eq res");
      return new_ret;
    }
  }

  return Node::null();
}

int ExtendedRewriter::bitVectorSubsume(Node a, Node b, bool strict, bool tryNot)
{
  Assert(a.getType() == b.getType());
  int max_ret = strict ? 2 : 1;
  int curr_ret = 0;
  Trace("q-ext-rewrite-debug2")
      << "Subsume " << a << " " << b << "?" << std::endl;
  // simple cases : a=b, a=max, b=0
  if (a == b || isConstBv(a, true) || isConstBv(b, false))
  {
    curr_ret = 1;
  }
  else if (a.isConst() && b.isConst())
  {
    unsigned csize = bv::utils::getSize(a);
    for (unsigned i = 0; i < csize; i++)
    {
      if (bv::utils::getBit(a, i) != bv::utils::getBit(b, i))
      {
      }
    }
  }

  if (curr_ret == max_ret)
  {
    return max_ret;
  }

  Kind ak = a.getKind();
  Kind bk = b.getKind();

  //------------------recurse on CONCAT
  if (ak == BITVECTOR_CONCAT || bk == BITVECTOR_CONCAT)
  {
    unsigned counter = bv::utils::getSize(a) - 1;
    bool reca = ak == BITVECTOR_CONCAT;
    Node cterm = reca ? a : b;
    Node oterm = reca ? b : a;
    int ccurr = 1;
    // each piece must subsume
    for (const Node& ctermc : cterm)
    {
      unsigned csize = bv::utils::getSize(ctermc);
      Assert((counter + 1) >= csize);
      Node extract =
          bv::utils::mkExtract(oterm, counter, (counter + 1) - csize);
      extract = Rewriter::rewrite(extract);

      // check subsume
      int cret = bitVectorSubsume(
          reca ? ctermc : extract, reca ? extract : ctermc, strict);
      if (cret == 0)
      {
        ccurr = 0;
        break;
      }
      else if (cret > ccurr)
      {
        ccurr = cret;
      }
      if (counter >= csize)
      {
        counter = counter - csize;
      }
    }
    // if all pieces subsume, then we take the max and update the return value
    if (ccurr == max_ret)
    {
      return max_ret;
    }
    else if (ccurr > curr_ret)
    {
      curr_ret = ccurr;
    }
  }

  //---------------recurse BITVECTOR_NOT
  if (ak == BITVECTOR_NOT && bk == BITVECTOR_NOT)
  {
    return bitVectorSubsume(b[0], a[0], strict);
  }

  //--------------recurse extract
  if (ak == BITVECTOR_EXTRACT && bk == BITVECTOR_EXTRACT
      && a.getOperator() == b.getOperator())
  {
    return bitVectorSubsume(a[0], b[0], strict);
  }

  //---------------recurse BITVECTOR_AND/OR
  bool reca = false;
  Node rec;
  if (ak == BITVECTOR_OR)
  {
    rec = a;
    reca = true;
  }
  else if (bk == BITVECTOR_AND)
  {
    rec = b;
  }
  if (!rec.isNull())
  {
    for (const Node& rc : rec)
    {
      int cret = bitVectorSubsume(reca ? rc : a, reca ? b : rc, strict);
      if (cret == max_ret)
      {
        return max_ret;
      }
      else if (cret > curr_ret)
      {
        curr_ret = cret;
      }
    }
    rec = Node::null();
  }

  //---------------recurse ITE
  if (ak == ITE)
  {
    rec = a;
    reca = true;
  }
  else if (bk == ITE)
  {
    rec = b;
    reca = false;
  }
  if (!rec.isNull())
  {
    int r1 = bitVectorSubsume(reca ? a[1] : a, reca ? b : b[1], strict);
    if (r1 > curr_ret)
    {
      int r2 = bitVectorSubsume(reca ? a[2] : a, reca ? b : b[2], strict);
      if (r2 > curr_ret)
      {
        curr_ret = r2 > r1 ? r1 : r2;
        if (curr_ret = max_ret)
        {
          return max_ret;
        }
      }
    }
    rec = Node::null();
  }

  //-----------------cases for b
  if (bk == BITVECTOR_SHL)
  {
    if (b[0].getKind() == BITVECTOR_LSHR)
    {
      if (b[0][0] == a && b[0][1] == b[1])
      {
        // x subsumes bvshl( bvlshr( x, y ), y )
        curr_ret = 1;
      }
    }
    Node anot = TermUtil::mkNegate(BITVECTOR_NOT, a);
    // x subsumes bvshl( y, z ) if z>=(~x).
    if (bitVectorArithComp(b[1], anot))
    {
      curr_ret = 1;
    }
  }
  else if (bk == BITVECTOR_LSHR)
  {
    if (b[0].getKind() == BITVECTOR_SHL)
    {
      if (b[0][0] == a && b[0][1] == b[1])
      {
        // x subsumes bvlshr( bvshl( x, y ), y )
        curr_ret = 1;
      }
    }
  }
  else if (bk == BITVECTOR_NEG)
  {
    if (b[0].getKind() == BITVECTOR_SHL)
    {
      Node anot = TermUtil::mkNegate(BITVECTOR_NOT, a);
      // x subsumes -bvshl( y, z ) if z>=(~x).
      if (bitVectorArithComp(b[0][1], anot))
      {
        curr_ret = 1;
      }
    }
  }

  if (curr_ret == max_ret)
  {
    return max_ret;
  }

  if (tryNot)
  {
    if (ak == BITVECTOR_NOT || bk == BITVECTOR_NOT)
    {
      int ret = bitVectorSubsume(TermUtil::mkNegate(BITVECTOR_NOT, b),
                                 TermUtil::mkNegate(BITVECTOR_NOT, a),
                                 strict,
                                 false);
      if (ret > curr_ret)
      {
        curr_ret = ret;
      }
    }
  }

  return curr_ret;
}

int ExtendedRewriter::bitVectorArithComp(Node a, Node b, bool strict)
{
  Assert(a.getType() == b.getType());
  int max_ret = strict ? 2 : 1;
  Trace("q-ext-rewrite-debug2")
      << "Arith comp " << a << " " << b << "?" << std::endl;
  int curr_ret = bitVectorSubsume(a, b, strict);
  if (curr_ret == max_ret)
  {
    return max_ret;
  }
  if (a.isConst() && b.isConst())
  {
    // TODO
  }

  // flip
  if (a.getKind() == BITVECTOR_NEG && b.getKind() == BITVECTOR_NEG)
  {
    return bitVectorArithComp(b[0], a[0], strict);
  }

  // shifting right always shrinks
  if (b.getKind() == BITVECTOR_LSHR)
  {
    if (bitVectorArithComp(a, b[0], strict) == max_ret)
    {
      curr_ret = 1;
      // if strict, also must be greater than zero shift
      if (strict)
      {
        Node zero = mkConstBv(b[1], false);
        if (bitVectorArithComp(b[1], zero, strict))
        {
          return max_ret;
        }
      }
    }
  }
  else if (b.getKind() == BITVECTOR_NOT)
  {
    if (a.getKind() == BITVECTOR_NOT)
    {
      // flipped?
    }
  }

  return curr_ret;
}

bool ExtendedRewriter::bitVectorDisjoint(Node a, Node b)
{
  Assert(a.getType() == b.getType());
  if (a.isConst() && b.isConst())
  {
    // TODO
  }
  // must be dually subsuming
  bool dualSubsumeSuccess = true;
  for (unsigned r = 0; r < 2; r++)
  {
    Node x = r == 0 ? a : b;
    Node y = r == 0 ? b : a;
    x = TermUtil::mkNegate(BITVECTOR_NOT, x);
    if (bitVectorSubsume(x, y) == 0)
    {
      dualSubsumeSuccess = false;
      break;
    }
  }
  if (dualSubsumeSuccess)
  {
    return true;
  }
  // infer the minimal and maximal indices
  /*
  unsigned min_a;
  unsigned max_a;
  bitVectorIntervalSetIndices(a, min_a, max_a );
  unsigned min_b;
  unsigned max_b;
  bitVectorIntervalSetIndices(a, min_b, max_b );
  if( min_b>max_a || min_a>max_b )
  {
    return true;
  }
  */
  return false;
}

void bitVectorIntervalSetIndices(Node a, unsigned& min_i, unsigned& max_i)
{
  unsigned size = bv::utils::getSize(a);
  Assert(size > 0);
  min_i = 0;
  max_i = size - 1;
  if (a.isConst())
  {
    for (unsigned i = 0; i < size; i++)
    {
    }
  }
  Kind ak = a.getKind();
  if (ak == BITVECTOR_SHL || ak == BITVECTOR_LSHR)
  {
    // constant shift
    if (a[1].isConst())
    {
    }
  }
  else if (ak == BITVECTOR_AND || ak == BITVECTOR_OR)
  {
  }
  else if (ak == MULT)
  {
    // powers of two combine
  }
}

Node ExtendedRewriter::decomposeRightAssocChain(Kind k,
                                                Node n,
                                                std::vector<Node>& children)
{
  Node curr = n;
  while (curr.getKind() == k)
  {
    children.push_back(curr[1]);
    curr = curr[0];
  }
  return curr;
}

Node ExtendedRewriter::mkRightAssocChain(Kind k,
                                         Node base,
                                         std::vector<Node>& children)
{
  NodeManager* nm = NodeManager::currentNM();
  Node curr = base;
  if (!children.empty())
  {
    // always sort
    std::sort(children.begin(), children.end());
    for (const Node& c : children)
    {
      curr = nm->mkNode(k, curr, c);
    }
  }
  return curr;
}

Node ExtendedRewriter::mkConstBv(Node n, bool isNot)
{
  unsigned size = bv::utils::getSize(n);
  return isNot ? bv::utils::mkOnes(size) : bv::utils::mkZero(size);
}

bool ExtendedRewriter::isConstBv(Node n, bool isNot)
{
  if (n.isConst())
  {
    Node const_n = mkConstBv(n, isNot);
    return n == const_n;
  }
  return false;
}

Node ExtendedRewriter::getConstBvChild(Node n, std::vector<Node>& nconst)
{
  Node ret;
  for (const Node& cn : n)
  {
    if (cn.isConst())
    {
      // we call this on bit-vector operators whose rewritten form has only one
      // constant child
      Assert(ret.isNull());
      ret = cn;
    }
    else
    {
      nconst.push_back(cn);
    }
  }
  return ret;
}

bool ExtendedRewriter::hasConstBvChild(Node n)
{
  for (const Node& cn : n)
  {
    if (cn.isConst())
    {
      return true;
    }
  }
  return false;
}

Node ExtendedRewriter::normalizeBvMonomial(Node n)
{
  // general monomial normalization
  std::map<Node, Node> msum;
  getBvMonomialSum(n, msum);

  if (Trace.isOn("q-ext-rewrite-bvarith"))
  {
    Trace("q-ext-rewrite-bvarith")
        << "Monomial representation of " << n << " : " << std::endl;
    for (std::pair<const Node, Node>& m : msum)
    {
      Assert(!m.second.isNull());
      Assert(m.second.getType() == m.first.getType());
      Node c = Rewriter::rewrite(m.second);
      Trace("q-ext-rewrite-bvarith") << "  " << m.first << " * " << c;
      Trace("q-ext-rewrite-bvarith") << std::endl;
    }
  }

  // monomial normalization technqiues

  NodeManager* nm = NodeManager::currentNM();

  // group terms that have the same factors
  for (unsigned r = 0; r < 2; r++)
  {
    // the kind we are factoring
    Kind fk = r == 0 ? BITVECTOR_SHL : BITVECTOR_MULT;
    std::vector<Node> fcts;
    std::map<Node, std::unordered_set<Node, NodeHashFunction> > fct_ms;
    std::map<Node, std::vector<Node> > ms_to_fct;
    std::map<Node, Node> ms_to_base;
    for (std::pair<const Node, Node>& m : msum)
    {
      Node v = m.first;
      bool success = false;
      if (r == 0)
      {
        // BITVECTOR_SHL is decomposed as right-associative chain
        if (v.getKind() == fk)
        {
          ms_to_base[v] = decomposeRightAssocChain(fk, v, ms_to_fct[v]);
          success = true;
        }
      }
      else if (r == 1)
      {
        success = true;
        // BITVECTOR_MULT is decomposed as children or self
        if (v.getKind() == fk)
        {
          for (const Node& vc : v)
          {
            ms_to_fct[v].push_back(vc);
          }
        }
        else
        {
          ms_to_fct[v].push_back(v);
        }
      }
      if (success)
      {
        std::vector<Node>& mts = ms_to_fct[v];
        for (const Node& sl : mts)
        {
          fct_ms[sl].insert(v);
          if (std::find(fcts.begin(), fcts.end(), sl) == fcts.end())
          {
            fcts.push_back(sl);
          }
        }
      }
    }
    if (!fcts.empty())
    {
      unsigned size = bv::utils::getSize(n);
      Node bvone = bv::utils::mkOne(size);
      std::sort(fcts.begin(), fcts.end());
      for (const Node& sl : fcts)
      {
        std::unordered_set<Node, NodeHashFunction>& sms = fct_ms[sl];
        if (sms.size() > 1)
        {
          Trace("q-ext-rewrite-bvarith-debug")
              << "Factoring " << sl << std::endl;
          // reconsturct the monomial
          std::map<Node, Node> msum_new;
          std::vector<Node> group_children;
          for (std::pair<const Node, Node>& m : msum)
          {
            Node v = m.first;
            if (sms.find(v) == sms.end())
            {
              msum_new[v] = m.second;
            }
            else
            {
              // remove a factor (make a copy of vector here)
              std::vector<Node> mts = ms_to_fct[v];
              std::vector<Node>::iterator it =
                  std::find(mts.begin(), mts.end(), sl);
              Assert(it != mts.end());
              mts.erase(it);
              Node gc;
              if (r == 0)
              {
                gc = mkRightAssocChain(fk, ms_to_base[v], mts);
              }
              else
              {
                gc = mts.empty()
                         ? bvone
                         : (mts.size() == 1 ? mts[0]
                                            : nm->mkNode(BITVECTOR_MULT, mts));
              }
              gc = nm->mkNode(BITVECTOR_MULT, gc, m.second);
              Trace("q-ext-rewrite-bvarith-debug")
                  << "...group child : " << gc << std::endl;
              group_children.push_back(gc);
            }
          }
          Assert(group_children.size() > 1);
          Node sgc = nm->mkNode(BITVECTOR_PLUS, group_children);
          // FIXME : avoid this call?
          sgc = extendedRewrite(sgc);
          sgc = nm->mkNode(fk, sgc, sl);
          msum_new[sgc] = bvone;
          Node new_ret = mkNodeFromBvMonomial(n, msum_new);
          new_ret = Rewriter::rewrite(new_ret);
          if (new_ret != n)
          {
            Trace("q-ext-rewrite-bvarith")
                << "Factored " << sl << " " << fk << " : " << n << " -> "
                << new_ret << std::endl;
            return new_ret;
          }
        }
      }
    }
  }

  Node new_ret = mkNodeFromBvMonomial(n, msum);
  Trace("q-ext-rewrite-bvarith")
      << "...got (pre-rewrite) : " << new_ret << std::endl;
  new_ret = Rewriter::rewrite(new_ret);
  if (new_ret != n)
  {
    return new_ret;
  }
  Trace("q-ext-rewrite-bvarith")
      << "Monomial " << n << " did not normalize." << std::endl;
  return Node::null();
}

void ExtendedRewriter::getBvMonomialSum(Node n, std::map<Node, Node>& msum)
{
  Trace("q-ext-rewrite-debug2") << "get bv monomial sum " << n << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  unsigned size = bv::utils::getSize(n);
  Node bv_one = bv::utils::mkOne(size);
  std::map<Node, Node> n_msum;
  if (n.isConst())
  {
    n_msum[bv_one] = n;
  }
  else
  {
    Kind k = n.getKind();
    if (k == BITVECTOR_PLUS)
    {
      for (const Node& cn : n)
      {
        getBvMonomialSum(cn, msum);
      }
    }
    else if (k == BITVECTOR_NEG)
    {
      getBvMonomialSum(n[0], n_msum);
      for (std::map<Node, Node>::iterator it = n_msum.begin();
           it != n_msum.end();
           ++it)
      {
        Node coeff = it->second;
        n_msum[it->first] = TermUtil::mkNegate(BITVECTOR_NEG, coeff);
      }
    }
    else if (k == BITVECTOR_NOT)
    {
      Node rec =
          nm->mkNode(BITVECTOR_NEG, nm->mkNode(BITVECTOR_PLUS, n[0], bv_one));
      getBvMonomialSum(rec, msum);
    }
    else if (k == BITVECTOR_CONCAT)
    {
      unsigned nchildren = n.getNumChildren();
      // if the last child is zero
      if (isConstBv(n[nchildren - 1], false))
      {
        Node rec;
        if (nchildren == 2 && n[0].getKind() == BITVECTOR_EXTRACT
            && bv::utils::getExtractLow(n[0]) == 0)
        {
          rec = n[0][0];
        }
        else
        {
          std::vector<Node> rchildren;
          for (unsigned j = 0; j < nchildren - 1; j++)
          {
            rchildren.push_back(n[j]);
          }
          rec = rchildren.size() == 1 ? rchildren[0]
                                      : nm->mkNode(BITVECTOR_CONCAT, rchildren);
        }
        unsigned size_rec = bv::utils::getSize(rec);
        // must ensure the same type
        if (size_rec > size)
        {
          rec = bv::utils::mkExtract(rec, size - 1, 0);
          rec = Rewriter::rewrite(rec);
        }
        else if (size_rec < size)
        {
          unsigned diff = size - size_rec;
          Node bzero = bv::utils::mkZero(diff);
          rec = nm->mkNode(BITVECTOR_CONCAT, bzero, rec);
          rec = Rewriter::rewrite(rec);
        }
        Assert(rec.getType() == n.getType());

        unsigned sizez = bv::utils::getSize(n[nchildren - 1]);
        Integer powsizez = Integer(1).multiplyByPow2(sizez);
        Node ccoeff = bv::utils::mkConst(size, powsizez);

        getBvMonomialSum(rec, n_msum);
        for (std::map<Node, Node>::iterator it = n_msum.begin();
             it != n_msum.end();
             ++it)
        {
          Node coeff = it->second;
          Assert(coeff.getType() == ccoeff.getType());
          n_msum[it->first] = nm->mkNode(BITVECTOR_MULT, coeff, ccoeff);
        }
      }
      else
      {
        n_msum[n] = bv_one;
      }
    }
    else if (k == BITVECTOR_MULT)
    {
      std::vector<Node> shls;
      std::vector<Node> children;
      Node coeff = bv_one;
      for (const Node& cn : n)
      {
        Node cnb = cn;
        if (cnb.getKind() == BITVECTOR_SHL)
        {
          cnb = decomposeRightAssocChain(BITVECTOR_SHL, cnb, shls);
        }
        std::map<Node, Node> cn_msum;
        getBvMonomialSum(cnb, cn_msum);
        if (cn_msum.size() == 1)
        {
          for (std::pair<const Node, Node>& mc : cn_msum)
          {
            Trace("q-ext-rewrite-debug2") << ".....factor : ";
            if (!mc.first.isConst())
            {
              Trace("q-ext-rewrite-debug2") << mc.first << " * ";
              children.push_back(mc.first);
            }
            Trace("q-ext-rewrite-debug2") << mc.second << std::endl;
            if (mc.second != bv_one)
            {
              coeff = nm->mkNode(BITVECTOR_MULT, coeff, mc.second);
            }
          }
        }
        else
        {
          // don't distribute
          children.push_back(cnb);
          Trace("q-ext-rewrite-debug2") << ".....factor : " << cnb << std::endl;
        }
      }
      Node v = bv_one;
      if (children.size() == 1)
      {
        v = children[0];
      }
      else if (children.size() > 1)
      {
        v = nm->mkNode(BITVECTOR_MULT, children);
      }
      if (!shls.empty())
      {
        v = mkRightAssocChain(BITVECTOR_SHL, v, shls);
      }
      Trace("q-ext-rewrite-debug2")
          << "...got " << v << " * " << coeff << std::endl;
      n_msum[v] = coeff;
    }
    else if (k == BITVECTOR_SHL)
    {
      std::vector<Node> shls;
      Node nn = decomposeRightAssocChain(BITVECTOR_SHL, n, shls);
      std::map<Node, Node> nn_msum;
      getBvMonomialSum(nn, nn_msum);
      if (nn_msum.size() == 1)
      {
        for (std::pair<const Node, Node>& nnc : nn_msum)
        {
          Node v = mkRightAssocChain(BITVECTOR_SHL, nnc.first, shls);
          n_msum[v] = nnc.second;
        }
      }
      else
      {
        // do not distribute
        n_msum[n] = bv_one;
      }
    }
    else
    {
      n_msum[n] = bv_one;
    }
  }
  // add the monomial sum for this node if we generated one
  if (!n_msum.empty())
  {
    for (std::pair<const Node, Node>& m : n_msum)
    {
      Node v = m.first;
      Node coeff = m.second;
      std::map<Node, Node>::iterator itm = msum.find(v);
      if (itm == msum.end())
      {
        msum[v] = coeff;
      }
      else
      {
        msum[v] = nm->mkNode(BITVECTOR_PLUS, coeff, itm->second);
      }
    }
  }
}

Node ExtendedRewriter::mkNodeFromBvMonomial(Node n, std::map<Node, Node>& msum)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> sum;
  for (std::pair<const Node, Node>& m : msum)
  {
    Node v = m.first;
    Node c = Rewriter::rewrite(m.second);
    Node mm = nm->mkNode(BITVECTOR_MULT, c, v);
    mm = Rewriter::rewrite(mm);
    sum.push_back(mm);
  }
  if (sum.empty())
  {
    return mkConstBv(n, false);
  }
  else if (sum.size() == 1)
  {
    return sum[0];
  }
  return nm->mkNode(BITVECTOR_PLUS, sum);
}

void ExtendedRewriter::spliceBv(Node a,
                                Node b,
                                std::vector<Node>& av,
                                std::vector<Node>& bv)
{
  Assert(a.getType() == b.getType());
  if (a.getKind() == BITVECTOR_CONCAT || b.getKind() == BITVECTOR_CONCAT)
  {
    unsigned counter = bv::utils::getSize(a) - 1;
    bool reca = a.getKind() == BITVECTOR_CONCAT;
    Node cterm = reca ? a : b;
    Node oterm = reca ? b : a;
    for (const Node& ctermc : cterm)
    {
      // extract relevant portion of other child
      unsigned csize = bv::utils::getSize(ctermc);
      Assert((counter + 1) >= csize);
      Node extract =
          bv::utils::mkExtract(oterm, counter, (counter + 1) - csize);
      extract = Rewriter::rewrite(extract);
      // recurse
      Node c1 = reca ? ctermc : extract;
      Node c2 = reca ? extract : ctermc, strict;
      spliceBv(c1, c2, av, bv);
      // decrement counter
      if (counter >= csize)
      {
        counter = counter - csize;
      }
    }
  }
  else
  {
    av.push_back(a);
    bv.push_back(b);
  }
}

int ExtendedRewriter::spliceBvConstBit(Node n1, Node n2, std::vector<Node>& nv)
{
  if (n1 == n2)
  {
    return -1;
  }
  Trace("q-ext-rewrite-debug")
      << "Splice constant bv bit " << n1 << " " << n2 << std::endl;
  // splice the children
  std::vector<Node> rc1;
  std::vector<Node> rc2;
  spliceBv(n1, n2, rc1, rc2);
  Assert(rc1.size() == rc2.size());
  int diff_index = -1;
  for (unsigned r = 0; r < rc1.size(); r++)
  {
    if (rc1[r] != rc2[r])
    {
      if (diff_index >= 0)
      {
        // differ at more than one index
        Trace("q-ext-rewrite-debug")
            << "...more than one diff component." << std::endl;
        return -1;
      }
      diff_index = r;
    }
  }
  Assert(diff_index >= 0);
  if (!rc1[diff_index].isConst() || !rc2[diff_index].isConst())
  {
    Trace("q-ext-rewrite-debug")
        << "...non-constant diff components." << std::endl;
    return -1;
  }
  // insert prefix
  if (diff_index > 0)
  {
    nv.insert(nv.end(), rc1.begin(), rc1.begin() + diff_index);
  }
  Assert(rc1[diff_index] != rc2[diff_index]);
  Node c1 = rc1[diff_index];
  Node c2 = rc2[diff_index];
  // do they differ by exactly one bit?
  int bit_diff_index = -1;
  unsigned csize = bv::utils::getSize(c1);
  for (unsigned i = 0; i < csize; i++)
  {
    if (bv::utils::getBit(c1, i) != bv::utils::getBit(c2, i))
    {
      if (bit_diff_index >= 0)
      {
        // differ by more than one bit
        nv.clear();
        Trace("q-ext-rewrite-debug")
            << "...more than one bit diff." << std::endl;
        return -1;
      }
      bit_diff_index = i;
    }
  }
  if (bit_diff_index >= 0)
  {
    std::vector<Node> split;
    if (bit_diff_index + 1 < static_cast<int>(csize))
    {
      Node extract = bv::utils::mkExtract(c1, csize - 1, bit_diff_index + 1);
      nv.push_back(Rewriter::rewrite(extract));
    }
    Node bit = bv::utils::getBit(c1, bit_diff_index) ? bv::utils::mkOnes(1)
                                                     : bv::utils::mkZero(1);
    diff_index = nv.size();
    nv.push_back(bit);
    // remainder
    if (bit_diff_index > 0)
    {
      Node extract = bv::utils::mkExtract(c1, bit_diff_index - 1, 0);
      nv.push_back(Rewriter::rewrite(extract));
    }
    // insert suffix
    if (diff_index < static_cast<int>(rc1.size()))
    {
      nv.insert(nv.end(), rc1.begin() + diff_index + 1, rc1.end());
    }
    return diff_index;
  }
  return -1;
}

Node ExtendedRewriter::extendBv(Node n, std::vector<Node>& exs)
{
  std::map<unsigned, Node> ex_map;
  for (const Node& e : exs)
  {
    Assert( e.getKind()==BITVECTOR_EXTRACT );
    Assert( e[0]==n );
    ex_map[bv::utils::getExtractHigh(e)] = e;
  }
  return extendBv(n, ex_map);
}

Node ExtendedRewriter::extendBv(Node n, std::map<unsigned, Node>& ex_map)
{
  Trace("q-ext-rewrite-debug") << "extendBv " << n << std::endl;
  std::vector<Node> children;
  int counter = bv::utils::getSize(n) - 1;
  for (const std::pair<const unsigned, Node>& ep : ex_map)
  {
    Trace("q-ext-rewrite-debug")
        << "  process " << ep.first << " : " << ep.second
        << ", counter=" << counter << std::endl;
    unsigned start = ep.first;
    Assert(static_cast<int>(start) <= counter);
    if (static_cast<int>(start) < counter)
    {
      children.push_back(bv::utils::mkExtract(n, counter, start + 1));
    }
    Node ex = ep.second;
    children.push_back(ex);
    // update the counter
    unsigned esize = bv::utils::getSize(ex);
    counter = start - esize;
    Assert(counter + 1 >= 0);
  }
  if (counter >= 0)
  {
    children.push_back(bv::utils::mkExtract(n, counter, 0));
  }
  Trace("q-ext-rewrite-debug")
      << "extendBv finish, children = " << children << std::endl;
  if (children.empty())
  {
    return n;
  }
  return children.size() == 1
             ? children[0]
             : NodeManager::currentNM()->mkNode(BITVECTOR_CONCAT, children);
}

void ExtendedRewriter::debugExtendedRewrite(Node n,
                                            Node ret,
                                            const char* c) const
{
  if (Trace.isOn("q-ext-rewrite"))
  {
    if (!ret.isNull())
    {
      Trace("q-ext-rewrite-apply") << "sygus-extr : apply " << c << std::endl;
      Trace("q-ext-rewrite") << "sygus-extr : " << c << " : " << n
                             << " rewrites to " << ret << std::endl;
    }
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
