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
 * Implementation of arithmetic entailment computation for string terms.
 */

#include "theory/strings/arith_entail.h"

#include "expr/attribute.h"
#include "expr/node_algorithm.h"
#include "proof/conv_proof_generator.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_poly_norm.h"
#include "theory/arith/arith_subs.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "theory/theory.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

ArithEntail::ArithEntail(NodeManager* nm, Rewriter* r, bool recApprox)
    : d_rr(r), d_recApprox(recApprox)
{
  d_one = nm->mkConstInt(Rational(1));
  d_zero = nm->mkConstInt(Rational(0));
}

Node ArithEntail::rewritePredViaEntailment(const Node& n, bool isSimple)
{
  Node exp;
  return rewritePredViaEntailment(n, exp, isSimple);
}

Node ArithEntail::rewritePredViaEntailment(const Node& n,
                                           Node& exp,
                                           bool isSimple)
{
  NodeManager* nm = n.getNodeManager();
  if (n.getKind() == Kind::EQUAL && n[0].getType().isInteger())
  {
    exp = nm->mkNode(Kind::SUB, nm->mkNode(Kind::SUB, n[0], n[1]), d_one);
    if (!findApprox(rewriteArith(exp), isSimple).isNull())
    {
      return nm->mkConst(false);
    }
    exp = nm->mkNode(Kind::SUB, nm->mkNode(Kind::SUB, n[1], n[0]), d_one);
    if (!findApprox(rewriteArith(exp), isSimple).isNull())
    {
      return nm->mkConst(false);
    }
    exp = Node::null();
    if (checkEq(n[0], n[1]))
    {
      // explanation is null
      return nm->mkConst(true);
    }
  }
  else if (n.getKind() == Kind::GEQ)
  {
    exp = nm->mkNode(Kind::SUB, n[0], n[1]);
    if (!findApprox(rewriteArith(exp), isSimple).isNull())
    {
      return nm->mkConst(true);
    }
    exp = nm->mkNode(Kind::SUB, nm->mkNode(Kind::SUB, n[1], n[0]), d_one);
    if (!findApprox(rewriteArith(exp), isSimple).isNull())
    {
      return nm->mkConst(false);
    }
    exp = Node::null();
  }
  return Node::null();
}

Node ArithEntail::rewriteArith(Node a)
{
  AlwaysAssert(a.getType().isInteger())
      << "Bad term: " << a << " " << a.getType();
  if (d_rr != nullptr)
  {
    return d_rr->rewrite(a);
  }
  else
  {
    a = rewriteLengthIntro(a);
  }
  // Otherwise, use the poly norm utility. This is important since the rewrite
  // must be justified by ARITH_POLY_NORM when in proof mode (when d_rr is
  // null).
  Node an = arith::PolyNorm::getPolyNorm(a);
  return an;
}

Node ArithEntail::normalizeGeq(const Node& n) const
{
  NodeManager* nm = n.getNodeManager();
  if (n.getNumChildren() != 2 || !n[0].getType().isInteger()
      || !n[1].getType().isInteger())
  {
    return Node::null();
  }
  switch (n.getKind())
  {
    case Kind::GEQ: return n;
    case Kind::LEQ: return nm->mkNode(Kind::GEQ, n[1], n[0]);
    case Kind::LT:
      return nm->mkNode(
          Kind::GEQ,
          n[1],
          nm->mkNode(Kind::ADD, n[0], nm->mkConstInt(Rational(1))));
    case Kind::GT:
      return nm->mkNode(
          Kind::GEQ,
          n[0],
          nm->mkNode(Kind::ADD, n[1], nm->mkConstInt(Rational(1))));
    default: break;
  }
  return Node::null();
}

Node ArithEntail::rewriteLengthIntro(const Node& n,
                                     TConvProofGenerator* pg) const
{
  NodeManager* nm = n.getNodeManager();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      if (cur.getNumChildren() == 0)
      {
        visit.pop_back();
        visited[cur] = cur;
        continue;
      }
      visited.emplace(cur, Node::null());
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    visit.pop_back();
    if (it->second.isNull())
    {
      Kind k = cur.getKind();
      bool childChanged = false;
      std::vector<Node> children;
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        children.push_back(it->second);
        childChanged = childChanged || it->second != cn;
      }
      Node ret = cur;
      if (childChanged)
      {
        ret = nm->mkNode(k, children);
      }
      if (k == Kind::STRING_LENGTH)
      {
        std::vector<Node> cc;
        for (const Node& c : children)
        {
          utils::getConcat(c, cc);
        }
        std::vector<Node> sum;
        for (const Node& c : cc)
        {
          if (c.isConst())
          {
            sum.push_back(nm->mkConstInt(Rational(Word::getLength(c))));
          }
          else
          {
            sum.push_back(nm->mkNode(Kind::STRING_LENGTH, c));
          }
        }
        Assert(!sum.empty());
        Node rret = sum.size() == 1 ? sum[0] : nm->mkNode(Kind::ADD, sum);
        if (pg != nullptr)
        {
          pg->addRewriteStep(ret,
                             rret,
                             nullptr,
                             false,
                             TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
        }
        ret = rret;
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

bool ArithEntail::checkEq(Node a, Node b)
{
  if (a == b)
  {
    return true;
  }
  Node ar = rewriteArith(a);
  Node br = rewriteArith(b);
  return ar == br;
}

bool ArithEntail::check(Node a, Node b, bool strict, bool isSimple)
{
  if (a == b)
  {
    return !strict;
  }
  Node diff = NodeManager::mkNode(Kind::SUB, a, b);
  return check(diff, strict, isSimple);
}

bool ArithEntail::check(Node a, bool strict, bool isSimple)
{
  if (a.isConst())
  {
    return a.getConst<Rational>().sgn() >= (strict ? 1 : 0);
  }
  Node ar = strict ? NodeManager::mkNode(Kind::SUB, a, d_one) : a;
  if (isSimple)
  {
    ar = arith::PolyNorm::getPolyNorm(ar);
    // if simple, just call the checkSimple routine.
    return checkSimple(ar);
  }
  else
  {
    // otherwise rewrite arith and find approximation
    ar = rewriteArith(ar);
  }
  Node ara = findApprox(ar, isSimple);
  return !ara.isNull();
}

Node ArithEntail::findApprox(Node ar, bool isSimple)
{
  std::map<Node, Node>& cache = isSimple ? d_approxCacheSimple : d_approxCache;
  std::map<Node, Node>::iterator it = cache.find(ar);
  if (it != cache.end())
  {
    return it->second;
  }
  Node ret;
  if (checkSimple(ar))
  {
    // didn't need approximation
    ret = ar;
  }
  else
  {
    ret = findApproxInternal(ar, isSimple);
  }
  cache[ar] = ret;
  return ret;
}

Node ArithEntail::findApproxInternal(Node ar, bool isSimple)
{
  // if not using recursive approximations, we always set isSimple to true
  if (!d_recApprox)
  {
    isSimple = true;
  }
  NodeManager* nm = ar.getNodeManager();
  std::map<Node, Node> msum;
  Trace("strings-ent-approx-debug")
      << "Setup arithmetic approximations for " << ar << std::endl;
  if (!ArithMSum::getMonomialSum(ar, msum))
  {
    Trace("strings-ent-approx-debug")
        << "...failed to get monomial sum!" << std::endl;
    return Node::null();
  }
  // for each monomial v*c, mApprox[v] a list of
  // possibilities for how the term can be soundly approximated, that is,
  // if mApprox[v] contains av, then v*c > av*c. Notice that if c
  // is positive, then v > av, otherwise if c is negative, then v < av.
  // In other words, av is an under-approximation if c is positive, and an
  // over-approximation if c is negative.
  bool changed = false;
  std::map<Node, std::vector<Node> > mApprox;
  // map from approximations to their monomial sums
  std::map<Node, std::map<Node, Node> > approxMsums;
  // aarSum stores each monomial that does not have multiple approximations
  std::vector<Node> aarSum;
  // stores the witness
  arith::ArithSubs approxMap;
  for (std::pair<const Node, Node>& m : msum)
  {
    Node v = m.first;
    Node c = m.second;
    Trace("strings-ent-approx-debug")
        << "Get approximations " << v << "..." << std::endl;
    if (v.isNull())
    {
      Node mn = c.isNull() ? nm->mkConstInt(Rational(1)) : c;
      aarSum.push_back(mn);
    }
    else
    {
      // c.isNull() means c = 1
      bool isOverApprox = !c.isNull() && c.getConst<Rational>().sgn() == -1;
      std::vector<Node>& approx = mApprox[v];
      std::unordered_set<Node> visited;
      std::vector<Node> toProcess;
      toProcess.push_back(v);
      do
      {
        Node curr = toProcess.back();
        Trace("strings-ent-approx-debug") << "  process " << curr << std::endl;
        curr = arith::PolyNorm::getPolyNorm(curr);
        toProcess.pop_back();
        if (visited.find(curr) == visited.end())
        {
          visited.insert(curr);
          std::vector<Node> currApprox;
          getArithApproximations(curr, currApprox, isOverApprox, isSimple);
          if (currApprox.empty())
          {
            Trace("strings-ent-approx-debug")
                << "...approximation: " << curr << std::endl;
            // no approximations, thus curr is a possibility
            approx.push_back(curr);
          }
          else if (isSimple)
          {
            // don't rewrite or re-approximate
            approx = currApprox;
          }
          else
          {
            toProcess.insert(
                toProcess.end(), currApprox.begin(), currApprox.end());
          }
        }
      } while (!toProcess.empty());
      Assert(!approx.empty());
      // if we have only one approximation, move it to final
      if (approx.size() == 1)
      {
        if (v != approx[0])
        {
          changed = true;
          Trace("strings-ent-approx")
              << "- Propagate (" << (d_rr == nullptr) << ", " << isSimple
              << ") " << v << " = " << approx[0] << std::endl;
          approxMap.add(v, approx[0]);
        }
        Node mn = ArithMSum::mkCoeffTerm(c, approx[0]);
        aarSum.push_back(mn);
        mApprox.erase(v);
      }
      else
      {
        // compute monomial sum form for each approximation, used below
        for (const Node& aa : approx)
        {
          if (approxMsums.find(aa) == approxMsums.end())
          {
            // ensure rewritten, which makes a difference if isSimple is true
            Node aar = arith::PolyNorm::getPolyNorm(aa);
            CVC5_UNUSED bool ret =
                ArithMSum::getMonomialSum(aar, approxMsums[aa]);
            Assert(ret) << "Could not find sum " << aa;
          }
        }
        changed = true;
      }
    }
  }
  if (!changed)
  {
    // approximations had no effect, return
    Trace("strings-ent-approx-debug") << "...no approximations" << std::endl;
    return Node::null();
  }
  // get the current "fixed" sum for the abstraction of ar
  Node aar =
      aarSum.empty()
          ? d_zero
          : (aarSum.size() == 1 ? aarSum[0] : nm->mkNode(Kind::ADD, aarSum));
  aar = arith::PolyNorm::getPolyNorm(aar);
  Trace("strings-ent-approx-debug")
      << "...processed fixed sum " << aar << " with " << mApprox.size()
      << " approximated monomials." << std::endl;
  // if we have a choice of how to approximate
  if (!mApprox.empty())
  {
    // convert aar back to monomial sum
    std::map<Node, Node> msumAar;
    if (!ArithMSum::getMonomialSum(aar, msumAar))
    {
      return Node::null();
    }
    if (TraceIsOn("strings-ent-approx"))
    {
      Trace("strings-ent-approx")
          << "---- Check arithmetic entailment by under-approximation " << ar
          << " >= 0" << std::endl;
      Trace("strings-ent-approx") << "FIXED:" << std::endl;
      ArithMSum::debugPrintMonomialSum(msumAar, "strings-ent-approx");
      Trace("strings-ent-approx") << "APPROX:" << std::endl;
      for (std::pair<const Node, std::vector<Node> >& a : mApprox)
      {
        Node c = msum[a.first];
        Trace("strings-ent-approx") << "  ";
        if (!c.isNull())
        {
          Trace("strings-ent-approx") << c << " * ";
        }
        Trace("strings-ent-approx")
            << a.second << " ...from " << a.first << std::endl;
      }
      Trace("strings-ent-approx") << std::endl;
    }
    Rational one(1);
    // incorporate monomials one at a time that have a choice of approximations
    while (!mApprox.empty())
    {
      Node v;
      Node vapprox;
      int maxScore = -1;
      // Look at each approximation, take the one with the best score.
      // Notice that we are in the process of trying to prove
      // ( c1*t1 + .. + cn*tn ) + ( approx_1 | ... | approx_m ) >= 0,
      // where c1*t1 + .. + cn*tn is the "fixed" component of our sum (aar)
      // and approx_1 ... approx_m are possible approximations. The
      // intution here is that we want coefficients c1...cn to be positive.
      // This is because arithmetic string terms t1...tn (which may be
      // applications of len, indexof, str.to.int) are never entailed to be
      // negative. Hence, we add the approx_i that contributes the "most"
      // towards making all constants c1...cn positive and cancelling negative
      // monomials in approx_i itself.
      for (std::pair<const Node, std::vector<Node> >& nam : mApprox)
      {
        Node cr = msum[nam.first];
        for (const Node& aa : nam.second)
        {
          unsigned helpsCancelCount = 0;
          unsigned addsObligationCount = 0;
          std::map<Node, Node>::iterator it;
          // we are processing an approximation cr*( c1*t1 + ... + cn*tn )
          for (std::pair<const Node, Node>& aam : approxMsums[aa])
          {
            // Say aar is of the form t + c*ti, and aam is the monomial ci*ti
            // where ci != 0. We say aam:
            // (1) helps cancel if c != 0 and c>0 != ci>0
            // (2) adds obligation if c>=0 and c+ci<0
            Node ti = aam.first;
            Node ci = aam.second;
            if (!cr.isNull())
            {
              ci = ci.isNull() ? cr
                               : nm->mkConstInt(cr.getConst<Rational>()
                                                * ci.getConst<Rational>());
            }
            Trace("strings-ent-approx-debug") << ci << "*" << ti << " ";
            int ciSgn = ci.isNull() ? 1 : ci.getConst<Rational>().sgn();
            it = msumAar.find(ti);
            if (it != msumAar.end())
            {
              Node c = it->second;
              int cSgn = c.isNull() ? 1 : c.getConst<Rational>().sgn();
              if (cSgn == 0)
              {
                addsObligationCount += (ciSgn == -1 ? 1 : 0);
              }
              else if (cSgn != ciSgn)
              {
                helpsCancelCount++;
                Rational r1 = c.isNull() ? one : c.getConst<Rational>();
                Rational r2 = ci.isNull() ? one : ci.getConst<Rational>();
                Rational r12 = r1 + r2;
                if (r12.sgn() == -1)
                {
                  addsObligationCount++;
                }
              }
            }
            else
            {
              addsObligationCount += (ciSgn == -1 ? 1 : 0);
            }
          }
          Trace("strings-ent-approx-debug")
              << "counts=" << helpsCancelCount << "," << addsObligationCount
              << " for " << aa << " into " << aar << std::endl;
          int score = (addsObligationCount > 0 ? 0 : 2)
                      + (helpsCancelCount > 0 ? 1 : 0);
          // if its the best, update v and vapprox
          if (v.isNull() || score > maxScore)
          {
            v = nam.first;
            vapprox = aa;
            maxScore = score;
          }
        }
        if (!v.isNull())
        {
          break;
        }
      }
      Trace("strings-ent-approx") << "- Decide (" << (d_rr == nullptr) << ") "
                                  << v << " = " << vapprox << std::endl;
      // we incorporate v approximated by vapprox into the overall approximation
      // for ar
      Assert(!v.isNull() && !vapprox.isNull());
      Assert(msum.find(v) != msum.end());
      Node mn = ArithMSum::mkCoeffTerm(msum[v], vapprox);
      aar = nm->mkNode(Kind::ADD, aar, mn);
      approxMap.add(v, vapprox);
      // update the msumAar map
      aar = arith::PolyNorm::getPolyNorm(aar);
      msumAar.clear();
      if (!ArithMSum::getMonomialSum(aar, msumAar))
      {
        Assert(false);
        Trace("strings-ent-approx")
            << "...failed to get monomial sum!" << std::endl;
        return Node::null();
      }
      // we have processed the approximation for v
      mApprox.erase(v);
    }
    Trace("strings-ent-approx") << "-----------------" << std::endl;
  }
  if (aar == ar)
  {
    Trace("strings-ent-approx-debug")
        << "...approximation had no effect" << std::endl;
    // this should never happen, but we avoid the infinite loop for sanity here
    Assert(false);
    return Node::null();
  }
  // Check entailment on the approximation of ar.
  // Notice that this may trigger further reasoning by approximation. For
  // example, len( replace( x ++ y, substr( x, 0, n ), z ) ) may be
  // under-approximated as len( x ) + len( y ) - len( substr( x, 0, n ) ) on
  // this call, where in the recursive call we may over-approximate
  // len( substr( x, 0, n ) ) as len( x ). In this example, we can infer
  // that len( replace( x ++ y, substr( x, 0, n ), z ) ) >= len( y ) in two
  // steps.
  if (check(aar, false, isSimple))
  {
    Trace("strings-ent-approx")
        << "*** StrArithApprox: showed " << ar
        << " >= 0 using under-approximation!" << std::endl;
    Trace("strings-ent-approx")
        << "*** StrArithApprox: rewritten was " << aar << std::endl;
    // Apply arithmetic substitution, which ensures we only replace terms
    // in the top-level arithmetic skeleton of ar.
    Node approx = approxMap.applyArith(ar);
    Trace("strings-ent-approx")
        << "*** StrArithApprox: under-approximation was " << approx
        << std::endl;
    return approx;
  }
  return Node::null();
}

void ArithEntail::getArithApproximations(Node a,
                                         std::vector<Node>& approx,
                                         bool isOverApprox,
                                         bool isSimple)
{
  NodeManager* nm = a.getNodeManager();
  // We do not handle ADD here since this leads to exponential behavior.
  // Instead, this is managed, e.g. during checkApprox, where
  // ADD terms are expanded "on-demand" during the reasoning.
  Trace("strings-ent-approx-debug")
      << "Get arith approximations " << a << std::endl;
  Kind ak = a.getKind();
  if (ak == Kind::MULT)
  {
    Node c;
    Node v;
    if (ArithMSum::getMonomial(a, c, v))
    {
      bool isNeg = c.getConst<Rational>().sgn() == -1;
      getArithApproximations(
          v, approx, isNeg ? !isOverApprox : isOverApprox, isSimple);
      for (unsigned i = 0, size = approx.size(); i < size; i++)
      {
        approx[i] = nm->mkNode(Kind::MULT, c, approx[i]);
      }
    }
  }
  else if (ak == Kind::STRING_LENGTH)
  {
    Kind aak = a[0].getKind();
    if (aak == Kind::STRING_SUBSTR)
    {
      // over,under-approximations for len( substr( x, n, m ) )
      Node lenx = nm->mkNode(Kind::STRING_LENGTH, a[0][0]);
      if (isOverApprox)
      {
        // m >= 0 implies
        //  m >= len( substr( x, n, m ) )
        if (check(a[0][2], false, isSimple))
        {
          approx.push_back(a[0][2]);
        }
        if (check(lenx, a[0][1], false, isSimple))
        {
          // n <= len( x ) implies
          //   len( x ) - n >= len( substr( x, n, m ) )
          approx.push_back(nm->mkNode(Kind::SUB, lenx, a[0][1]));
        }
        else
        {
          // len( x ) >= len( substr( x, n, m ) )
          approx.push_back(lenx);
        }
      }
      else
      {
        // 0 <= n and n+m <= len( x ) implies
        //   m <= len( substr( x, n, m ) )
        Node npm = nm->mkNode(Kind::ADD, a[0][1], a[0][2]);
        if (check(a[0][1], false, isSimple)
            && check(lenx, npm, false, isSimple))
        {
          approx.push_back(a[0][2]);
        }
        // 0 <= n and n+m >= len( x ) implies
        //   len(x)-n <= len( substr( x, n, m ) )
        if (check(a[0][1], false, isSimple)
            && check(npm, lenx, false, isSimple))
        {
          approx.push_back(nm->mkNode(Kind::SUB, lenx, a[0][1]));
        }
      }
    }
    else if (aak == Kind::STRING_REPLACE)
    {
      // over,under-approximations for len( replace( x, y, z ) )
      // notice this is either len( x ) or ( len( x ) + len( z ) - len( y ) )
      Node lenx = nm->mkNode(Kind::STRING_LENGTH, a[0][0]);
      Node leny = nm->mkNode(Kind::STRING_LENGTH, a[0][1]);
      Node lenz = nm->mkNode(Kind::STRING_LENGTH, a[0][2]);
      if (isOverApprox)
      {
        if (check(leny, lenz, false, isSimple))
        {
          // len( y ) >= len( z ) implies
          //   len( x ) >= len( replace( x, y, z ) )
          approx.push_back(lenx);
        }
        else
        {
          // len( x ) + len( z ) >= len( replace( x, y, z ) )
          approx.push_back(nm->mkNode(Kind::ADD, lenx, lenz));
        }
      }
      else
      {
        if (check(lenz, leny, false, isSimple)
            || check(lenz, lenx, false, isSimple))
        {
          // len( y ) <= len( z ) or len( x ) <= len( z ) implies
          //   len( x ) <= len( replace( x, y, z ) )
          approx.push_back(lenx);
        }
        else
        {
          // len( x ) - len( y ) <= len( replace( x, y, z ) )
          approx.push_back(nm->mkNode(Kind::SUB, lenx, leny));
        }
      }
    }
    else if (aak == Kind::STRING_ITOS)
    {
      // over,under-approximations for len( int.to.str( x ) )
      if (isOverApprox)
      {
        if (check(a[0][0], false, isSimple))
        {
          if (check(a[0][0], true, isSimple))
          {
            // x > 0 implies
            //   x >= len( int.to.str( x ) )
            approx.push_back(a[0][0]);
          }
          else
          {
            // x >= 0 implies
            //   x+1 >= len( int.to.str( x ) )
            approx.push_back(
                nm->mkNode(Kind::ADD, nm->mkConstInt(Rational(1)), a[0][0]));
          }
        }
      }
      else
      {
        if (check(a[0][0], false, isSimple))
        {
          // x >= 0 implies
          //   len( int.to.str( x ) ) >= 1
          approx.push_back(nm->mkConstInt(Rational(1)));
        }
        // other crazy things are possible here, e.g.
        // len( int.to.str( len( y ) + 10 ) ) >= 2
      }
    }
  }
  else if (ak == Kind::STRING_INDEXOF)
  {
    // over,under-approximations for indexof( x, y, n )
    if (isOverApprox)
    {
      Node lenx = nm->mkNode(Kind::STRING_LENGTH, a[0]);
      Node leny = nm->mkNode(Kind::STRING_LENGTH, a[1]);
      if (check(lenx, leny, false, isSimple))
      {
        // len( x ) >= len( y ) implies
        //   len( x ) - len( y ) >= indexof( x, y, n )
        approx.push_back(nm->mkNode(Kind::SUB, lenx, leny));
      }
      else
      {
        // len( x ) >= indexof( x, y, n )
        approx.push_back(lenx);
      }
    }
    else
    {
      // TODO?:
      // contains( substr( x, n, len( x ) ), y ) implies
      //   n <= indexof( x, y, n )
      // ...hard to test, runs risk of non-termination

      // -1 <= indexof( x, y, n )
      approx.push_back(nm->mkConstInt(Rational(-1)));
    }
  }
  else if (ak == Kind::STRING_STOI)
  {
    // over,under-approximations for str.to.int( x )
    if (isOverApprox)
    {
      // TODO?:
      // y >= 0 implies
      //   y >= str.to.int( int.to.str( y ) )
    }
    else
    {
      // -1 <= str.to.int( x )
      approx.push_back(nm->mkConstInt(Rational(-1)));
    }
  }
  Trace("strings-ent-approx-debug")
      << "Return " << approx.size() << " approximations" << std::endl;
}

bool ArithEntail::checkWithEqAssumption(Node assumption, Node a, bool strict)
{
  Assert(assumption.getKind() == Kind::EQUAL);
  Trace("strings-entail") << "checkWithEqAssumption: " << assumption << " " << a
                          << ", strict=" << strict << std::endl;

  // Find candidates variables to compute substitutions for
  std::unordered_set<Node> candVars;
  std::vector<Node> toVisit = {assumption};
  while (!toVisit.empty())
  {
    Node curr = toVisit.back();
    toVisit.pop_back();

    if (curr.getKind() == Kind::ADD || curr.getKind() == Kind::MULT
        || curr.getKind() == Kind::SUB || curr.getKind() == Kind::EQUAL)
    {
      for (const auto& currChild : curr)
      {
        toVisit.push_back(currChild);
      }
    }
    else if (curr.isVar() && Theory::theoryOf(curr) == THEORY_ARITH)
    {
      candVars.insert(curr);
    }
    else if (curr.getKind() == Kind::STRING_LENGTH)
    {
      candVars.insert(curr);
    }
  }

  // Check if any of the candidate variables are in n
  Node v;
  Assert(toVisit.empty());
  toVisit.push_back(a);
  while (!toVisit.empty())
  {
    Node curr = toVisit.back();
    toVisit.pop_back();

    for (const auto& currChild : curr)
    {
      toVisit.push_back(currChild);
    }

    if (candVars.find(curr) != candVars.end())
    {
      v = curr;
      break;
    }
  }

  if (v.isNull())
  {
    // No suitable candidate found
    return false;
  }

  Node solution = ArithMSum::solveEqualityFor(assumption, v);
  if (solution.isNull())
  {
    // Could not solve for v
    return false;
  }
  Trace("strings-entail") << "checkWithEqAssumption: subs " << v << " -> "
                          << solution << std::endl;

  TNode tv = v;
  TNode tsolution = solution;
  a = a.substitute(tv, tsolution);
  return check(a, strict);
}

bool ArithEntail::checkWithAssumption(Node assumption,
                                      Node a,
                                      Node b,
                                      bool strict)
{
  NodeManager* nm = assumption.getNodeManager();

  if (!assumption.isConst() && assumption.getKind() != Kind::EQUAL)
  {
    // We rewrite inequality assumptions from x <= y to x + (str.len s) = y
    // where s is some fresh string variable. We use (str.len s) because
    // (str.len s) must be non-negative for the equation to hold.
    Node x, y;
    if (assumption.getKind() == Kind::GEQ)
    {
      x = assumption[0];
      y = assumption[1];
    }
    else
    {
      // (not (>= s t)) --> (>= (t - 1) s)
      Assert(assumption.getKind() == Kind::NOT
             && assumption[0].getKind() == Kind::GEQ);
      x = nm->mkNode(Kind::SUB, assumption[0][1], nm->mkConstInt(Rational(1)));
      y = assumption[0][0];
    }

    Node s = NodeManager::mkBoundVar("slackVal", nm->stringType());
    Node slen = nm->mkNode(Kind::STRING_LENGTH, s);
    Node sleny = nm->mkNode(Kind::ADD, y, slen);
    Node rr = rewriteArith(nm->mkNode(Kind::SUB, x, sleny));
    if (rr.isConst())
    {
      assumption = nm->mkConst(rr.getConst<Rational>().sgn() == 0);
    }
    else
    {
      assumption = nm->mkNode(Kind::EQUAL, x, sleny);
    }
  }

  Node diff = nm->mkNode(Kind::SUB, a, b);
  bool res = false;
  if (assumption.isConst())
  {
    bool assumptionBool = assumption.getConst<bool>();
    if (assumptionBool)
    {
      res = check(diff, strict);
    }
    else
    {
      res = true;
    }
  }
  else
  {
    res = checkWithEqAssumption(assumption, diff, strict);
  }
  return res;
}

bool ArithEntail::checkWithAssumptions(std::vector<Node> assumptions,
                                       Node a,
                                       Node b,
                                       bool strict)
{
  // TODO: We currently try to show the entailment with each assumption
  // independently. In the future, we should make better use of multiple
  // assumptions.
  bool res = false;
  for (const auto& assumption : assumptions)
  {
    if (checkWithAssumption(assumption, a, b, strict))
    {
      res = true;
      break;
    }
  }
  return res;
}

struct ArithEntailConstantBoundLowerId
{
};
typedef expr::Attribute<ArithEntailConstantBoundLowerId, Node>
    ArithEntailConstantBoundLower;

struct ArithEntailConstantBoundUpperId
{
};
typedef expr::Attribute<ArithEntailConstantBoundUpperId, Node>
    ArithEntailConstantBoundUpper;

void ArithEntail::setConstantBoundCache(TNode n, Node ret, bool isLower)
{
  if (isLower)
  {
    ArithEntailConstantBoundLower acbl;
    n.setAttribute(acbl, ret);
  }
  else
  {
    ArithEntailConstantBoundUpper acbu;
    n.setAttribute(acbu, ret);
  }
}

bool ArithEntail::getConstantBoundCache(TNode n, bool isLower, Node& c)
{
  if (isLower)
  {
    ArithEntailConstantBoundLower acbl;
    if (n.hasAttribute(acbl))
    {
      c = n.getAttribute(acbl);
      return true;
    }
  }
  else
  {
    ArithEntailConstantBoundUpper acbu;
    if (n.hasAttribute(acbu))
    {
      c = n.getAttribute(acbu);
      return true;
    }
  }
  return false;
}

Node ArithEntail::getConstantBound(TNode a, bool isLower)
{
  Assert(rewriteArith(a) == a);
  Node ret;
  if (getConstantBoundCache(a, isLower, ret))
  {
    return ret;
  }
  if (a.isConst())
  {
    ret = a;
  }
  else if (a.getKind() == Kind::STRING_LENGTH)
  {
    if (isLower)
    {
      ret = d_zero;
    }
  }
  else if (a.getKind() == Kind::ADD || a.getKind() == Kind::MULT)
  {
    std::vector<Node> children;
    bool success = true;
    for (unsigned i = 0; i < a.getNumChildren(); i++)
    {
      Node ac = getConstantBound(a[i], isLower);
      if (ac.isNull())
      {
        success = false;
        break;
      }
      else
      {
        if (ac.getConst<Rational>().sgn() == 0)
        {
          if (a.getKind() == Kind::MULT)
          {
            success = false;
            break;
          }
        }
        else
        {
          if (a.getKind() == Kind::MULT)
          {
            if ((ac.getConst<Rational>().sgn() > 0) != isLower)
            {
              success = false;
              break;
            }
          }
          children.push_back(ac);
        }
      }
    }
    if (success)
    {
      if (children.empty())
      {
        ret = d_zero;
      }
      else if (children.size() == 1)
      {
        ret = children[0];
      }
      else
      {
        ret = a.getNodeManager()->mkNode(a.getKind(), children);
        ret = rewriteArith(ret);
      }
    }
  }
  Trace("strings-rewrite-cbound")
      << "Constant " << (isLower ? "lower" : "upper") << " bound for " << a
      << " is " << ret << std::endl;
  Assert(ret.isNull() || ret.isConst());
  // entailment check should be at least as powerful as computing a lower bound
  Assert(!isLower || ret.isNull() || ret.getConst<Rational>().sgn() < 0
         || check(a, false));
  Assert(!isLower || ret.isNull() || ret.getConst<Rational>().sgn() <= 0
         || check(a, true));
  // cache
  setConstantBoundCache(a, ret, isLower);
  return ret;
}

Node ArithEntail::getConstantBoundLength(TNode s, bool isLower) const
{
  Assert(s.getType().isStringLike());
  Node ret;
  if (getConstantBoundCache(s, isLower, ret))
  {
    return ret;
  }
  NodeManager* nm = s.getNodeManager();
  Kind sk = s.getKind();
  if (s.isConst())
  {
    size_t len = Word::getLength(s);
    ret = nm->mkConstInt(Rational(len));
  }
  else if (sk == Kind::SEQ_UNIT || sk == Kind::STRING_UNIT)
  {
    ret = nm->mkConstInt(1);
  }
  else if (sk == Kind::STRING_CONCAT)
  {
    Rational sum(0);
    bool success = true;
    for (const Node& sc : s)
    {
      Node b = getConstantBoundLength(sc, isLower);
      if (b.isNull())
      {
        if (isLower)
        {
          // assume zero and continue
          continue;
        }
        success = false;
        break;
      }
      Assert(b.isConst());
      sum = sum + b.getConst<Rational>();
    }
    if (success && (!isLower || sum.sgn() != 0))
    {
      ret = nm->mkConstInt(sum);
    }
  }
  if (ret.isNull() && isLower)
  {
    ret = d_zero;
  }
  // cache
  setConstantBoundCache(s, ret, isLower);
  return ret;
}

bool ArithEntail::checkSimple(Node a)
{
  // check whether a >= 0
  if (a.isConst())
  {
    return a.getConst<Rational>().sgn() >= 0;
  }
  else if (a.getKind() == Kind::STRING_LENGTH)
  {
    // str.len( t ) >= 0
    return true;
  }
  else if (a.getKind() == Kind::ADD || a.getKind() == Kind::MULT)
  {
    for (unsigned i = 0; i < a.getNumChildren(); i++)
    {
      if (!checkSimple(a[i]))
      {
        return false;
      }
    }
    // t1 >= 0 ^ ... ^ tn >= 0 => t1 op ... op tn >= 0
    return true;
  }

  return false;
}

bool ArithEntail::inferZerosInSumGeq(Node x,
                                     std::vector<Node>& ys,
                                     std::vector<Node>& zeroYs)
{
  Assert(zeroYs.empty());

  NodeManager* nm = x.getNodeManager();

  // Check if we can show that y1 + ... + yn >= x
  Node sum = (ys.size() > 1) ? nm->mkNode(Kind::ADD, ys) : ys[0];
  if (!check(sum, x))
  {
    return false;
  }

  // Try to remove yi one-by-one and check if we can still show:
  //
  // y1 + ... + yi-1 +  yi+1 + ... + yn >= x
  //
  // If that's the case, we know that yi can be zero and the inequality still
  // holds.
  size_t i = 0;
  while (i < ys.size())
  {
    Node yi = ys[i];
    std::vector<Node>::iterator pos = ys.erase(ys.begin() + i);
    if (ys.size() > 1)
    {
      sum = nm->mkNode(Kind::ADD, ys);
    }
    else
    {
      sum = ys.size() == 1 ? ys[0] : d_zero;
    }

    if (check(sum, x))
    {
      zeroYs.push_back(yi);
    }
    else
    {
      ys.insert(pos, yi);
      i++;
    }
  }
  return true;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
