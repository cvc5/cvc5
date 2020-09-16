/*********************                                                        */
/*! \file arith_entail.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of arithmetic entailment computation for string terms.
 **/

#include "theory/strings/arith_entail.h"

#include "expr/attribute.h"
#include "theory/arith/arith_msum.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "theory/theory.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

bool ArithEntail::checkEq(Node a, Node b)
{
  if (a == b)
  {
    return true;
  }
  Node ar = Rewriter::rewrite(a);
  Node br = Rewriter::rewrite(b);
  return ar == br;
}

bool ArithEntail::check(Node a, Node b, bool strict)
{
  if (a == b)
  {
    return !strict;
  }
  Node diff = NodeManager::currentNM()->mkNode(kind::MINUS, a, b);
  return check(diff, strict);
}

struct StrCheckEntailArithTag
{
};
struct StrCheckEntailArithComputedTag
{
};
/** Attribute true for expressions for which check returned true */
typedef expr::Attribute<StrCheckEntailArithTag, bool> StrCheckEntailArithAttr;
typedef expr::Attribute<StrCheckEntailArithComputedTag, bool>
    StrCheckEntailArithComputedAttr;

bool ArithEntail::check(Node a, bool strict)
{
  if (a.isConst())
  {
    return a.getConst<Rational>().sgn() >= (strict ? 1 : 0);
  }

  Node ar = strict ? NodeManager::currentNM()->mkNode(
                kind::MINUS, a, NodeManager::currentNM()->mkConst(Rational(1)))
                   : a;
  ar = Rewriter::rewrite(ar);

  if (ar.getAttribute(StrCheckEntailArithComputedAttr()))
  {
    return ar.getAttribute(StrCheckEntailArithAttr());
  }

  bool ret = checkInternal(ar);
  if (!ret)
  {
    // try with approximations
    ret = checkApprox(ar);
  }
  // cache the result
  ar.setAttribute(StrCheckEntailArithAttr(), ret);
  ar.setAttribute(StrCheckEntailArithComputedAttr(), true);
  return ret;
}

bool ArithEntail::checkApprox(Node ar)
{
  Assert(Rewriter::rewrite(ar) == ar);
  NodeManager* nm = NodeManager::currentNM();
  std::map<Node, Node> msum;
  Trace("strings-ent-approx-debug")
      << "Setup arithmetic approximations for " << ar << std::endl;
  if (!ArithMSum::getMonomialSum(ar, msum))
  {
    Trace("strings-ent-approx-debug")
        << "...failed to get monomial sum!" << std::endl;
    return false;
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
  for (std::pair<const Node, Node>& m : msum)
  {
    Node v = m.first;
    Node c = m.second;
    Trace("strings-ent-approx-debug")
        << "Get approximations " << v << "..." << std::endl;
    if (v.isNull())
    {
      Node mn = c.isNull() ? nm->mkConst(Rational(1)) : c;
      aarSum.push_back(mn);
    }
    else
    {
      // c.isNull() means c = 1
      bool isOverApprox = !c.isNull() && c.getConst<Rational>().sgn() == -1;
      std::vector<Node>& approx = mApprox[v];
      std::unordered_set<Node, NodeHashFunction> visited;
      std::vector<Node> toProcess;
      toProcess.push_back(v);
      do
      {
        Node curr = toProcess.back();
        Trace("strings-ent-approx-debug") << "  process " << curr << std::endl;
        curr = Rewriter::rewrite(curr);
        toProcess.pop_back();
        if (visited.find(curr) == visited.end())
        {
          visited.insert(curr);
          std::vector<Node> currApprox;
          getArithApproximations(curr, currApprox, isOverApprox);
          if (currApprox.empty())
          {
            Trace("strings-ent-approx-debug")
                << "...approximation: " << curr << std::endl;
            // no approximations, thus curr is a possibility
            approx.push_back(curr);
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
        changed = v != approx[0];
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
            CVC4_UNUSED bool ret =
                ArithMSum::getMonomialSum(aa, approxMsums[aa]);
            Assert(ret);
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
    return false;
  }
  // get the current "fixed" sum for the abstraction of ar
  Node aar = aarSum.empty()
                 ? nm->mkConst(Rational(0))
                 : (aarSum.size() == 1 ? aarSum[0] : nm->mkNode(PLUS, aarSum));
  aar = Rewriter::rewrite(aar);
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
      return false;
    }
    if (Trace.isOn("strings-ent-approx"))
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
                               : Rewriter::rewrite(nm->mkNode(MULT, ci, cr));
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
      Trace("strings-ent-approx")
          << "- Decide " << v << " = " << vapprox << std::endl;
      // we incorporate v approximated by vapprox into the overall approximation
      // for ar
      Assert(!v.isNull() && !vapprox.isNull());
      Assert(msum.find(v) != msum.end());
      Node mn = ArithMSum::mkCoeffTerm(msum[v], vapprox);
      aar = nm->mkNode(PLUS, aar, mn);
      // update the msumAar map
      aar = Rewriter::rewrite(aar);
      msumAar.clear();
      if (!ArithMSum::getMonomialSum(aar, msumAar))
      {
        Assert(false);
        Trace("strings-ent-approx")
            << "...failed to get monomial sum!" << std::endl;
        return false;
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
    return false;
  }
  // Check entailment on the approximation of ar.
  // Notice that this may trigger further reasoning by approximation. For
  // example, len( replace( x ++ y, substr( x, 0, n ), z ) ) may be
  // under-approximated as len( x ) + len( y ) - len( substr( x, 0, n ) ) on
  // this call, where in the recursive call we may over-approximate
  // len( substr( x, 0, n ) ) as len( x ). In this example, we can infer
  // that len( replace( x ++ y, substr( x, 0, n ), z ) ) >= len( y ) in two
  // steps.
  if (check(aar))
  {
    Trace("strings-ent-approx")
        << "*** StrArithApprox: showed " << ar
        << " >= 0 using under-approximation!" << std::endl;
    Trace("strings-ent-approx")
        << "*** StrArithApprox: under-approximation was " << aar << std::endl;
    return true;
  }
  return false;
}

void ArithEntail::getArithApproximations(Node a,
                                         std::vector<Node>& approx,
                                         bool isOverApprox)
{
  NodeManager* nm = NodeManager::currentNM();
  // We do not handle PLUS here since this leads to exponential behavior.
  // Instead, this is managed, e.g. during checkApprox, where
  // PLUS terms are expanded "on-demand" during the reasoning.
  Trace("strings-ent-approx-debug")
      << "Get arith approximations " << a << std::endl;
  Kind ak = a.getKind();
  if (ak == MULT)
  {
    Node c;
    Node v;
    if (ArithMSum::getMonomial(a, c, v))
    {
      bool isNeg = c.getConst<Rational>().sgn() == -1;
      getArithApproximations(v, approx, isNeg ? !isOverApprox : isOverApprox);
      for (unsigned i = 0, size = approx.size(); i < size; i++)
      {
        approx[i] = nm->mkNode(MULT, c, approx[i]);
      }
    }
  }
  else if (ak == STRING_LENGTH)
  {
    Kind aak = a[0].getKind();
    if (aak == STRING_SUBSTR)
    {
      // over,under-approximations for len( substr( x, n, m ) )
      Node lenx = nm->mkNode(STRING_LENGTH, a[0][0]);
      if (isOverApprox)
      {
        // m >= 0 implies
        //  m >= len( substr( x, n, m ) )
        if (check(a[0][2]))
        {
          approx.push_back(a[0][2]);
        }
        if (check(lenx, a[0][1]))
        {
          // n <= len( x ) implies
          //   len( x ) - n >= len( substr( x, n, m ) )
          approx.push_back(nm->mkNode(MINUS, lenx, a[0][1]));
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
        Node npm = nm->mkNode(PLUS, a[0][1], a[0][2]);
        if (check(a[0][1]) && check(lenx, npm))
        {
          approx.push_back(a[0][2]);
        }
        // 0 <= n and n+m >= len( x ) implies
        //   len(x)-n <= len( substr( x, n, m ) )
        if (check(a[0][1]) && check(npm, lenx))
        {
          approx.push_back(nm->mkNode(MINUS, lenx, a[0][1]));
        }
      }
    }
    else if (aak == STRING_STRREPL)
    {
      // over,under-approximations for len( replace( x, y, z ) )
      // notice this is either len( x ) or ( len( x ) + len( z ) - len( y ) )
      Node lenx = nm->mkNode(STRING_LENGTH, a[0][0]);
      Node leny = nm->mkNode(STRING_LENGTH, a[0][1]);
      Node lenz = nm->mkNode(STRING_LENGTH, a[0][2]);
      if (isOverApprox)
      {
        if (check(leny, lenz))
        {
          // len( y ) >= len( z ) implies
          //   len( x ) >= len( replace( x, y, z ) )
          approx.push_back(lenx);
        }
        else
        {
          // len( x ) + len( z ) >= len( replace( x, y, z ) )
          approx.push_back(nm->mkNode(PLUS, lenx, lenz));
        }
      }
      else
      {
        if (check(lenz, leny) || check(lenz, lenx))
        {
          // len( y ) <= len( z ) or len( x ) <= len( z ) implies
          //   len( x ) <= len( replace( x, y, z ) )
          approx.push_back(lenx);
        }
        else
        {
          // len( x ) - len( y ) <= len( replace( x, y, z ) )
          approx.push_back(nm->mkNode(MINUS, lenx, leny));
        }
      }
    }
    else if (aak == STRING_ITOS)
    {
      // over,under-approximations for len( int.to.str( x ) )
      if (isOverApprox)
      {
        if (check(a[0][0], false))
        {
          if (check(a[0][0], true))
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
                nm->mkNode(PLUS, nm->mkConst(Rational(1)), a[0][0]));
          }
        }
      }
      else
      {
        if (check(a[0][0]))
        {
          // x >= 0 implies
          //   len( int.to.str( x ) ) >= 1
          approx.push_back(nm->mkConst(Rational(1)));
        }
        // other crazy things are possible here, e.g.
        // len( int.to.str( len( y ) + 10 ) ) >= 2
      }
    }
  }
  else if (ak == STRING_STRIDOF)
  {
    // over,under-approximations for indexof( x, y, n )
    if (isOverApprox)
    {
      Node lenx = nm->mkNode(STRING_LENGTH, a[0]);
      Node leny = nm->mkNode(STRING_LENGTH, a[1]);
      if (check(lenx, leny))
      {
        // len( x ) >= len( y ) implies
        //   len( x ) - len( y ) >= indexof( x, y, n )
        approx.push_back(nm->mkNode(MINUS, lenx, leny));
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
      approx.push_back(nm->mkConst(Rational(-1)));
    }
  }
  else if (ak == STRING_STOI)
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
      approx.push_back(nm->mkConst(Rational(-1)));
    }
  }
  Trace("strings-ent-approx-debug") << "Return " << approx.size() << std::endl;
}

bool ArithEntail::checkWithEqAssumption(Node assumption, Node a, bool strict)
{
  Assert(assumption.getKind() == kind::EQUAL);
  Assert(Rewriter::rewrite(assumption) == assumption);

  // Find candidates variables to compute substitutions for
  std::unordered_set<Node, NodeHashFunction> candVars;
  std::vector<Node> toVisit = {assumption};
  while (!toVisit.empty())
  {
    Node curr = toVisit.back();
    toVisit.pop_back();

    if (curr.getKind() == kind::PLUS || curr.getKind() == kind::MULT
        || curr.getKind() == kind::MINUS || curr.getKind() == kind::EQUAL)
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
    else if (curr.getKind() == kind::STRING_LENGTH)
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

  a = a.substitute(TNode(v), TNode(solution));
  return check(a, strict);
}

bool ArithEntail::checkWithAssumption(Node assumption,
                                      Node a,
                                      Node b,
                                      bool strict)
{
  Assert(Rewriter::rewrite(assumption) == assumption);

  NodeManager* nm = NodeManager::currentNM();

  if (!assumption.isConst() && assumption.getKind() != kind::EQUAL)
  {
    // We rewrite inequality assumptions from x <= y to x + (str.len s) = y
    // where s is some fresh string variable. We use (str.len s) because
    // (str.len s) must be non-negative for the equation to hold.
    Node x, y;
    if (assumption.getKind() == kind::GEQ)
    {
      x = assumption[0];
      y = assumption[1];
    }
    else
    {
      // (not (>= s t)) --> (>= (t - 1) s)
      Assert(assumption.getKind() == kind::NOT
             && assumption[0].getKind() == kind::GEQ);
      x = nm->mkNode(kind::MINUS, assumption[0][1], nm->mkConst(Rational(1)));
      y = assumption[0][0];
    }

    Node s = nm->mkBoundVar("slackVal", nm->stringType());
    Node slen = nm->mkNode(kind::STRING_LENGTH, s);
    assumption = Rewriter::rewrite(
        nm->mkNode(kind::EQUAL, x, nm->mkNode(kind::PLUS, y, slen)));
  }

  Node diff = nm->mkNode(kind::MINUS, a, b);
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
    Assert(Rewriter::rewrite(assumption) == assumption);

    if (checkWithAssumption(assumption, a, b, strict))
    {
      res = true;
      break;
    }
  }
  return res;
}

Node ArithEntail::getConstantBound(Node a, bool isLower)
{
  Assert(Rewriter::rewrite(a) == a);
  Node ret;
  if (a.isConst())
  {
    ret = a;
  }
  else if (a.getKind() == kind::STRING_LENGTH)
  {
    if (isLower)
    {
      ret = NodeManager::currentNM()->mkConst(Rational(0));
    }
  }
  else if (a.getKind() == kind::PLUS || a.getKind() == kind::MULT)
  {
    std::vector<Node> children;
    bool success = true;
    for (unsigned i = 0; i < a.getNumChildren(); i++)
    {
      Node ac = getConstantBound(a[i], isLower);
      if (ac.isNull())
      {
        ret = ac;
        success = false;
        break;
      }
      else
      {
        if (ac.getConst<Rational>().sgn() == 0)
        {
          if (a.getKind() == kind::MULT)
          {
            ret = ac;
            success = false;
            break;
          }
        }
        else
        {
          if (a.getKind() == kind::MULT)
          {
            if ((ac.getConst<Rational>().sgn() > 0) != isLower)
            {
              ret = Node::null();
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
        ret = NodeManager::currentNM()->mkConst(Rational(0));
      }
      else if (children.size() == 1)
      {
        ret = children[0];
      }
      else
      {
        ret = NodeManager::currentNM()->mkNode(a.getKind(), children);
        ret = Rewriter::rewrite(ret);
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
  return ret;
}

bool ArithEntail::checkInternal(Node a)
{
  Assert(Rewriter::rewrite(a) == a);
  // check whether a >= 0
  if (a.isConst())
  {
    return a.getConst<Rational>().sgn() >= 0;
  }
  else if (a.getKind() == kind::STRING_LENGTH)
  {
    // str.len( t ) >= 0
    return true;
  }
  else if (a.getKind() == kind::PLUS || a.getKind() == kind::MULT)
  {
    for (unsigned i = 0; i < a.getNumChildren(); i++)
    {
      if (!checkInternal(a[i]))
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

  NodeManager* nm = NodeManager::currentNM();

  // Check if we can show that y1 + ... + yn >= x
  Node sum = (ys.size() > 1) ? nm->mkNode(PLUS, ys) : ys[0];
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
      sum = nm->mkNode(PLUS, ys);
    }
    else
    {
      sum = ys.size() == 1 ? ys[0] : nm->mkConst(Rational(0));
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
}  // namespace CVC4
