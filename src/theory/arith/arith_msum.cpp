/*********************                                                        */
/*! \file arith_msum.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of arith_msum
 **/

#include "theory/arith/arith_msum.h"

#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

bool ArithMSum::getMonomial(Node n, Node& c, Node& v)
{
  if (n.getKind() == MULT && n.getNumChildren() == 2 && n[0].isConst())
  {
    c = n[0];
    v = n[1];
    return true;
  }
  return false;
}

bool ArithMSum::getMonomial(Node n, std::map<Node, Node>& msum)
{
  if (n.isConst())
  {
    if (msum.find(Node::null()) == msum.end())
    {
      msum[Node::null()] = n;
      return true;
    }
  }
  else if (n.getKind() == MULT && n.getNumChildren() == 2 && n[0].isConst())
  {
    if (msum.find(n[1]) == msum.end())
    {
      msum[n[1]] = n[0];
      return true;
    }
  }
  else
  {
    if (msum.find(n) == msum.end())
    {
      msum[n] = Node::null();
      return true;
    }
  }
  return false;
}

bool ArithMSum::getMonomialSum(Node n, std::map<Node, Node>& msum)
{
  if (n.getKind() == PLUS)
  {
    for (Node nc : n)
    {
      if (!getMonomial(nc, msum))
      {
        return false;
      }
    }
    return true;
  }
  return getMonomial(n, msum);
}

bool ArithMSum::getMonomialSumLit(Node lit, std::map<Node, Node>& msum)
{
  if (lit.getKind() == GEQ || lit.getKind() == EQUAL)
  {
    if (getMonomialSum(lit[0], msum))
    {
      if (lit[1].isConst() && lit[1].getConst<Rational>().isZero())
      {
        return true;
      }
      else
      {
        // subtract the other side
        std::map<Node, Node> msum2;
        NodeManager* nm = NodeManager::currentNM();
        if (getMonomialSum(lit[1], msum2))
        {
          for (std::map<Node, Node>::iterator it = msum2.begin();
               it != msum2.end();
               ++it)
          {
            std::map<Node, Node>::iterator it2 = msum.find(it->first);
            if (it2 != msum.end())
            {
              Node r = nm->mkNode(
                  MINUS,
                  it2->second.isNull() ? nm->mkConst(Rational(1)) : it2->second,
                  it->second.isNull() ? nm->mkConst(Rational(1)) : it->second);
              msum[it->first] = Rewriter::rewrite(r);
            }
            else
            {
              msum[it->first] = it->second.isNull() ? nm->mkConst(Rational(-1))
                                                    : negate(it->second);
            }
          }
          return true;
        }
      }
    }
  }
  return false;
}

Node ArithMSum::mkNode(const std::map<Node, Node>& msum)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> children;
  for (std::map<Node, Node>::const_iterator it = msum.begin(); it != msum.end();
       ++it)
  {
    Node m;
    if (!it->first.isNull())
    {
      m = mkCoeffTerm(it->second, it->first);
    }
    else
    {
      Assert(!it->second.isNull());
      m = it->second;
    }
    children.push_back(m);
  }
  return children.size() > 1
             ? nm->mkNode(PLUS, children)
             : (children.size() == 1 ? children[0] : nm->mkConst(Rational(0)));
}

int ArithMSum::isolate(
    Node v, const std::map<Node, Node>& msum, Node& veq_c, Node& val, Kind k)
{
  Assert(veq_c.isNull());
  std::map<Node, Node>::const_iterator itv = msum.find(v);
  if (itv != msum.end())
  {
    std::vector<Node> children;
    Rational r =
        itv->second.isNull() ? Rational(1) : itv->second.getConst<Rational>();
    if (r.sgn() != 0)
    {
      for (std::map<Node, Node>::const_iterator it = msum.begin();
           it != msum.end();
           ++it)
      {
        if (it->first != v)
        {
          Node m;
          if (!it->first.isNull())
          {
            m = mkCoeffTerm(it->second, it->first);
          }
          else
          {
            m = it->second;
          }
          children.push_back(m);
        }
      }
      val = children.size() > 1
                ? NodeManager::currentNM()->mkNode(PLUS, children)
                : (children.size() == 1
                       ? children[0]
                       : NodeManager::currentNM()->mkConst(Rational(0)));
      if (!r.isOne() && !r.isNegativeOne())
      {
        if (v.getType().isInteger())
        {
          veq_c = NodeManager::currentNM()->mkConst(r.abs());
        }
        else
        {
          val = NodeManager::currentNM()->mkNode(
              MULT,
              val,
              NodeManager::currentNM()->mkConst(Rational(1) / r.abs()));
        }
      }
      val = r.sgn() == 1 ? negate(val) : Rewriter::rewrite(val);
      return (r.sgn() == 1 || k == EQUAL) ? 1 : -1;
    }
  }
  return 0;
}

int ArithMSum::isolate(
    Node v, const std::map<Node, Node>& msum, Node& veq, Kind k, bool doCoeff)
{
  Node veq_c;
  Node val;
  // isolate v in the (in)equality
  int ires = isolate(v, msum, veq_c, val, k);
  if (ires != 0)
  {
    Node vc = v;
    if (!veq_c.isNull())
    {
      if (doCoeff)
      {
        vc = NodeManager::currentNM()->mkNode(MULT, veq_c, vc);
      }
      else
      {
        return 0;
      }
    }
    bool inOrder = ires == 1;
    veq = NodeManager::currentNM()->mkNode(
        k, inOrder ? vc : val, inOrder ? val : vc);
  }
  return ires;
}

Node ArithMSum::solveEqualityFor(Node lit, Node v)
{
  Assert(lit.getKind() == EQUAL);
  // first look directly at sides
  TypeNode tn = lit[0].getType();
  for (unsigned r = 0; r < 2; r++)
  {
    if (lit[r] == v)
    {
      return lit[1 - r];
    }
  }
  if (tn.isReal())
  {
    std::map<Node, Node> msum;
    if (ArithMSum::getMonomialSumLit(lit, msum))
    {
      Node val, veqc;
      if (ArithMSum::isolate(v, msum, veqc, val, EQUAL) != 0)
      {
        if (veqc.isNull())
        {
          // in this case, we have an integer equality with a coefficient
          // on the variable we solved for that could not be eliminated,
          // hence we fail.
          return val;
        }
      }
    }
  }
  return Node::null();
}

bool ArithMSum::decompose(Node n, Node v, Node& coeff, Node& rem)
{
  std::map<Node, Node> msum;
  if (getMonomialSum(n, msum))
  {
    std::map<Node, Node>::iterator it = msum.find(v);
    if (it == msum.end())
    {
      return false;
    }
    else
    {
      coeff = it->second;
      msum.erase(v);
      rem = mkNode(msum);
      return true;
    }
  }
  return false;
}

Node ArithMSum::negate(Node t)
{
  Node tt = NodeManager::currentNM()->mkNode(
      MULT, NodeManager::currentNM()->mkConst(Rational(-1)), t);
  tt = Rewriter::rewrite(tt);
  return tt;
}

Node ArithMSum::offset(Node t, int i)
{
  Node tt = NodeManager::currentNM()->mkNode(
      PLUS, NodeManager::currentNM()->mkConst(Rational(i)), t);
  tt = Rewriter::rewrite(tt);
  return tt;
}

void ArithMSum::debugPrintMonomialSum(std::map<Node, Node>& msum, const char* c)
{
  for (std::map<Node, Node>::iterator it = msum.begin(); it != msum.end(); ++it)
  {
    Trace(c) << "  ";
    if (!it->second.isNull())
    {
      Trace(c) << it->second;
      if (!it->first.isNull())
      {
        Trace(c) << " * ";
      }
    }
    if (!it->first.isNull())
    {
      Trace(c) << it->first;
    }
    Trace(c) << std::endl;
  }
  Trace(c) << std::endl;
}

} /* CVC4::theory namespace */
} /* CVC4 namespace */
