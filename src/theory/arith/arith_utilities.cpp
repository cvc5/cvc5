/*********************                                                        */
/*! \file arith_utilities.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of common functions for dealing with nodes.
 **/

#include "arith_utilities.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

Kind joinKinds(Kind k1, Kind k2)
{
  if (k2 < k1)
  {
    return joinKinds(k2, k1);
  }
  else if (k1 == k2)
  {
    return k1;
  }
  Assert(isRelationOperator(k1));
  Assert(isRelationOperator(k2));
  if (k1 == EQUAL)
  {
    if (k2 == LEQ || k2 == GEQ)
    {
      return k1;
    }
  }
  else if (k1 == LT)
  {
    if (k2 == LEQ)
    {
      return k1;
    }
  }
  else if (k1 == LEQ)
  {
    if (k2 == GEQ)
    {
      return EQUAL;
    }
  }
  else if (k1 == GT)
  {
    if (k2 == GEQ)
    {
      return k1;
    }
  }
  return UNDEFINED_KIND;
}

Kind transKinds(Kind k1, Kind k2)
{
  if (k2 < k1)
  {
    return transKinds(k2, k1);
  }
  else if (k1 == k2)
  {
    return k1;
  }
  Assert(isRelationOperator(k1));
  Assert(isRelationOperator(k2));
  if (k1 == EQUAL)
  {
    return k2;
  }
  else if (k1 == LT)
  {
    if (k2 == LEQ)
    {
      return k1;
    }
  }
  else if (k1 == GT)
  {
    if (k2 == GEQ)
    {
      return k1;
    }
  }
  return UNDEFINED_KIND;
}

bool isTranscendentalKind(Kind k)
{
  // many operators are eliminated during rewriting
  Assert(k != TANGENT && k != COSINE && k != COSECANT
         && k != SECANT && k != COTANGENT);
  return k == EXPONENTIAL || k == SINE || k == PI;
}

Node getApproximateConstant(Node c, bool isLower, unsigned prec)
{
  Assert(c.isConst());
  Rational cr = c.getConst<Rational>();

  unsigned lower = 0;
  unsigned upper = pow(10, prec);

  Rational den = Rational(upper);
  if (cr.getDenominator() < den.getNumerator())
  {
    // denominator is not more than precision, we return it
    return c;
  }

  int csign = cr.sgn();
  Assert(csign != 0);
  if (csign == -1)
  {
    cr = -cr;
  }
  Rational one = Rational(1);
  Rational ten = Rational(10);
  Rational pow_ten = Rational(1);
  // inefficient for large numbers
  while (cr >= one)
  {
    cr = cr / ten;
    pow_ten = pow_ten * ten;
  }
  Rational allow_err = one / den;

  // now do binary search
  Rational two = Rational(2);
  NodeManager* nm = NodeManager::currentNM();
  Node cret;
  do
  {
    unsigned curr = (lower + upper) / 2;
    Rational curr_r = Rational(curr) / den;
    Rational err = cr - curr_r;
    int esign = err.sgn();
    if (err.abs() <= allow_err)
    {
      if (esign == 1 && !isLower)
      {
        curr_r = Rational(curr + 1) / den;
      }
      else if (esign == -1 && isLower)
      {
        curr_r = Rational(curr - 1) / den;
      }
      curr_r = curr_r * pow_ten;
      cret = nm->mkConst(csign == 1 ? curr_r : -curr_r);
    }
    else
    {
      Assert(esign != 0);
      // update lower/upper
      if (esign == -1)
      {
        upper = curr;
      }
      else if (esign == 1)
      {
        lower = curr;
      }
    }
  } while (cret.isNull());
  return cret;
}

void printRationalApprox(const char* c, Node cr, unsigned prec)
{
  Assert(cr.isConst());
  Node ca = getApproximateConstant(cr, true, prec);
  if (ca != cr)
  {
    Trace(c) << "(+ ";
  }
  Trace(c) << ca;
  if (ca != cr)
  {
    Trace(c) << " [0,10^" << prec << "])";
  }
}

Node arithSubstitute(Node n, std::vector<Node>& vars, std::vector<Node>& subs)
{
  Assert(vars.size() == subs.size());
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<Node>::iterator itv;
  std::vector<TNode> visit;
  TNode cur;
  Kind ck;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited[cur] = Node::null();
      ck = cur.getKind();
      itv = std::find(vars.begin(), vars.end(), cur);
      if (itv != vars.end())
      {
        visited[cur] = subs[std::distance(vars.begin(), itv)];
      }
      else if (cur.getNumChildren() == 0)
      {
        visited[cur] = cur;
      }
      else
      {
        TheoryId ctid = theory::kindToTheoryId(ck);
        if ((ctid != THEORY_ARITH && ctid != THEORY_BOOL
             && ctid != THEORY_BUILTIN)
            || isTranscendentalKind(ck))
        {
          // Do not traverse beneath applications that belong to another theory
          // besides (core) arithmetic. Notice that transcendental function
          // applications are also not traversed here.
          visited[cur] = cur;
        }
        else
        {
          visit.push_back(cur);
          for (const Node& cn : cur)
          {
            visit.push_back(cn);
          }
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
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
        ret = nm->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node mkBounded(Node l, Node a, Node u)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(AND, nm->mkNode(GEQ, a, l), nm->mkNode(LEQ, a, u));
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
