/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic utility for polynomial normalization
 */

#include "theory/arith/arith_poly_norm.h"

#include "util/rational.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace arith {

Node MonomialVar::multMonoVar(Node m1, Node m2)
{
  
}

void PolyNorm::addMonomial(Node x, Node c, bool isNeg)
{
  Assert (c.getKind()==CONST_RATIONAL);
  NodeManager * nm = NodeManager::currentNM();
  std::unordered_map<Node, Node>::iterator it = d_polyNorm.find(x);
  if (it==d_polyNorm.end())
  {
    d_polyNorm[x] = isNeg ? nm->mkConst(Rational(-c.getConst<Rational>())) : c;
    return;
  }
  Rational r = c.getConst<Rational>();
  if (isNeg)
  {
    r = -r;
  }
  Assert (it->second.getKind()==CONST_RATIONAL);
  d_polyNorm[x] = nm->mkConst(Rational(it->second.getConst<Rational>() + r));
}

void PolyNorm::multiplyMonomial(Node x, Node c)
{
  Assert (c.getKind()==CONST_RATIONAL);
  NodeManager * nm = NodeManager::currentNM();
  Rational r = c.getConst<Rational>();
  if (x.isNull())
  {
    // multiply by constant
    for (std::pair<const Node, Node>& m : d_polyNorm)
    {
      Assert (m.second.getKind()==CONST_RATIONAL);
      // c1*x*c2 = (c1*c2)*x
      d_polyNorm[m.first] = nm->mkConst(Rational(m.second.getConst<Rational>()*r));
    }
  }
  else
  {
    std::unordered_map<Node, Node> ptmp = d_polyNorm;
    d_polyNorm.clear();
    for (const std::pair<const Node, Node>& m : ptmp)
    {
      Assert (m.second.getKind()==CONST_RATIONAL);
      // c1*x1*c2*x2 = (c1*c2)*(x1*x2)
      Node newM = multMonoVar(m.first, x);
      d_polyNorm[newM] = nm->mkConst(Rational(m.second.getConst<Rational>()*r));
    }
  }
}

void PolyNorm::add(const PolyNorm& p)
{
  for (const std::pair<const Node, Node>& m : p.d_polyNorm)
  {
    addMonomial(m.first, m.second);
  }
}

void PolyNorm::subtract(const PolyNorm& p)
{
  for (const std::pair<const Node, Node>& m : p.d_polyNorm)
  {
    addMonomial(m.first, m.second, true);
  }
}

void PolyNorm::multiply(const PolyNorm& p)
{
  PolyNorm psum;
  psum.d_polyNorm = d_polyNorm;
  for (const std::pair<const Node, Node>& m : p.d_polyNorm)
  {
    
  }
}

void PolyNorm::clear()
{
  d_polyNorm.clear();
}

bool PolyNorm::empty() const
{
  return d_polyNorm.empty();
}

PolyNorm PolyNorm::mkPolyNorm(Node n)
{
  NodeManager * nm = NodeManager::currentNM();
  Node one = nm->mkConst(Rational(1));
  Node null;
  std::unordered_map<TNode, PolyNorm> visited;
  std::unordered_map<TNode, PolyNorm>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    it = visited.find(cur);
    Kind k = cur.getKind();
    if (it == visited.end()) {
      if (k==CONST_RATIONAL)
      {
        visited[cur].addMonomial(null, cur);
      }
      else if (k==PLUS || k==MINUS || k==UMINUS || k==MULT || k==NONLINEAR_MULT)
      {
        visited[cur].clear();
        for (const Node& cn : cur) {
          visit.push_back(cn);
        }
      }
      else
      {
        // it is a leaf
        visited[cur].addMonomial(cur, one);
        visit.pop_back();
      }
      continue;
    }
    visit.pop_back();
    if (it->second.empty()) 
    {
      PolyNorm& ret = visited[cur];
      switch (k)
      {
        case PLUS:
        case MINUS:
        case UMINUS:
        case MULT:
        case NONLINEAR_MULT:
          for (size_t i=0, nchild = cur.getNumChildren(); i<nchild; i++)
          {
            it = visited.find(cur[i]);
            Assert(it != visited.end());
            if ((k==MINUS && i==1) || k==UMINUS)
            {
              ret.subtract(it->second);
            }
            else if (i>0 && (k==MULT || k==NONLINEAR_MULT))
            {
              ret.multiply(it->second);
            }
            else
            {
              ret.add(it->second);
            }
          }
          break;
        default:
          Unhandled() << "Unhandled polynomial operation " << cur;
          break;
      }
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  return visited[n];
}

bool PolyNorm::isArithPolyNorm(Node a, Node b)
{
  PolyNorm pa = PolyNorm::mkPolyNorm(a);
  PolyNorm pb = PolyNorm::mkPolyNorm(b);
  return false;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
