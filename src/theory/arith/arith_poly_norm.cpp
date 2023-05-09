/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic utility for polynomial normalization
 */

#include "theory/arith/arith_poly_norm.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {

void PolyNorm::addMonomial(TNode x, const Rational& c, bool isNeg)
{
  Assert(c.sgn() != 0);
  std::unordered_map<Node, Rational>::iterator it = d_polyNorm.find(x);
  if (it == d_polyNorm.end())
  {
    d_polyNorm[x] = isNeg ? -c : c;
    return;
  }
  Rational res(it->second + (isNeg ? -c : c));
  if (res.sgn() == 0)
  {
    // cancels
    d_polyNorm.erase(it);
  }
  else
  {
    d_polyNorm[x] = res;
  }
}

void PolyNorm::multiplyMonomial(TNode x, const Rational& c)
{
  Assert(c.sgn() != 0);
  if (x.isNull())
  {
    // multiply by constant
    for (std::pair<const Node, Rational>& m : d_polyNorm)
    {
      // c1*x*c2 = (c1*c2)*x
      m.second *= c;
    }
  }
  else
  {
    std::unordered_map<Node, Rational> ptmp = d_polyNorm;
    d_polyNorm.clear();
    for (const std::pair<const Node, Rational>& m : ptmp)
    {
      // c1*x1*c2*x2 = (c1*c2)*(x1*x2)
      Node newM = multMonoVar(m.first, x);
      d_polyNorm[newM] = m.second * c;
    }
  }
}

void PolyNorm::add(const PolyNorm& p)
{
  for (const std::pair<const Node, Rational>& m : p.d_polyNorm)
  {
    addMonomial(m.first, m.second);
  }
}

void PolyNorm::subtract(const PolyNorm& p)
{
  for (const std::pair<const Node, Rational>& m : p.d_polyNorm)
  {
    addMonomial(m.first, m.second, true);
  }
}

void PolyNorm::multiply(const PolyNorm& p)
{
  if (p.d_polyNorm.size() == 1)
  {
    for (const std::pair<const Node, Rational>& m : p.d_polyNorm)
    {
      multiplyMonomial(m.first, m.second);
    }
  }
  else
  {
    // If multiplying by sum, must distribute; if multiplying by zero, clear.
    // First, remember the current state and clear.
    std::unordered_map<Node, Rational> ptmp = d_polyNorm;
    d_polyNorm.clear();
    for (const std::pair<const Node, Rational>& m : p.d_polyNorm)
    {
      PolyNorm pbase;
      pbase.d_polyNorm = ptmp;
      pbase.multiplyMonomial(m.first, m.second);
      // add this to current
      add(pbase);
    }
  }
}

void PolyNorm::clear() { d_polyNorm.clear(); }

bool PolyNorm::empty() const { return d_polyNorm.empty(); }

bool PolyNorm::isEqual(const PolyNorm& p) const
{
  if (d_polyNorm.size() != p.d_polyNorm.size())
  {
    return false;
  }
  std::unordered_map<Node, Rational>::const_iterator it;
  for (const std::pair<const Node, Rational>& m : d_polyNorm)
  {
    Assert(m.second.sgn() != 0);
    it = p.d_polyNorm.find(m.first);
    if (it == p.d_polyNorm.end() || m.second != it->second)
    {
      return false;
    }
  }
  return true;
}

Node PolyNorm::multMonoVar(TNode m1, TNode m2)
{
  std::vector<TNode> vars = getMonoVars(m1);
  std::vector<TNode> vars2 = getMonoVars(m2);
  vars.insert(vars.end(), vars2.begin(), vars2.end());
  if (vars.empty())
  {
    // constants
    return Node::null();
  }
  else if (vars.size() == 1)
  {
    return vars[0];
  }
  // use default sorting
  std::sort(vars.begin(), vars.end());
  return NodeManager::currentNM()->mkNode(NONLINEAR_MULT, vars);
}

std::vector<TNode> PolyNorm::getMonoVars(TNode m)
{
  std::vector<TNode> vars;
  // m is null if this is the empty variable (for constant monomials)
  if (!m.isNull())
  {
    Kind k = m.getKind();
    Assert(k != CONST_RATIONAL && k != CONST_INTEGER);
    if (k == MULT || k == NONLINEAR_MULT)
    {
      vars.insert(vars.end(), m.begin(), m.end());
    }
    else
    {
      vars.push_back(m);
    }
  }
  return vars;
}

PolyNorm PolyNorm::mkPolyNorm(TNode n)
{
  Assert(n.getType().isRealOrInt());
  Rational one(1);
  Node null;
  std::unordered_map<TNode, PolyNorm> visited;
  std::unordered_map<TNode, PolyNorm>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    it = visited.find(cur);
    Kind k = cur.getKind();
    if (it == visited.end())
    {
      if (k == CONST_RATIONAL || k == CONST_INTEGER)
      {
        Rational r = cur.getConst<Rational>();
        if (r.sgn() == 0)
        {
          // zero is not an entry
          visited[cur] = PolyNorm();
        }
        else
        {
          visited[cur].addMonomial(null, r);
        }
      }
      else if (k == ADD || k == SUB || k == NEG || k == MULT
               || k == NONLINEAR_MULT || k == TO_REAL)
      {
        visited[cur] = PolyNorm();
        for (const Node& cn : cur)
        {
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
        case ADD:
        case SUB:
        case NEG:
        case MULT:
        case NONLINEAR_MULT:
        case TO_REAL:
          for (size_t i = 0, nchild = cur.getNumChildren(); i < nchild; i++)
          {
            it = visited.find(cur[i]);
            Assert(it != visited.end());
            if ((k == SUB && i == 1) || k == NEG)
            {
              ret.subtract(it->second);
            }
            else if (i > 0 && (k == MULT || k == NONLINEAR_MULT))
            {
              ret.multiply(it->second);
            }
            else
            {
              ret.add(it->second);
            }
          }
          break;
        case CONST_RATIONAL:
        case CONST_INTEGER: break;
        default: Unhandled() << "Unhandled polynomial operation " << cur; break;
      }
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  return visited[n];
}

bool PolyNorm::isArithPolyNorm(TNode a, TNode b)
{
  PolyNorm pa = PolyNorm::mkPolyNorm(a);
  PolyNorm pb = PolyNorm::mkPolyNorm(b);
  return pa.isEqual(pb);
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
