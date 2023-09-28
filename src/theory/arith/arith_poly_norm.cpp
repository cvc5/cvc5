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

#include "util/bitvector.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {

void PolyNorm::addMonomial(TNode x, const Rational& c, bool isNeg)
{
  // if zero, ignore
  if (c.sgn() == 0)
  {
    return;
  }
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

void PolyNorm::mod(const Rational& c)
{
  Assert(c.sgn() != 0);
  Assert (c.isIntegral());
  const Integer& ci = c.getNumerator();
  // multiply by constant
  for (std::pair<const Node, Rational>& m : d_polyNorm)
  {
    // c1*x*c2 = (c1*c2)*x
    Assert (m.second.isIntegral());
    m.second = Rational(m.second.getNumerator().euclidianDivideRemainder(ci));
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

bool PolyNorm::isEqualMod(const PolyNorm& p, Rational& c) const
{
  if (d_polyNorm.size() != p.d_polyNorm.size())
  {
    return false;
  }
  bool firstTime = true;
  c = Rational(1);
  std::unordered_map<Node, Rational>::const_iterator it;
  for (const std::pair<const Node, Rational>& m : d_polyNorm)
  {
    Assert(m.second.sgn() != 0);
    it = p.d_polyNorm.find(m.first);
    if (it == p.d_polyNorm.end())
    {
      return false;
    }
    if (firstTime)
    {
      c = m.second / it->second;
      firstTime = false;
    }
    else if (m.second / it->second != c)
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
        visited[cur].addMonomial(null, r);
        visit.pop_back();
        continue;
      }
      else if (k == CONST_BITVECTOR)
      {
        BitVector bv = cur.getConst<BitVector>();
        visited[cur].addMonomial(null, Rational(bv.getValue()));
        visit.pop_back();
        continue;
      }
      else if (k == CONST_BITVECTOR_SYMBOLIC)
      {
        // handle symbolic bv constants here as well
        if (cur[0].isConst() && cur[1].isConst()
            && cur[1].getConst<Rational>().sgn() == 1
            && cur[1].getConst<Rational>().getNumerator().fitsUnsignedInt())
        {
          Integer value = cur[0].getConst<Rational>().getNumerator();
          Integer size = cur[1].getConst<Rational>().getNumerator();
          BitVector bv(size.toUnsignedInt(), value);
          visited[cur].addMonomial(null, Rational(bv.getValue()));
          visit.pop_back();
          continue;
        }
      }
      else if (k == ADD || k == SUB || k == NEG || k == MULT
               || k == NONLINEAR_MULT || k == TO_REAL || k == BITVECTOR_ADD
               || k == BITVECTOR_SUB || k == BITVECTOR_NEG
               || k == BITVECTOR_MULT)
      {
        visited[cur] = PolyNorm();
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
        continue;
      }
      // it is a leaf
      visited[cur].addMonomial(cur, one);
      visit.pop_back();
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
        case BITVECTOR_ADD:
        case BITVECTOR_SUB:
        case BITVECTOR_NEG:
        case BITVECTOR_MULT:
          for (size_t i = 0, nchild = cur.getNumChildren(); i < nchild; i++)
          {
            it = visited.find(cur[i]);
            Assert(it != visited.end());
            if (((k == SUB || k == BITVECTOR_SUB) && i == 1) || k == NEG
                || k == BITVECTOR_NEG)
            {
              ret.subtract(it->second);
            }
            else if (i > 0
                     && (k == MULT || k == NONLINEAR_MULT
                         || k == BITVECTOR_MULT))
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
        case CONST_INTEGER:
        case CONST_BITVECTOR:
        case CONST_BITVECTOR_SYMBOLIC:
          // ignore, this is the case of a repeated zero, since we check for
          // empty of the polynomial above.
          break;
        default: Unhandled() << "Unhandled polynomial operation " << cur; break;
      }
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  return visited[n];
}

bool PolyNorm::isArithPolyNorm(TNode a, TNode b)
{
  if (a==b)
  {
    return true;
  }
  TypeNode at = a.getType();
  if (at.isBoolean())
  {
    // otherwise may be atoms
    return isArithPolyNormAtom(a, b);
  }
  // Otherwise normalize, which notice abstracts any non-arithmetic term.
  // We impose no type requirements here.
  PolyNorm pa = PolyNorm::mkPolyNorm(a);
  PolyNorm pb = PolyNorm::mkPolyNorm(b);
  return pa.isEqual(pb);
}

bool PolyNorm::isArithPolyNormAtom(TNode a, TNode b)
{
  Assert(a.getType().isBoolean());
  Kind k = a.getKind();
  if (b.getKind() != k)
  {
    return false;
  }
  // the type of nodes are considering
  TypeNode eqtn;
  if (k == EQUAL)
  {
    for (size_t i = 0; i < 2; i++)
    {
      Node eq = i == 0 ? a : b;
      for (size_t j = 0; j < 2; j++)
      {
        TypeNode tn = eq[j].getType();
        eqtn = eqtn.isNull() ? tn : eqtn.leastUpperBound(tn);
        // could happen if we are comparing equalities of different types
        if (eqtn.isNull())
        {
          return false;
        }
      }
    }
  }
  else if (k == GEQ || k == LEQ || k == GT || k == LT)
  {
    // k is a handled binary relation, i.e. one that permits normalization
    // via subtracting the right side from the left.
  }
  else
  {
    // note that we cannot use this method to show equivalence for
    // bitvector inequalities.
    return false;
  }
  PolyNorm pa = PolyNorm::mkDiff(a[0], a[1]);
  PolyNorm pb = PolyNorm::mkDiff(b[0], b[1]);
  // if a non-arithmetic equality
  if (k == EQUAL && !eqtn.isRealOrInt())
  {
    if (eqtn.isBitVector())
    {
      // for bitvectors, take modulo 2^w on coefficients
      Rational w = Rational(Integer(2).pow(eqtn.getBitVectorSize()));
      pa.mod(w);
      pb.mod(w);
    }
    // Check for equality. notice that we don't insist on any type here.
    return pa.isEqual(pb);
  }
  // check if the two polynomials are equal modulo a constant coefficient
  // in other words, x ~ y is equivalent to z ~ w if
  // x-y = c*(z-w) for some c > 0.
  Rational c;
  if (!pa.isEqualMod(pb, c))
  {
    return false;
  }
  Assert(c.sgn() != 0);
  // if equal, can be negative. Notice this shortcuts symmetry of equality.
  return k == EQUAL || c.sgn() == 1;
}

PolyNorm PolyNorm::mkDiff(TNode a, TNode b)
{
  PolyNorm pa = PolyNorm::mkPolyNorm(a);
  PolyNorm pb = PolyNorm::mkPolyNorm(b);
  pa.subtract(pb);
  return pa;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
