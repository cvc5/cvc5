/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic utility for polynomial normalization
 */

#include "theory/arith/arith_poly_norm.h"

#include "expr/attribute.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"
#include "theory/arith/arith_poly_norm.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {

void PolyNorm::addMonomial(TNode x, const Rational& c, bool isNeg)
{
  // if zero, ignore since adding zero is a no-op.
  if (c.sgn() == 0)
  {
    return;
  }
  std::map<Node, Rational>::iterator it = d_polyNorm.find(x);
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
    std::map<Node, Rational> ptmp = d_polyNorm;
    d_polyNorm.clear();
    for (const std::pair<const Node, Rational>& m : ptmp)
    {
      // c1*x1*c2*x2 = (c1*c2)*(x1*x2)
      Node newM = multMonoVar(m.first, x);
      d_polyNorm[newM] = m.second * c;
    }
  }
}

void PolyNorm::mulCoeffs(const Rational& c)
{
  if (c.sgn() == 0)
  {
    d_polyNorm.clear();
    return;
  }
  for (std::pair<const Node, Rational>& m : d_polyNorm)
  {
    m.second *= c;
  }
}

void PolyNorm::modCoeffs(const Rational& c)
{
  Assert(c.sgn() != 0);
  Assert(c.isIntegral());
  const Integer& ci = c.getNumerator();
  // mod the coefficient by constant
  std::vector<Node> zeroes;
  for (std::pair<const Node, Rational>& m : d_polyNorm)
  {
    Assert(m.second.isIntegral());
    m.second = Rational(m.second.getNumerator().euclidianDivideRemainder(ci));
    if (m.second.sgn()==0)
    {
      zeroes.push_back(m.first);
    }
  }
  // go back and erase monomials that became zero
  for (const Node& z : zeroes)
  {
    d_polyNorm.erase(z);
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
    std::map<Node, Rational> ptmp = d_polyNorm;
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
  std::map<Node, Rational>::const_iterator it;
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

bool PolyNorm::isConstant(Rational& c) const
{
  if (d_polyNorm.size() == 0)
  {
    c = Rational(0);
    return true;
  }
  if (d_polyNorm.size() == 1)
  {
    if (d_polyNorm.begin()->first.isNull())
    {
      c = d_polyNorm.begin()->second;
      return true;
    }
  }
  return false;
}

bool PolyNorm::isEqualMod(const PolyNorm& p, Rational& c) const
{
  if (d_polyNorm.size() != p.d_polyNorm.size())
  {
    return false;
  }
  bool firstTime = true;
  c = Rational(1);
  std::map<Node, Rational>::const_iterator it;
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

Node PolyNorm::toNode(const TypeNode& tn) const
{
  std::vector<Node> sum;
  NodeManager* nm = tn.getNodeManager();
  bool isArith = (tn.isInteger() || tn.isReal());
  bool isBv = tn.isBitVector();
  Kind multKind;
  Kind addKind;
  Node one;
  if (isArith)
  {
    multKind = Kind::MULT;
    addKind = Kind::ADD;
    one = nm->mkConstRealOrInt(tn, Rational(1));
  }
  else if (isBv)
  {
    multKind = Kind::BITVECTOR_MULT;
    addKind = Kind::BITVECTOR_ADD;
    one = bv::utils::mkOne(nm, tn.getBitVectorSize());
  }
  else
  {
    return Node::null();
  }
  for (const std::pair<const Node, Rational>& m : d_polyNorm)
  {
    Node coeff;
    if (isArith)
    {
      coeff = nm->mkConstRealOrInt(tn, m.second);
    }
    else
    {
      Assert(isBv);
      coeff = nm->mkConst(
          BitVector(tn.getBitVectorSize(), m.second.getNumerator()));
    }
    if (m.first.isNull())
    {
      sum.push_back(coeff);
      continue;
    }
    Node t = m.first;
    if (t.getKind() == Kind::SEXPR)
    {
      std::vector<Node> vars(t.begin(), t.end());
      t = nm->mkNode(multKind, vars);
    }
    if (coeff == one)
    {
      sum.push_back(t);
    }
    else
    {
      Assert(t.getType().isComparableTo(tn));
      sum.push_back(nm->mkNode(multKind, {coeff, t}));
    }
  }
  if (sum.size() == 1)
  {
    return sum[0];
  }
  if (sum.empty())
  {
    if (isArith)
    {
      return nm->mkConstRealOrInt(tn, Rational(0));
    }
    else
    {
      Assert(isBv);
      return bv::utils::mkZero(nm, tn.getBitVectorSize());
    }
  }
  // must sort to ensure this method is idempotent
  std::sort(sum.begin(), sum.end());
  return nm->mkNode(addKind, sum);
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
  // we use SEXPR instead of multiplication, which is agnostic to types
  return m2.getNodeManager()->mkNode(Kind::SEXPR, vars);
}

std::vector<TNode> PolyNorm::getMonoVars(TNode m)
{
  std::vector<TNode> vars;
  // m is null if this is the empty variable (for constant monomials)
  if (!m.isNull())
  {
    Kind k = m.getKind();
    Assert(k != Kind::CONST_RATIONAL && k != Kind::CONST_INTEGER);
    if (k == Kind::SEXPR)
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
      if (k == Kind::CONST_RATIONAL || k == Kind::CONST_INTEGER)
      {
        Rational r = cur.getConst<Rational>();
        visited[cur].addMonomial(null, r);
        visit.pop_back();
        continue;
      }
      else if (k == Kind::CONST_BITVECTOR)
      {
        // The bitwidth does not matter here, since the logic for normalizing
        // polynomials considers the semantics of overflow.
        BitVector bv = cur.getConst<BitVector>();
        visited[cur].addMonomial(null, Rational(bv.getValue()));
        visit.pop_back();
        continue;
      }
      else if (k == Kind::ADD || k == Kind::SUB || k == Kind::NEG
               || k == Kind::MULT || k == Kind::NONLINEAR_MULT
               || k == Kind::TO_REAL || k == Kind::BITVECTOR_ADD
               || k == Kind::BITVECTOR_SUB || k == Kind::BITVECTOR_NEG
               || k == Kind::BITVECTOR_MULT)
      {
        visited[cur] = PolyNorm();
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
        continue;
      }
      else if (k == Kind::DIVISION || k == Kind::DIVISION_TOTAL)
      {
        // only division by non-zero constant is supported
        if (cur[1].isConst() && cur[1].getConst<Rational>().sgn() != 0)
        {
          visited[cur] = PolyNorm();
          visit.push_back(cur[0]);
          continue;
        }
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
        case Kind::ADD:
        case Kind::SUB:
        case Kind::NEG:
        case Kind::MULT:
        case Kind::NONLINEAR_MULT:
        case Kind::TO_REAL:
        case Kind::BITVECTOR_ADD:
        case Kind::BITVECTOR_SUB:
        case Kind::BITVECTOR_NEG:
        case Kind::BITVECTOR_MULT:
          for (size_t i = 0, nchild = cur.getNumChildren(); i < nchild; i++)
          {
            it = visited.find(cur[i]);
            Assert(it != visited.end());
            if (((k == Kind::SUB || k == Kind::BITVECTOR_SUB) && i == 1) || k == Kind::NEG
                || k == Kind::BITVECTOR_NEG)
            {
              ret.subtract(it->second);
            }
            else if (i > 0
                     && (k == Kind::MULT || k == Kind::NONLINEAR_MULT
                         || k == Kind::BITVECTOR_MULT))
            {
              ret.multiply(it->second);
            }
            else
            {
              ret.add(it->second);
            }
          }
          break;
        case Kind::DIVISION:
        case Kind::DIVISION_TOTAL:
        {
          it = visited.find(cur[0]);
          Assert(it != visited.end());
          ret.add(it->second);
          Assert(cur[1].isConst());
          // multiply by inverse
          Rational invc = cur[1].getConst<Rational>().inverse();
          ret.multiplyMonomial(TNode::null(), invc);
        }
        break;
        case Kind::CONST_RATIONAL:
        case Kind::CONST_INTEGER:
        case Kind::CONST_BITVECTOR:
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
  TypeNode at = a.getType();
  Assert(!at.isBoolean());
  if (a == b)
  {
    return true;
  }
  // Normalize, which notice abstracts any non-arithmetic term.
  // We impose no type requirements here.
  PolyNorm pa = PolyNorm::mkPolyNorm(a);
  PolyNorm pb = PolyNorm::mkPolyNorm(b);
  return areEqualPolyNormTyped(at, pa, pb);
}

bool PolyNorm::areEqualPolyNormTyped(const TypeNode& t,
                                     PolyNorm& pa,
                                     PolyNorm& pb)
{
  // do modulus by 2^bitwidth if bitvectors
  if (t.isBitVector())
  {
    Rational w = Rational(Integer(2).pow(t.getBitVectorSize()));
    pa.modCoeffs(w);
    pb.modCoeffs(w);
  }
  return pa.isEqual(pb);
}

bool PolyNorm::isArithPolyNormRel(TNode a, TNode b, Rational& ca, Rational& cb)
{
  Assert(a.getType().isBoolean());
  if (a == b)
  {
    return true;
  }
  Kind k = a.getKind();
  if (b.getKind() != k)
  {
    return false;
  }
  // Compute the type of nodes we are considering. We must ensure that a and b
  // have comparable type, or else we fail here.
  TypeNode eqtn;
  if (k == Kind::EQUAL)
  {
    Assert(a[0].getType().isComparableTo(a[1].getType()));
    Assert(b[0].getType().isComparableTo(b[1].getType()));
    eqtn = a[0].getType().leastUpperBound(a[1].getType());
    TypeNode eqtn2 = b[0].getType().leastUpperBound(b[1].getType());
    if (eqtn.isRealOrInt())
    {
      // we can prove equivalence of Real vs Int equalities
      if (!eqtn2.isRealOrInt())
      {
        return false;
      }
    }
    else
    {
      eqtn = eqtn.leastUpperBound(eqtn2);
      // could happen if we are comparing equalities of different types
      if (!eqtn.isBitVector())
      {
        return false;
      }
    }
  }
  else if (k != Kind::GEQ && k != Kind::LEQ && k != Kind::GT && k != Kind::LT)
  {
    // note that we cannot use this method to show equivalence for
    // bitvector inequalities.
    return false;
  }
  Trace("arith-poly-norm-rel")
      << "Poly norm rel? " << a << " " << b << std::endl;
  // k is a handled binary relation, i.e. one that permits normalization
  // via subtracting the right side from the left.
  PolyNorm pa = PolyNorm::mkDiff(a[0], a[1]);
  PolyNorm pb = PolyNorm::mkDiff(b[0], b[1]);
  // if a non-arithmetic equality
  if (k == Kind::EQUAL && !eqtn.isRealOrInt())
  {
    Assert(eqtn.isBitVector());
    ca = Rational(1);
    cb = Rational(1);
    Trace("arith-poly-norm-rel") << "...determine multiply factor" << std::endl;
    for (const std::pair<const Node, Rational>& m : pa.d_polyNorm)
    {
      std::map<Node, Rational>::iterator itb = pb.d_polyNorm.find(m.first);
      if (itb == pb.d_polyNorm.end())
      {
        // a monomial in a is not in b
        return false;
      }
      // if this factor is odd
      bool oddA = m.second.getNumerator().testBit(0);
      bool oddB = itb->second.getNumerator().testBit(0);
      if (oddA != oddB)
      {
        // an odd with an even
        return false;
      }
      else if (oddA && oddB)
      {
        // Coefficients are both odd but not equal, multiply either side.
        // Ensure that we take them modulo the bitwidth here.
        Integer w = Integer(2).pow(eqtn.getBitVectorSize());
        Integer ai = m.second.getNumerator().euclidianDivideRemainder(w);
        Integer bi = itb->second.getNumerator().euclidianDivideRemainder(w);
        if (ai != bi)
        {
          ca = Rational(bi);
          cb = Rational(ai);
        }
        // else, coefficients are equal, we should just try 1 / 1
        break;
      }
      // even with even is inconclusive
    }
    Trace("arith-poly-norm") << "...try " << ca << " / " << cb << std::endl;
    pa.mulCoeffs(ca);
    pb.mulCoeffs(cb);
    // Check for equality, taking modulo 2^w on coefficients.
    return areEqualPolyNormTyped(eqtn, pa, pb);
  }
  // check if the two polynomials are equal modulo a constant coefficient
  // in other words, x ~ y is equivalent to z ~ w if
  // c1*(x-y) = c2*(z-w) for some non-zero c1 and c2.
  ca = pb.d_polyNorm.empty() ? Rational(1) : pb.d_polyNorm.cbegin()->second;
  cb = pa.d_polyNorm.empty() ? Rational(1) : pa.d_polyNorm.cbegin()->second;
  pa.mulCoeffs(ca);
  pb.mulCoeffs(cb);
  if (!pa.isEqual(pb))
  {
    return false;
  }
  Assert(ca.sgn() != 0);
  Assert(cb.sgn() != 0);
  // if equal, can be negative. Notice this shortcuts symmetry of equality.
  return k == Kind::EQUAL || ca.sgn() == cb.sgn();
}

Node PolyNorm::getArithPolyNormRelPremise(TNode a,
                                          TNode b,
                                          const Rational& rx,
                                          const Rational& ry)
{
  NodeManager* nm = a.getNodeManager();
  Node lhs, rhs;
  if (a[0].getType().isBitVector())
  {
    uint32_t wa = a[0].getType().getBitVectorSize();
    uint32_t wb = b[0].getType().getBitVectorSize();
    Node cx = nm->mkConst(BitVector(wa, rx.getNumerator()));
    Node cy = nm->mkConst(BitVector(wb, ry.getNumerator()));
    Node x = nm->mkNode(Kind::BITVECTOR_SUB, a[0], a[1]);
    Node y = nm->mkNode(Kind::BITVECTOR_SUB, b[0], b[1]);
    lhs = nm->mkNode(Kind::BITVECTOR_MULT, cx, x);
    rhs = nm->mkNode(Kind::BITVECTOR_MULT, cy, y);
  }
  else
  {
    Node x = nm->mkNode(Kind::SUB, a[0], a[1]);
    Node y = nm->mkNode(Kind::SUB, b[0], b[1]);
    Node cx, cy;
    // Equality does not support mixed arithmetic, so we eliminate it here.
    if (x.getType().isInteger() && y.getType().isInteger())
    {
      cx = nm->mkConstInt(rx);
      cy = nm->mkConstInt(ry);
    }
    else
    {
      cx = nm->mkConstReal(rx);
      cy = nm->mkConstReal(ry);
      // add TO_REAL to avoid mixed arithmetic
      if (x.getType().isInteger())
      {
        x = nm->mkNode(Kind::TO_REAL, x);
      }
      if (y.getType().isInteger())
      {
        y = nm->mkNode(Kind::TO_REAL, y);
      }
    }
    lhs = nm->mkNode(Kind::MULT, cx, x);
    rhs = nm->mkNode(Kind::MULT, cy, y);
  }
  return lhs.eqNode(rhs);
}

PolyNorm PolyNorm::mkDiff(TNode a, TNode b)
{
  PolyNorm pa = PolyNorm::mkPolyNorm(a);
  PolyNorm pb = PolyNorm::mkPolyNorm(b);
  pa.subtract(pb);
  return pa;
}

struct ArithPolyNormTag
{
};
/** Cache for PolyNorm::getPolyNorm */
typedef expr::Attribute<ArithPolyNormTag, Node> ArithPolyNormAttr;

Node PolyNorm::getPolyNorm(Node a)
{
  ArithPolyNormAttr apna;
  Node an = a.getAttribute(apna);
  if (an.isNull())
  {
    PolyNorm pa = arith::PolyNorm::mkPolyNorm(a);
    an = pa.toNode(a.getType());
    if (an.isNull())
    {
      a.setAttribute(apna, a);
      return a;
    }
    else
    {
      a.setAttribute(apna, an);
      if (a != an)
      {
        // as an optimization, assume idempotent
        an.setAttribute(apna, an);
      }
    }
  }
  return an;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
