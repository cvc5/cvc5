/*********************                                                        */
/*! \file arith_utilities.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of common functions for dealing with nodes.
 **/

#include "arith_utilities.h"

namespace CVC4 {
namespace theory {
namespace arith {

/** Join kinds, where k1 and k2 are arithmetic relations returns an
 * arithmetic relation ret such that
 * if (a <k1> b) and (a <k2> b), then (a <ret> b).
 */
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
  if (k1 == kind::EQUAL)
  {
    if (k2 == kind::LEQ || k2 == kind::GEQ)
    {
      return k1;
    }
  }
  else if (k1 == kind::LT)
  {
    if (k2 == kind::LEQ)
    {
      return k1;
    }
  }
  else if (k1 == kind::LEQ)
  {
    if (k2 == kind::GEQ)
    {
      return kind::EQUAL;
    }
  }
  else if (k1 == kind::GT)
  {
    if (k2 == kind::GEQ)
    {
      return k1;
    }
  }
  return kind::UNDEFINED_KIND;
}

/** Transitive kinds, where k1 and k2 are arithmetic relations returns an
 * arithmetic relation ret such that
 * if (a <k1> b) and (b <k2> c) then (a <ret> c).
 */
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
  if (k1 == kind::EQUAL)
  {
    return k2;
  }
  else if (k1 == kind::LT)
  {
    if (k2 == kind::LEQ)
    {
      return k1;
    }
  }
  else if (k1 == kind::GT)
  {
    if (k2 == kind::GEQ)
    {
      return k1;
    }
  }
  return kind::UNDEFINED_KIND;
}

/** Is k a transcendental function kind? */
bool isTranscendentalKind(Kind k)
{
  // many operators are eliminated during rewriting
  Assert(k != kind::TANGENT && k != kind::COSINE && k != kind::COSECANT
         && k != kind::SECANT && k != kind::COTANGENT);
  return k == kind::EXPONENTIAL || k == kind::SINE || k == kind::PI;
}

/**
 * Get a lower/upper approximation of the constant r within the given
 * level of precision. In other words, this returns a constant c' such that
 *   c' <= c <= c' + 1/(10^prec) if isLower is true, or
 *   c' + 1/(10^prec) <= c <= c' if isLower is false.
 * where c' is a rational of the form n/d for some n and d <= 10^prec.
 */
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

/** print rational approximation of cr with precision prec on trace c */
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

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
