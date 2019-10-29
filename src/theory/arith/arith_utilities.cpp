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

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
