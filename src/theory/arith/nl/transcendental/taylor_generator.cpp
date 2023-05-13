/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Generate taylor approximations transcendental lemmas.
 */

#include "theory/arith/nl/transcendental/taylor_generator.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/evaluator.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

TaylorGenerator::TaylorGenerator()
    : d_taylor_real_fv(NodeManager::currentNM()->mkBoundVar(
        "x", NodeManager::currentNM()->realType()))
{
}

TNode TaylorGenerator::getTaylorVariable() { return d_taylor_real_fv; }

std::pair<Node, Node> TaylorGenerator::getTaylor(Kind k, std::uint64_t n)
{
  Assert(n > 0);
  // check if we have already computed this Taylor series
  auto itt = d_taylor_terms[k].find(n);
  if (itt != d_taylor_terms[k].end())
  {
    return itt->second;
  }

  NodeManager* nm = NodeManager::currentNM();

  // the current factorial `counter!`
  Integer factorial = 1;
  // the current variable power `x^counter`
  Node varpow = nm->mkConstReal(Rational(1));
  std::vector<Node> sum;
  for (std::uint64_t counter = 1; counter <= n; ++counter)
  {
    if (k == Kind::EXPONENTIAL)
    {
      // Maclaurin series for exponential:
      //   \sum_{n=0}^\infty x^n / n!
      sum.push_back(
          nm->mkNode(Kind::DIVISION, varpow, nm->mkConstReal(factorial)));
    }
    else if (k == Kind::SINE)
    {
      // Maclaurin series for exponential:
      //   \sum_{n=0}^\infty (-1)^n / (2n+1)! * x^(2n+1)
      if (counter % 2 == 0)
      {
        int sign = (counter % 4 == 0 ? -1 : 1);
        sum.push_back(nm->mkNode(Kind::MULT,
                                 nm->mkNode(Kind::DIVISION,
                                            nm->mkConstReal(sign),
                                            nm->mkConstReal(factorial)),
                                 varpow));
      }
    }
    factorial *= counter;
    varpow = nm->mkNode(Kind::MULT, d_taylor_real_fv, varpow);
  }
  Node taylor_sum = (sum.size() == 1 ? sum[0] : nm->mkNode(Kind::ADD, sum));
  Node taylor_rem =
      nm->mkNode(Kind::DIVISION, varpow, nm->mkConstReal(factorial));

  auto res = std::make_pair(taylor_sum, taylor_rem);

  // put result in cache
  d_taylor_terms[k][n] = res;

  return res;
}

void TaylorGenerator::getPolynomialApproximationBounds(
    Kind k, std::uint64_t d, ApproximationBounds& pbounds)
{
  auto it = d_poly_bounds[k].find(d);
  if (it == d_poly_bounds[k].end())
  {
    NodeManager* nm = NodeManager::currentNM();
    // n is the Taylor degree we are currently considering
    std::uint64_t n = 2 * d;
    // n must be even
    std::pair<Node, Node> taylor = getTaylor(k, n);
    Node taylor_sum = taylor.first;
    // ru is x^{n+1}/(n+1)!
    Node ru = taylor.second;
    Trace("nl-trans") << "Taylor for " << k << " is : " << taylor.first
                      << std::endl;
    Trace("nl-trans") << "Taylor remainder for " << k << " is " << taylor.second
                      << std::endl;
    if (k == Kind::EXPONENTIAL)
    {
      pbounds.d_lower = taylor_sum;
      pbounds.d_upperNeg = nm->mkNode(Kind::ADD, taylor_sum, ru);
      pbounds.d_upperPos =
          nm->mkNode(Kind::MULT,
                     taylor_sum,
                     nm->mkNode(Kind::ADD, nm->mkConstReal(Rational(1)), ru));
    }
    else
    {
      Assert(k == Kind::SINE);
      Node l = nm->mkNode(Kind::SUB, taylor_sum, ru);
      Node u = nm->mkNode(Kind::ADD, taylor_sum, ru);
      pbounds.d_lower = l;
      pbounds.d_upperNeg = u;
      pbounds.d_upperPos = u;
    }
    Trace("nl-trans") << "Polynomial approximation for " << k
                      << " is: " << std::endl;
    Trace("nl-trans") << " Lower: " << pbounds.d_lower << std::endl;
    Trace("nl-trans") << " Upper (neg): " << pbounds.d_upperNeg << std::endl;
    Trace("nl-trans") << " Upper (pos): " << pbounds.d_upperPos << std::endl;
    d_poly_bounds[k].emplace(d, pbounds);
  }
  else
  {
    pbounds = it->second;
  }
}

std::uint64_t TaylorGenerator::getPolynomialApproximationBoundForArg(
    Kind k, Node c, std::uint64_t d, ApproximationBounds& pbounds)
{
  getPolynomialApproximationBounds(k, d, pbounds);
  Trace("nl-trans") << "c = " << c << std::endl;
  Assert(c.isConst());
  if (k == Kind::EXPONENTIAL && c.getConst<Rational>().sgn() == 1)
  {
    bool success = false;
    std::uint64_t ds = d;
    TNode ttrf = getTaylorVariable();
    TNode tc = c;
    Evaluator eval(nullptr);
    do
    {
      success = true;
      std::uint64_t n = 2 * ds;
      std::pair<Node, Node> taylor = getTaylor(k, n);
      // check that 1-c^{n+1}/(n+1)! > 0
      Node ru = taylor.second;
      Node rus = eval.eval(ru, {ttrf}, {tc});
      Assert(rus.isConst());
      if (rus.getConst<Rational>() > 1)
      {
        success = false;
        ds = ds + 1;
      }
    } while (!success);
    if (ds > d)
    {
      Trace("nl-ext-exp-taylor")
          << "*** Increase Taylor bound to " << ds << " > " << d << " for ("
          << k << " " << c << ")" << std::endl;
      // must use sound upper bound
      ApproximationBounds pboundss;
      getPolynomialApproximationBounds(k, ds, pboundss);
      pbounds.d_upperPos = pboundss.d_upperPos;
    }
    return ds;
  }
  return d;
}

std::pair<Node, Node> TaylorGenerator::getTfModelBounds(Node tf,
                                                        std::uint64_t d,
                                                        NlModel& model)
{
  // compute the model value of the argument
  Node c = model.computeAbstractModelValue(tf[0]);
  Assert(c.isConst());
  int csign = c.getConst<Rational>().sgn();
  Kind k = tf.getKind();
  if (csign == 0)
  {
    NodeManager* nm = NodeManager::currentNM();
    // at zero, its trivial
    if (k == Kind::SINE)
    {
      Node zero = nm->mkConstReal(Rational(0));
      return std::pair<Node, Node>(zero, zero);
    }
    Assert(k == Kind::EXPONENTIAL);
    Node one = nm->mkConstReal(Rational(1));
    return std::pair<Node, Node>(one, one);
  }
  bool isNeg = csign == -1;

  ApproximationBounds pbounds;
  getPolynomialApproximationBoundForArg(k, c, d, pbounds);

  std::vector<Node> bounds;
  TNode tfv = getTaylorVariable();
  TNode tfs = tf[0];
  Evaluator eval(nullptr);
  for (unsigned d2 = 0; d2 < 2; d2++)
  {
    Node pab = (d2 == 0 ? pbounds.d_lower
                        : (isNeg ? pbounds.d_upperNeg : pbounds.d_upperPos));
    if (!pab.isNull())
    {
      // { x -> M_A(tf[0]) }
      // Notice that we compute the model value of tfs first, so that
      // the call to rewrite below does not modify the term, where notice that
      // rewrite( x*x { x -> M_A(t) } ) = M_A(t)*M_A(t)
      // is not equal to
      // M_A( x*x { x -> t } ) = M_A( t*t )
      // where M_A denotes the abstract model.
      Node mtfs = model.computeAbstractModelValue(tfs);
      pab = eval.eval(pab, {tfv}, {mtfs});
      Assert(pab.isConst());
      bounds.push_back(pab);
    }
    else
    {
      bounds.push_back(Node::null());
    }
  }
  return std::pair<Node, Node>(bounds[0], bounds[1]);
}

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
