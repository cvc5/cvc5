/*********************                                                        */
/*! \file taylor_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Gereon Kremer, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Generate taylor approximations transcendental lemmas.
 **/

#include "theory/arith/nl/transcendental/taylor_generator.h"

#include "theory/arith/arith_utilities.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

TaylorGenerator::TaylorGenerator()
    : d_nm(NodeManager::currentNM()),
      d_taylor_real_fv(d_nm->mkBoundVar("x", d_nm->realType()))
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
  Node varpow = nm->mkConst(Rational(1));
  std::vector<Node> sum;
  for (std::uint64_t counter = 1; counter <= n; ++counter)
  {
    if (k == Kind::EXPONENTIAL)
    {
      // Maclaurin series for exponential:
      //   \sum_{n=0}^\infty x^n / n!
      sum.push_back(
          nm->mkNode(Kind::DIVISION, varpow, nm->mkConst<Rational>(factorial)));
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
                                            nm->mkConst<Rational>(sign),
                                            nm->mkConst<Rational>(factorial)),
                                 varpow));
      }
    }
    factorial *= counter;
    varpow =
        Rewriter::rewrite(nm->mkNode(Kind::MULT, d_taylor_real_fv, varpow));
  }
  Node taylor_sum = sum.size() == 1 ? sum[0] : nm->mkNode(Kind::PLUS, sum);

  Node taylor_rem =
      nm->mkNode(Kind::DIVISION, varpow, nm->mkConst<Rational>(factorial));

  auto res = std::make_pair(taylor_sum, taylor_rem);

  // put result in cache
  d_taylor_terms[k][n] = res;

  return res;
}

void TaylorGenerator::getPolynomialApproximationBounds(
    Kind k, unsigned d, std::vector<Node>& pbounds)
{
  if (d_poly_bounds[k][d].empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    // n is the Taylor degree we are currently considering
    unsigned n = 2 * d;
    // n must be even
    std::pair<Node, Node> taylor = getTaylor(k, n);
    Trace("nl-ext-tftp-debug2")
        << "Taylor for " << k << " is : " << taylor.first << std::endl;
    Node taylor_sum = Rewriter::rewrite(taylor.first);
    Trace("nl-ext-tftp-debug2")
        << "Taylor for " << k << " is (post-rewrite) : " << taylor_sum
        << std::endl;
    Trace("nl-ext-tftp-debug2")
        << "Taylor remainder for " << k << " is " << taylor.second << std::endl;
    // ru is x^{n+1}/(n+1)!
    Node ru = Rewriter::rewrite(taylor.second);
    Trace("nl-ext-tftp-debug2")
        << "Taylor remainder factor is (post-rewrite) : " << ru << std::endl;
    if (k == Kind::EXPONENTIAL)
    {
      pbounds.push_back(taylor_sum);
      pbounds.push_back(taylor_sum);
      pbounds.push_back(Rewriter::rewrite(
          nm->mkNode(Kind::MULT,
                     taylor_sum,
                     nm->mkNode(Kind::PLUS, nm->mkConst(Rational(1)), ru))));
      pbounds.push_back(
          Rewriter::rewrite(nm->mkNode(Kind::PLUS, taylor_sum, ru)));
    }
    else
    {
      Assert(k == Kind::SINE);
      Node l = Rewriter::rewrite(nm->mkNode(Kind::MINUS, taylor_sum, ru));
      Node u = Rewriter::rewrite(nm->mkNode(Kind::PLUS, taylor_sum, ru));
      pbounds.push_back(l);
      pbounds.push_back(l);
      pbounds.push_back(u);
      pbounds.push_back(u);
    }
    Trace("nl-ext-tf-tplanes")
        << "Polynomial approximation for " << k << " is: " << std::endl;
    Trace("nl-ext-tf-tplanes") << " Lower (pos): " << pbounds[0] << std::endl;
    Trace("nl-ext-tf-tplanes") << " Upper (pos): " << pbounds[2] << std::endl;
    Trace("nl-ext-tf-tplanes") << " Lower (neg): " << pbounds[1] << std::endl;
    Trace("nl-ext-tf-tplanes") << " Upper (neg): " << pbounds[3] << std::endl;
    d_poly_bounds[k][d].insert(
        d_poly_bounds[k][d].end(), pbounds.begin(), pbounds.end());
  }
  else
  {
    pbounds.insert(
        pbounds.end(), d_poly_bounds[k][d].begin(), d_poly_bounds[k][d].end());
  }
}

unsigned TaylorGenerator::getPolynomialApproximationBoundForArg(
    Kind k, Node c, unsigned d, std::vector<Node>& pbounds)
{
  getPolynomialApproximationBounds(k, d, pbounds);
  Assert(c.isConst());
  if (k == Kind::EXPONENTIAL && c.getConst<Rational>().sgn() == 1)
  {
    bool success = false;
    unsigned ds = d;
    TNode ttrf = getTaylorVariable();
    TNode tc = c;
    do
    {
      success = true;
      unsigned n = 2 * ds;
      std::pair<Node, Node> taylor = getTaylor(k, n);
      // check that 1-c^{n+1}/(n+1)! > 0
      Node ru = taylor.second;
      Node rus = ru.substitute(ttrf, tc);
      rus = Rewriter::rewrite(rus);
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
      std::vector<Node> pboundss;
      getPolynomialApproximationBounds(k, ds, pboundss);
      pbounds[2] = pboundss[2];
    }
    return ds;
  }
  return d;
}

std::pair<Node, Node> TaylorGenerator::getTfModelBounds(Node tf, unsigned d, NlModel& model)
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
      Node zero = nm->mkConst(Rational(0));
      return std::pair<Node, Node>(zero, zero);
    }
    Assert(k == Kind::EXPONENTIAL);
    Node one = nm->mkConst(Rational(1));
    return std::pair<Node, Node>(one, one);
  }
  bool isNeg = csign == -1;

  std::vector<Node> pbounds;
  getPolynomialApproximationBoundForArg(k, c, d, pbounds);

  std::vector<Node> bounds;
  TNode tfv = getTaylorVariable();
  TNode tfs = tf[0];
  for (unsigned d2 = 0; d2 < 2; d2++)
  {
    int index = d2 == 0 ? (isNeg ? 1 : 0) : (isNeg ? 3 : 2);
    Node pab = pbounds[index];
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
      pab = pab.substitute(tfv, mtfs);
      pab = Rewriter::rewrite(pab);
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
}  // namespace CVC4
