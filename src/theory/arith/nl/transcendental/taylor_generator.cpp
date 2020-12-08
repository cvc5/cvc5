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
      d_taylor_real_fv(d_nm->mkBoundVar("x", d_nm->realType())),
      d_taylor_real_fv_base(d_nm->mkBoundVar("a", d_nm->realType())),
      d_taylor_real_fv_base_rem(d_nm->mkBoundVar("b", d_nm->realType()))
{
}

TNode TaylorGenerator::getTaylorVariable() { return d_taylor_real_fv; }

std::pair<Node, Node> TaylorGenerator::getTaylor(TNode fa, std::uint64_t n)
{
  NodeManager* nm = NodeManager::currentNM();
  Node d_zero = nm->mkConst(Rational(0));

  Assert(n > 0);
  Node fac;  // what term we cache for fa
  if (fa[0] == d_zero)
  {
    // optimization : simpler to compute (x-fa[0])^n if we are centered around 0
    fac = fa;
  }
  else
  {
    // otherwise we use a standard factor a in (x-a)^n
    fac = nm->mkNode(fa.getKind(), d_taylor_real_fv_base);
  }
  Node taylor_rem;
  Node taylor_sum;
  // check if we have already computed this Taylor series
  auto itt = s_taylor_sum[fac].find(n);
  if (itt == s_taylor_sum[fac].end())
  {
    Node i_exp_base;
    if (fa[0] == d_zero)
    {
      i_exp_base = d_taylor_real_fv;
    }
    else
    {
      i_exp_base = Rewriter::rewrite(
          nm->mkNode(Kind::MINUS, d_taylor_real_fv, d_taylor_real_fv_base));
    }
    Node i_derv = fac;
    Node i_fact = nm->mkConst(Rational(1));
    Node i_exp = i_fact;
    int i_derv_status = 0;
    unsigned counter = 0;
    std::vector<Node> sum;
    do
    {
      counter++;
      if (fa.getKind() == Kind::EXPONENTIAL)
      {
        // unchanged
      }
      else if (fa.getKind() == Kind::SINE)
      {
        if (i_derv_status % 2 == 1)
        {
          Node pi = nm->mkNullaryOperator(nm->realType(), Kind::PI);
          Node pi_2 = Rewriter::rewrite(nm->mkNode(
              Kind::MULT, pi, nm->mkConst(Rational(1) / Rational(2))));

          Node arg = nm->mkNode(Kind::PLUS, pi_2, d_taylor_real_fv_base);
          i_derv = nm->mkNode(Kind::SINE, arg);
        }
        else
        {
          i_derv = fa;
        }
        if (i_derv_status >= 2)
        {
          i_derv = nm->mkNode(Kind::MINUS, d_zero, i_derv);
        }
        i_derv = Rewriter::rewrite(i_derv);
        i_derv_status = i_derv_status == 3 ? 0 : i_derv_status + 1;
      }
      if (counter == (n + 1))
      {
        TNode x = d_taylor_real_fv_base;
        i_derv = i_derv.substitute(x, d_taylor_real_fv_base_rem);
      }
      Node curr = nm->mkNode(
          Kind::MULT, nm->mkNode(Kind::DIVISION, i_derv, i_fact), i_exp);
      if (counter == (n + 1))
      {
        taylor_rem = curr;
      }
      else
      {
        sum.push_back(curr);
        i_fact = Rewriter::rewrite(
            nm->mkNode(Kind::MULT, nm->mkConst(Rational(counter)), i_fact));
        i_exp = Rewriter::rewrite(nm->mkNode(Kind::MULT, i_exp_base, i_exp));
      }
    } while (counter <= n);
    taylor_sum = sum.size() == 1 ? sum[0] : nm->mkNode(Kind::PLUS, sum);

    if (fac[0] != d_taylor_real_fv_base)
    {
      TNode x = d_taylor_real_fv_base;
      taylor_sum = taylor_sum.substitute(x, fac[0]);
    }

    // cache
    s_taylor_sum[fac][n] = taylor_sum;
    d_taylor_rem[fac][n] = taylor_rem;
  }
  else
  {
    taylor_sum = itt->second;
    Assert(d_taylor_rem[fac].find(n) != d_taylor_rem[fac].end());
    taylor_rem = d_taylor_rem[fac][n];
  }

  // must substitute for the argument if we were using a different lookup
  if (fa[0] != fac[0])
  {
    TNode x = d_taylor_real_fv_base;
    taylor_sum = taylor_sum.substitute(x, fa[0]);
  }
  return std::pair<Node, Node>(taylor_sum, taylor_rem);
}

void TaylorGenerator::getPolynomialApproximationBounds(
    Kind k, unsigned d, std::vector<Node>& pbounds)
{
  if (d_poly_bounds[k][d].empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    Node tft = nm->mkNode(k, nm->mkConst(Rational(0)));
    // n is the Taylor degree we are currently considering
    unsigned n = 2 * d;
    // n must be even
    std::pair<Node, Node> taylor = getTaylor(tft, n);
    Trace("nl-ext-tftp-debug2")
        << "Taylor for " << k << " is : " << taylor.first << std::endl;
    Node taylor_sum = Rewriter::rewrite(taylor.first);
    Trace("nl-ext-tftp-debug2")
        << "Taylor for " << k << " is (post-rewrite) : " << taylor_sum
        << std::endl;
    Assert(taylor.second.getKind() == Kind::MULT);
    Assert(taylor.second.getNumChildren() == 2);
    Assert(taylor.second[0].getKind() == Kind::DIVISION);
    Trace("nl-ext-tftp-debug2")
        << "Taylor remainder for " << k << " is " << taylor.second << std::endl;
    // ru is x^{n+1}/(n+1)!
    Node ru = nm->mkNode(Kind::DIVISION, taylor.second[1], taylor.second[0][1]);
    ru = Rewriter::rewrite(ru);
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
    NodeManager* nm = NodeManager::currentNM();
    Node tft = nm->mkNode(k, nm->mkConst(Rational(0)));
    bool success = false;
    unsigned ds = d;
    TNode ttrf = getTaylorVariable();
    TNode tc = c;
    do
    {
      success = true;
      unsigned n = 2 * ds;
      std::pair<Node, Node> taylor = getTaylor(tft, n);
      // check that 1-c^{n+1}/(n+1)! > 0
      Node ru =
          nm->mkNode(Kind::DIVISION, taylor.second[1], taylor.second[0][1]);
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
