/*********************                                                        */
/*! \file transcendental_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of solver for handling transcendental functions.
 **/

#include "theory/arith/nl/transcendental/exponential_solver.h"

#include <cmath>
#include <set>

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "options/arith_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

ExponentialSolver::ExponentialSolver(TranscendentalState* tstate)
    : d_data(tstate)
{
}

ExponentialSolver::~ExponentialSolver() {}

void ExponentialSolver::checkInitialRefine()
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("nl-ext")
      << "Get initial refinement lemmas for transcendental functions..."
      << std::endl;
  for (std::pair<const Kind, std::vector<Node> >& tfl : d_data->d_funcMap)
  {
    if (tfl.first != Kind::EXPONENTIAL)
    {
      continue;
    }
    Assert(tfl.first == Kind::EXPONENTIAL);
    for (const Node& t : tfl.second)
    {
      // initial refinements
      if (d_tf_initial_refine.find(t) == d_tf_initial_refine.end())
      {
        d_tf_initial_refine[t] = true;
        Node lem;
        // ( exp(x) > 0 ) ^ ( x=0 <=> exp( x ) = 1 ) ^ ( x < 0 <=> exp( x ) <
        // 1 ) ^ ( x <= 0 V exp( x ) > x + 1 )
        lem = nm->mkNode(
            Kind::AND,
            nm->mkNode(Kind::GT, t, d_data->d_zero),
            nm->mkNode(Kind::EQUAL,
                       t[0].eqNode(d_data->d_zero),
                       t.eqNode(d_data->d_one)),
            nm->mkNode(Kind::EQUAL,
                       nm->mkNode(Kind::LT, t[0], d_data->d_zero),
                       nm->mkNode(Kind::LT, t, d_data->d_one)),
            nm->mkNode(
                Kind::OR,
                nm->mkNode(Kind::LEQ, t[0], d_data->d_zero),
                nm->mkNode(
                    Kind::GT, t, nm->mkNode(Kind::PLUS, t[0], d_data->d_one))));
        if (!lem.isNull())
        {
          d_data->d_im.addPendingArithLemma(lem, InferenceId::NL_T_INIT_REFINE);
        }
      }
    }
  }
}

void ExponentialSolver::checkMonotonic()
{
  Trace("nl-ext") << "Get monotonicity lemmas for transcendental functions..."
                  << std::endl;

  auto it = d_data->d_funcMap.find(Kind::EXPONENTIAL);
  if (it == d_data->d_funcMap.end())
  {
    Trace("nl-ext-exp") << "No exponential terms" << std::endl;
    return;
  }

  // sort arguments of all transcendentals
  std::vector<Node> tf_args;
  std::map<Node, Node> tf_arg_to_term;

  for (const Node& tf : it->second)
  {
    Node a = tf[0];
    Node mvaa = d_data->d_model.computeAbstractModelValue(a);
    if (mvaa.isConst())
    {
      Trace("nl-ext-exp") << "...tf term : " << a << std::endl;
      tf_args.push_back(a);
      tf_arg_to_term[a] = tf;
    }
  }

  if (tf_args.empty())
  {
    return;
  }

  SortNlModel smv;
  smv.d_nlm = &d_data->d_model;
  // sort by concrete values
  smv.d_isConcrete = true;
  smv.d_reverse_order = true;
  std::sort(tf_args.begin(), tf_args.end(), smv);

  Node targ, targval, t, tval;
  for (const auto& sarg: tf_args) {
    Node sargval = d_data->d_model.computeAbstractModelValue(sarg);
    Assert(sargval.isConst());
    Node s = tf_arg_to_term[sarg];
    Node sval = d_data->d_model.computeAbstractModelValue(s);
    Assert(sval.isConst());

    // store the concavity region
    d_data->d_tf_region[s] = 1;
    Trace("nl-ext-concavity") << ", arg model value = " << sargval << std::endl;

    if (!tval.isNull() && sval.getConst<Rational>() > tval.getConst<Rational>())
    {
      NodeManager* nm = NodeManager::currentNM();
      Node mono_lem = nm->mkNode(Kind::IMPLIES,
                                 nm->mkNode(Kind::GEQ, targ, sarg),
                                 nm->mkNode(Kind::GEQ, t, s));
      Trace("nl-ext-exp")
          << "Monotonicity lemma : " << mono_lem << std::endl;

      d_data->d_im.addPendingArithLemma(mono_lem,
                                        InferenceId::NL_T_MONOTONICITY);
    }
    // store the previous values
    targ = sarg;
    targval = sargval;
    t = s;
    tval = sval;
  }
}

bool ExponentialSolver::checkTfTangentPlanesFun(Node tf,
                                                   unsigned d)
{
  NodeManager* nm = NodeManager::currentNM();
  //Kind k = tf.getKind();
  // this should only be run on master applications
  Assert(d_data->d_trSlaves.find(tf) != d_data->d_trSlaves.end());

  // Figure 3 : c
  Node c = d_data->d_model.computeAbstractModelValue(tf[0]);
  int csign = c.getConst<Rational>().sgn();
  if (csign == 0)
  {
    // no secant/tangent plane is necessary
    return true;
  }
  Assert(csign == 1 || csign == -1);

  // Figure 3: P_l, P_u
  // mapped to for signs of c
  std::map<int, Node> poly_approx_bounds[2];
  std::vector<Node> pbounds;
  d_data->d_taylor.getPolynomialApproximationBoundForArg(Kind::EXPONENTIAL, c, d, pbounds);
  poly_approx_bounds[0][1] = pbounds[0];
  poly_approx_bounds[0][-1] = pbounds[1];
  poly_approx_bounds[1][1] = pbounds[2];
  poly_approx_bounds[1][-1] = pbounds[3];

  // Figure 3 : v
  Node v = d_data->d_model.computeAbstractModelValue(tf);

  // check value of tf
  Trace("nl-ext-tftp-debug") << "Process tangent plane refinement for " << tf
                             << ", degree " << d << "..." << std::endl;
  Trace("nl-ext-tftp-debug") << "  value in model : " << v << std::endl;
  Trace("nl-ext-tftp-debug") << "  arg value in model : " << c << std::endl;

  std::vector<Node> taylor_vars;
  taylor_vars.push_back(d_data->d_taylor.getTaylorVariable());

  // compute the concavity
  std::unordered_map<Node, int, NodeHashFunction>::iterator itr =
      d_data->d_tf_region.find(tf);
  if (itr != d_data->d_tf_region.end())
  {
    Assert(itr->second == 1);
    Trace("nl-ext-tftp-debug") << "  region is : 1" << std::endl;
  }
  // Figure 3 : conc
  Trace("nl-ext-tftp-debug") << "  concavity is : 1" << std::endl;
  // bounds for which we are this concavity
  // Figure 3: < l, u >
  Node bounds[2];

  // Figure 3: P
  Node poly_approx;

  // compute whether this is a tangent refinement or a secant refinement
  bool is_tangent = false;
  bool is_secant = false;
  std::pair<Node, Node> mvb = d_data->d_taylor.getTfModelBounds(tf, d, d_data->d_model);
  // this is the approximated value of tf(c), which is a value such that:
  //    M_A(tf(c)) >= poly_appox_c >= tf(c) or
  //    M_A(tf(c)) <= poly_appox_c <= tf(c)
  // In other words, it is a better approximation of the true value of tf(c)
  // in the case that we add a refinement lemma. We use this value in the
  // refinement schemas below.
  Node poly_approx_c;
  for (unsigned r = 0; r < 2; r++)
  {
    Node pab = poly_approx_bounds[r][csign];
    Node v_pab = r == 0 ? mvb.first : mvb.second;
    if (!v_pab.isNull())
    {
      Trace("nl-ext-tftp-debug2")
          << "...model value of " << pab << " is " << v_pab << std::endl;

      Assert(v_pab.isConst());
      Node comp = nm->mkNode(r == 0 ? Kind::LT : Kind::GT, v, v_pab);
      Trace("nl-ext-tftp-debug2") << "...compare : " << comp << std::endl;
      Node compr = Rewriter::rewrite(comp);
      Trace("nl-ext-tftp-debug2") << "...got : " << compr << std::endl;
      if (compr == d_data->d_true)
      {
        poly_approx_c = v_pab;
        // beyond the bounds
        if (r == 0)
        {
          poly_approx = poly_approx_bounds[r][csign];
          is_tangent = true;
          is_secant = false;
        }
        else
        {
          poly_approx = poly_approx_bounds[r][csign];
          is_tangent = false;
          is_secant = true;
        }
        if (Trace.isOn("nl-ext-tftp"))
        {
          Trace("nl-ext-tftp") << "*** Outside boundary point (";
          Trace("nl-ext-tftp") << (r == 0 ? "low" : "high") << ") ";
          printRationalApprox("nl-ext-tftp", v_pab);
          Trace("nl-ext-tftp") << ", will refine..." << std::endl;
          Trace("nl-ext-tftp")
              << "    poly_approx = " << poly_approx << std::endl;
          Trace("nl-ext-tftp")
              << "    is_tangent = " << is_tangent << std::endl;
          Trace("nl-ext-tftp") << "    is_secant = " << is_secant << std::endl;
        }
        break;
      }
      else
      {
        Trace("nl-ext-tftp")
            << "  ...within " << (r == 0 ? "low" : "high") << " bound : ";
        printRationalApprox("nl-ext-tftp", v_pab);
        Trace("nl-ext-tftp") << std::endl;
      }
    }
  }

  // Figure 3: P( c )
  if (is_tangent || is_secant)
  {
    Trace("nl-ext-tftp-debug2")
        << "...poly approximation at c is " << poly_approx_c << std::endl;
  }
  else
  {
    // we may want to continue getting better bounds
    return false;
  }

  if (is_tangent)
  {
    // compute tangent plane
    // Figure 3: T( x )
    // We use zero slope tangent planes, since the concavity of the Taylor
    // approximation cannot be easily established.
    Node tplane = poly_approx_c;

    Node lem = nm->mkNode(Kind::GEQ, tf, tplane);
    std::vector<Node> antec;
    for (unsigned i = 0; i < 2; i++)
    {
      // Tangent plane is valid in the interval [c,u) if the slope of the
      // function matches its concavity, and is valid in (l, c] otherwise.
      Node use_bound = (i == 0) ? c : bounds[i];
      if (!use_bound.isNull())
      {
        Node ant = nm->mkNode(i == 0 ? Kind::GEQ : Kind::LEQ, tf[0], use_bound);
        antec.push_back(ant);
      }
    }
    if (!antec.empty())
    {
      Node antec_n = antec.size() == 1 ? antec[0] : nm->mkNode(Kind::AND, antec);
      lem = nm->mkNode(Kind::IMPLIES, antec_n, lem);
    }
    Trace("nl-ext-tftp-debug2")
        << "*** Tangent plane lemma (pre-rewrite): " << lem << std::endl;
    lem = Rewriter::rewrite(lem);
    Trace("nl-ext-tftp-lemma")
        << "*** Tangent plane lemma : " << lem << std::endl;
    Assert(d_data->d_model.computeAbstractModelValue(lem) == d_data->d_false);
    // Figure 3 : line 9
    d_data->d_im.addPendingArithLemma(lem, InferenceId::NL_T_TANGENT, true);
  }
  else if (is_secant)
  {
    // bounds are the minimum and maximum previous secant points
    // should not repeat secant points: secant lemmas should suffice to
    // rule out previous assignment
    Assert(std::find(
               d_data->d_secant_points[tf][d].begin(), d_data->d_secant_points[tf][d].end(), c)
           == d_data->d_secant_points[tf][d].end());
    // Insert into the (temporary) vector. We do not update this vector
    // until we are sure this secant plane lemma has been processed. We do
    // this by mapping the lemma to a side effect below.
    std::vector<Node> spoints = d_data->d_secant_points[tf][d];
    spoints.push_back(c);

    // sort
    SortNlModel smv;
    smv.d_nlm = &d_data->d_model;
    smv.d_isConcrete = true;
    std::sort(spoints.begin(), spoints.end(), smv);
    // get the resulting index of c
    unsigned index =
        std::find(spoints.begin(), spoints.end(), c) - spoints.begin();
    // bounds are the next closest upper/lower bound values
    if (index > 0)
    {
      bounds[0] = spoints[index - 1];
    }
    else
    {
      // otherwise, we use the lower boundary point for this concavity
      // region
        // pick c-1
        bounds[0] = Rewriter::rewrite(nm->mkNode(Kind::MINUS, c, d_data->d_one));
    }
    if (index < spoints.size() - 1)
    {
      bounds[1] = spoints[index + 1];
    }
    else
    {
      // otherwise, we use the upper boundary point for this concavity
      // region
        // pick c+1
        bounds[1] = Rewriter::rewrite(nm->mkNode(Kind::PLUS, c, d_data->d_one));
    }
    Trace("nl-ext-tftp-debug2") << "...secant bounds are : " << bounds[0]
                                << " ... " << bounds[1] << std::endl;

    // the secant plane may be conjunction of 1-2 guarded inequalities
    std::vector<Node> lemmaConj;
    for (unsigned s = 0; s < 2; s++)
    {
      // compute secant plane
      Assert(!poly_approx.isNull());
      Assert(!bounds[s].isNull());
      // take the model value of l or u (since may contain PI)
      Node b = d_data->d_model.computeAbstractModelValue(bounds[s]);
      Trace("nl-ext-tftp-debug2") << "...model value of bound " << bounds[s]
                                  << " is " << b << std::endl;
      Assert(b.isConst());
      if (c != b)
      {
        // Figure 3 : P(l), P(u), for s = 0,1
        Node poly_approx_b;
        std::vector<Node> taylor_subs;
        taylor_subs.push_back(b);
        Assert(taylor_vars.size() == taylor_subs.size());
        poly_approx_b = poly_approx.substitute(taylor_vars.begin(),
                                               taylor_vars.end(),
                                               taylor_subs.begin(),
                                               taylor_subs.end());
        // Figure 3: S_l( x ), S_u( x ) for s = 0,1
        Node splane;
        Node rcoeff_n = Rewriter::rewrite(nm->mkNode(Kind::MINUS, b, c));
        Assert(rcoeff_n.isConst());
        Rational rcoeff = rcoeff_n.getConst<Rational>();
        Assert(rcoeff.sgn() != 0);
        poly_approx_b = Rewriter::rewrite(poly_approx_b);
        poly_approx_c = Rewriter::rewrite(poly_approx_c);
        splane = nm->mkNode(
            Kind::PLUS,
            poly_approx_b,
            nm->mkNode(Kind::MULT,
                       nm->mkNode(Kind::MINUS, poly_approx_b, poly_approx_c),
                       nm->mkConst(Rational(1) / rcoeff),
                       nm->mkNode(Kind::MINUS, tf[0], b)));

        Node lem = nm->mkNode(Kind::LEQ, tf, splane);
        // With respect to Figure 3, this is slightly different.
        // In particular, we chose b to be the model value of bounds[s],
        // which is a constant although bounds[s] may not be (e.g. if it
        // contains PI).
        // To ensure that c...b does not cross an inflection point,
        // we guard with the symbolic version of bounds[s].
        // This leads to lemmas e.g. of this form:
        //   ( c <= x <= PI/2 ) => ( sin(x) < ( P( b ) - P( c ) )*( x -
        //   b ) + P( b ) )
        // where b = (PI/2)^M, the current value of PI/2 in the model.
        // This is sound since we are guarded by the symbolic
        // representation of PI/2.
        Node antec_n =
            nm->mkNode(Kind::AND,
                       nm->mkNode(Kind::GEQ, tf[0], s == 0 ? bounds[s] : c),
                       nm->mkNode(Kind::LEQ, tf[0], s == 0 ? c : bounds[s]));
        lem = nm->mkNode(Kind::IMPLIES, antec_n, lem);
        Trace("nl-ext-tftp-debug2")
            << "*** Secant plane lemma (pre-rewrite) : " << lem << std::endl;
        lem = Rewriter::rewrite(lem);
        Trace("nl-ext-tftp-lemma")
            << "*** Secant plane lemma : " << lem << std::endl;
        lemmaConj.push_back(lem);
        Assert(d_data->d_model.computeAbstractModelValue(lem) == d_data->d_false);
      }
    }
    // Figure 3 : line 22
    Assert(!lemmaConj.empty());
    Node lem =
        lemmaConj.size() == 1 ? lemmaConj[0] : nm->mkNode(Kind::AND, lemmaConj);
    NlLemma nlem(lem, LemmaProperty::NONE, nullptr, InferenceId::NL_T_SECANT);
    // The side effect says that if lem is added, then we should add the
    // secant point c for (tf,d).
    nlem.d_secantPoint.push_back(std::make_tuple(tf, d, c));
    d_data->d_im.addPendingArithLemma(nlem, true);
  }
  return true;
}

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
