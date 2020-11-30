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

#include "theory/arith/nl/transcendental/sine_solver.h"

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

SineSolver::SineSolver(TranscendentalState* tstate) : d_data(tstate) {}

SineSolver::~SineSolver() {}

void SineSolver::checkInitialRefine()
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("nl-ext")
      << "Get initial refinement lemmas for transcendental functions..."
      << std::endl;
  for (std::pair<const Kind, std::vector<Node> >& tfl : d_data->d_funcMap)
  {
    if (tfl.first != Kind::SINE)
    {
      continue;
    }
    for (const Node& t : tfl.second)
    {
      // initial refinements
      if (d_tf_initial_refine.find(t) == d_tf_initial_refine.end())
      {
        d_tf_initial_refine[t] = true;
        Node lem;
        Node symn = nm->mkNode(Kind::SINE,
                               nm->mkNode(Kind::MULT, d_data->d_neg_one, t[0]));
        symn = Rewriter::rewrite(symn);
        // Can assume it is its own master since phase is split over 0,
        // hence  -pi <= t[0] <= pi implies -pi <= -t[0] <= pi.
        d_data->d_trMaster[symn] = symn;
        d_data->d_trSlaves[symn].insert(symn);
        Assert(d_data->d_trSlaves.find(t) != d_data->d_trSlaves.end());
        std::vector<Node> children;

        lem =
            nm->mkNode(Kind::AND,
                       // bounds
                       nm->mkNode(Kind::AND,
                                  nm->mkNode(Kind::LEQ, t, d_data->d_one),
                                  nm->mkNode(Kind::GEQ, t, d_data->d_neg_one)),
                       // symmetry
                       nm->mkNode(Kind::PLUS, t, symn).eqNode(d_data->d_zero),
                       // sign
                       nm->mkNode(Kind::EQUAL,
                                  nm->mkNode(Kind::LT, t[0], d_data->d_zero),
                                  nm->mkNode(Kind::LT, t, d_data->d_zero)),
                       // zero val
                       nm->mkNode(Kind::EQUAL,
                                  nm->mkNode(Kind::GT, t[0], d_data->d_zero),
                                  nm->mkNode(Kind::GT, t, d_data->d_zero)));
        lem = nm->mkNode(
            Kind::AND,
            lem,
            // zero tangent
            nm->mkNode(Kind::AND,
                       nm->mkNode(Kind::IMPLIES,
                                  nm->mkNode(Kind::GT, t[0], d_data->d_zero),
                                  nm->mkNode(Kind::LT, t, t[0])),
                       nm->mkNode(Kind::IMPLIES,
                                  nm->mkNode(Kind::LT, t[0], d_data->d_zero),
                                  nm->mkNode(Kind::GT, t, t[0]))),
            // pi tangent
            nm->mkNode(
                Kind::AND,
                nm->mkNode(
                    Kind::IMPLIES,
                    nm->mkNode(Kind::LT, t[0], d_data->d_pi),
                    nm->mkNode(Kind::LT,
                               t,
                               nm->mkNode(Kind::MINUS, d_data->d_pi, t[0]))),
                nm->mkNode(
                    Kind::IMPLIES,
                    nm->mkNode(Kind::GT, t[0], d_data->d_pi_neg),
                    nm->mkNode(
                        Kind::GT,
                        t,
                        nm->mkNode(Kind::MINUS, d_data->d_pi_neg, t[0])))));
        if (!lem.isNull())
        {
          d_data->d_im.addPendingArithLemma(lem, InferenceId::NL_T_INIT_REFINE);
        }
      }
    }
  }
}

void SineSolver::checkMonotonic()
{
  Trace("nl-ext") << "Get monotonicity lemmas for transcendental functions..."
                  << std::endl;

  auto it = d_data->d_funcMap.find(Kind::SINE);
  if (it == d_data->d_funcMap.end())
  {
    Trace("nl-ext-exp") << "No sine terms" << std::endl;
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
      Trace("nl-ext-tf-mono-debug") << "...tf term : " << a << std::endl;
      tf_args.push_back(a);
      tf_arg_to_term[a] = tf;
    }
  }

  if (tf_args.empty())
  {
    return;
  }

  sortByNlModel(
      tf_args.begin(), tf_args.end(), &d_data->d_model, true, false, true);

  std::vector<Node> mpoints = {d_data->d_pi,
                               d_data->d_pi_2,
                               d_data->d_zero,
                               d_data->d_pi_neg_2,
                               d_data->d_pi_neg};
  std::vector<Node> mpoints_vals;

  // get model values for points
  for (const auto& point : mpoints)
  {
    mpoints_vals.emplace_back(d_data->d_model.computeAbstractModelValue(point));
    Assert(mpoints_vals.back().isConst());
  }

  unsigned mdir_index = 0;
  int monotonic_dir = -1;
  Node mono_bounds[2];
  Node targ, targval, t, tval;
  for (const auto& sarg : tf_args)
  {
    Node sargval = d_data->d_model.computeAbstractModelValue(sarg);
    Assert(sargval.isConst());
    Node s = tf_arg_to_term[sarg];
    Node sval = d_data->d_model.computeAbstractModelValue(s);
    Assert(sval.isConst());

    // increment to the proper monotonicity region
    bool increment = true;
    while (increment && mdir_index < mpoints.size())
    {
      increment = false;
      Node pval = mpoints_vals[mdir_index];
      Assert(pval.isConst());
      if (sargval.getConst<Rational>() < pval.getConst<Rational>())
      {
        increment = true;
        Trace("nl-ext-tf-mono")
            << "...increment at " << sarg << " since model value is less than "
            << mpoints[mdir_index] << std::endl;
      }
      if (increment)
      {
        tval = Node::null();
        mono_bounds[1] = mpoints[mdir_index];
        mdir_index++;
        monotonic_dir = regionToMonotonicityDir(mdir_index);
        if (mdir_index < mpoints.size())
        {
          mono_bounds[0] = mpoints[mdir_index];
        }
        else
        {
          mono_bounds[0] = Node::null();
        }
      }
    }
    // store the concavity region
    d_data->d_tf_region[s] = mdir_index;
    Trace("nl-ext-concavity")
        << "Transcendental function " << s << " is in region #" << mdir_index;
    Trace("nl-ext-concavity") << ", arg model value = " << sargval << std::endl;

    if (!tval.isNull())
    {
      NodeManager* nm = NodeManager::currentNM();
      Node mono_lem;
      if (monotonic_dir == 1
          && sval.getConst<Rational>() > tval.getConst<Rational>())
      {
        mono_lem = nm->mkNode(Kind::IMPLIES,
                              nm->mkNode(Kind::GEQ, targ, sarg),
                              nm->mkNode(Kind::GEQ, t, s));
      }
      else if (monotonic_dir == -1
               && sval.getConst<Rational>() < tval.getConst<Rational>())
      {
        mono_lem = nm->mkNode(Kind::IMPLIES,
                              nm->mkNode(Kind::LEQ, targ, sarg),
                              nm->mkNode(Kind::LEQ, t, s));
      }
      if (!mono_lem.isNull())
      {
        if (!mono_bounds[0].isNull())
        {
          Assert(!mono_bounds[1].isNull());
          mono_lem = nm->mkNode(
              Kind::IMPLIES,
              nm->mkNode(Kind::AND,
                         mkBounded(mono_bounds[0], targ, mono_bounds[1]),
                         mkBounded(mono_bounds[0], sarg, mono_bounds[1])),
              mono_lem);
        }
        Trace("nl-ext-tf-mono")
            << "Monotonicity lemma : " << mono_lem << std::endl;

        d_data->d_im.addPendingArithLemma(mono_lem,
                                          InferenceId::NL_T_MONOTONICITY);
      }
    }
    // store the previous values
    targ = sarg;
    targval = sargval;
    t = s;
    tval = sval;
  }
}

void SineSolver::doTangentLemma(TNode e, TNode c, TNode poly_approx, int region)
{
  NodeManager* nm = NodeManager::currentNM();

  // compute tangent plane
  // Figure 3: T( x )
  // We use zero slope tangent planes, since the concavity of the Taylor
  // approximation cannot be easily established.
  int concavity = regionToConcavity(region);
  int mdir = regionToMonotonicityDir(region);
  Node lem = nm->mkNode(
      Kind::IMPLIES,
      nm->mkNode(
          Kind::AND,
          nm->mkNode(Kind::GEQ,
                     e[0],
                     mdir == concavity ? Node(c) : regionToLowerBound(region)),
          nm->mkNode(Kind::LEQ,
                     e[0],
                     mdir != concavity ? Node(c) : regionToUpperBound(region))),
      nm->mkNode(concavity == 1 ? Kind::GEQ : Kind::LEQ, e, poly_approx));

  Trace("nl-ext-sine") << "*** Tangent plane lemma (pre-rewrite): " << lem
                       << std::endl;
  lem = Rewriter::rewrite(lem);
  Trace("nl-ext-sine") << "*** Tangent plane lemma : " << lem << std::endl;
  Assert(d_data->d_model.computeAbstractModelValue(lem) == d_data->d_false);
  // Figure 3 : line 9
  d_data->d_im.addPendingArithLemma(lem, InferenceId::NL_T_TANGENT, nullptr, true);
}

void SineSolver::doSecantLemmas(TNode e,
                                TNode poly_approx,
                                TNode c,
                                TNode poly_approx_c,
                                unsigned d,
                                int region)
{
  d_data->doSecantLemmas(getSecantBounds(e, c, d, region),
                         poly_approx,
                         c,
                         poly_approx_c,
                         e,
                         d,
                         regionToConcavity(region));
}

std::pair<Node, Node> SineSolver::getSecantBounds(TNode e,
                                                  TNode c,
                                                  unsigned d,
                                                  int region)
{
  std::pair<Node, Node> bounds = d_data->getClosestSecantPoints(e, c, d);

  // Check if we already have neighboring secant points
  if (bounds.first.isNull())
  {
    // lower boundary point for this concavity region
    bounds.first = regionToLowerBound(region);
  }
  if (bounds.second.isNull())
  {
    // upper boundary point for this concavity region
    bounds.second = regionToUpperBound(region);
  }
  return bounds;
}

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
