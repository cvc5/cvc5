/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of solver for handling transcendental functions.
 */

#include "theory/arith/nl/transcendental/sine_solver.h"

#include <cmath>
#include <set>

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "expr/skolem_manager.h"
#include "options/arith_options.h"
#include "proof/proof.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/arith/nl/transcendental/transcendental_state.h"
#include "theory/rewriter.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {
namespace {

/**
 * Ensure a is in the main phase:
 *   -pi <= a <= pi
 */
inline Node mkValidPhase(TNode a, TNode pi)
{
  return mkBounded(
      NodeManager::currentNM()->mkNode(Kind::MULT, mkRationalNode(-1), pi),
      a,
      pi);
}
}  // namespace

SineSolver::SineSolver(TranscendentalState* tstate) : d_data(tstate) {}

SineSolver::~SineSolver() {}

void SineSolver::doPhaseShift(TNode a, TNode new_a, TNode y)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Assert(a.getKind() == Kind::SINE);
  Trace("nl-ext-tf") << "Basis sine : " << new_a << " for " << a << std::endl;
  Assert(!d_data->d_pi.isNull());
  Node shift = sm->mkDummySkolem("s", nm->integerType(), "number of shifts");
  // TODO (cvc4-projects #47) : do not introduce shift here, instead needs model-based
  // refinement for constant shifts (cvc4-projects #1284)
  Node lem = nm->mkNode(
      Kind::AND,
      mkValidPhase(y, d_data->d_pi),
      nm->mkNode(Kind::ITE,
                 mkValidPhase(a[0], d_data->d_pi),
                 a[0].eqNode(y),
                 a[0].eqNode(nm->mkNode(Kind::PLUS,
                                        y,
                                        nm->mkNode(Kind::MULT,
                                                   nm->mkConst(Rational(2)),
                                                   shift,
                                                   d_data->d_pi)))),
      new_a.eqNode(a));
  CDProof* proof = nullptr;
  if (d_data->isProofEnabled())
  {
    proof = d_data->getProof();
    proof->addStep(lem, PfRule::ARITH_TRANS_SINE_SHIFT, {}, {a[0], y, shift});
  }
  // note we must do preprocess on this lemma
  Trace("nl-ext-lemma") << "NonlinearExtension::Lemma : purify : " << lem
                        << std::endl;
  d_data->d_im.addPendingLemma(lem, InferenceId::ARITH_NL_T_PURIFY_ARG, proof);
}

void SineSolver::checkInitialRefine()
{
  NodeManager* nm = NodeManager::currentNM();
  for (std::pair<const Kind, std::vector<Node> >& tfl : d_data->d_funcMap)
  {
    if (tfl.first != Kind::SINE)
    {
      continue;
    }
    Trace("nl-ext") << "Get initial (sine) refinement lemmas for "
                       "transcendental functions..."
                    << std::endl;
    for (const Node& t : tfl.second)
    {
      // initial refinements
      if (d_tf_initial_refine.find(t) == d_tf_initial_refine.end())
      {
        d_tf_initial_refine[t] = true;
        Node symn = nm->mkNode(Kind::SINE,
                               nm->mkNode(Kind::MULT, d_data->d_neg_one, t[0]));
        symn = Rewriter::rewrite(symn);
        // Can assume it is its own master since phase is split over 0,
        // hence  -pi <= t[0] <= pi implies -pi <= -t[0] <= pi.
        d_data->d_trMaster[symn] = symn;
        d_data->d_trSlaves[symn].insert(symn);
        Assert(d_data->d_trSlaves.find(t) != d_data->d_trSlaves.end());

        {
          // sine bounds: -1 <= sin(t) <= 1
          Node lem = nm->mkNode(Kind::AND,
                                nm->mkNode(Kind::LEQ, t, d_data->d_one),
                                nm->mkNode(Kind::GEQ, t, d_data->d_neg_one));
          CDProof* proof = nullptr;
          if (d_data->isProofEnabled())
          {
            proof = d_data->getProof();
            proof->addStep(lem, PfRule::ARITH_TRANS_SINE_BOUNDS, {}, {t[0]});
          }
          d_data->d_im.addPendingLemma(
              lem, InferenceId::ARITH_NL_T_INIT_REFINE, proof);
        }
        {
          // sine symmetry: sin(t) - sin(-t) = 0
          Node lem = nm->mkNode(Kind::PLUS, t, symn).eqNode(d_data->d_zero);
          CDProof* proof = nullptr;
          if (d_data->isProofEnabled())
          {
            proof = d_data->getProof();
            proof->addStep(lem, PfRule::ARITH_TRANS_SINE_SYMMETRY, {}, {t[0]});
          }
          d_data->d_im.addPendingLemma(
              lem, InferenceId::ARITH_NL_T_INIT_REFINE, proof);
        }
        {
          // sine zero tangent:
          //   t > 0  =>  sin(t) < t
          //   t < 0  =>  sin(t) > t
          Node lem =
              nm->mkNode(Kind::AND,
                         nm->mkNode(Kind::IMPLIES,
                                    nm->mkNode(Kind::GT, t[0], d_data->d_zero),
                                    nm->mkNode(Kind::LT, t, t[0])),
                         nm->mkNode(Kind::IMPLIES,
                                    nm->mkNode(Kind::LT, t[0], d_data->d_zero),
                                    nm->mkNode(Kind::GT, t, t[0])));
          CDProof* proof = nullptr;
          if (d_data->isProofEnabled())
          {
            proof = d_data->getProof();
            proof->addStep(
                lem, PfRule::ARITH_TRANS_SINE_TANGENT_ZERO, {}, {t[0]});
          }
          d_data->d_im.addPendingLemma(
              lem, InferenceId::ARITH_NL_T_INIT_REFINE, proof);
        }
        {
          // sine pi tangent:
          //   t > -pi  =>  sin(t) > -pi-t
          //   t <  pi  =>  sin(t) <  pi-t
          Node lem = nm->mkNode(
              Kind::AND,
              nm->mkNode(
                  Kind::IMPLIES,
                  nm->mkNode(Kind::GT, t[0], d_data->d_pi_neg),
                  nm->mkNode(Kind::GT,
                             t,
                             nm->mkNode(Kind::MINUS, d_data->d_pi_neg, t[0]))),
              nm->mkNode(
                  Kind::IMPLIES,
                  nm->mkNode(Kind::LT, t[0], d_data->d_pi),
                  nm->mkNode(Kind::LT,
                             t,
                             nm->mkNode(Kind::MINUS, d_data->d_pi, t[0]))));
          CDProof* proof = nullptr;
          if (d_data->isProofEnabled())
          {
            proof = d_data->getProof();
            proof->addStep(
                lem, PfRule::ARITH_TRANS_SINE_TANGENT_PI, {}, {t[0]});
          }
          d_data->d_im.addPendingLemma(
              lem, InferenceId::ARITH_NL_T_INIT_REFINE, proof);
        }
        {
          Node lem =
              nm->mkNode(Kind::AND,
                         // sign
                         nm->mkNode(Kind::EQUAL,
                                    nm->mkNode(Kind::LT, t[0], d_data->d_zero),
                                    nm->mkNode(Kind::LT, t, d_data->d_zero)),
                         // zero val
                         nm->mkNode(Kind::EQUAL,
                                    nm->mkNode(Kind::GT, t[0], d_data->d_zero),
                                    nm->mkNode(Kind::GT, t, d_data->d_zero)));
          d_data->d_im.addPendingLemma(lem,
                                       InferenceId::ARITH_NL_T_INIT_REFINE);
        }
      }
    }
  }
}

void SineSolver::checkMonotonic()
{

  auto it = d_data->d_funcMap.find(Kind::SINE);
  if (it == d_data->d_funcMap.end())
  {
    Trace("nl-ext-exp") << "No sine terms" << std::endl;
    return;
  }
  Trace("nl-ext")
      << "Get monotonicity lemmas for (sine) transcendental functions..."
      << std::endl;

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

        d_data->d_im.addPendingLemma(mono_lem,
                                     InferenceId::ARITH_NL_T_MONOTONICITY);
      }
    }
    // store the previous values
    targ = sarg;
    targval = sargval;
    t = s;
    tval = sval;
  }
}

void SineSolver::doTangentLemma(
    TNode e, TNode c, TNode poly_approx, int region, std::uint64_t d)
{
  NodeManager* nm = NodeManager::currentNM();

  // compute tangent plane
  // Figure 3: T( x )
  // We use zero slope tangent planes, since the concavity of the Taylor
  // approximation cannot be easily established.
  Convexity convexity = regionToConvexity(region);
  int mdir = regionToMonotonicityDir(region);
  bool usec = (mdir == 1) == (convexity == Convexity::CONCAVE);
  Node lem = nm->mkNode(
      Kind::IMPLIES,
      nm->mkNode(
          Kind::AND,
          nm->mkNode(
              Kind::GEQ, e[0], usec ? regionToLowerBound(region) : Node(c)),
          nm->mkNode(
              Kind::LEQ, e[0], usec ? Node(c) : regionToUpperBound(region))),
      nm->mkNode(convexity == Convexity::CONVEX ? Kind::GEQ : Kind::LEQ,
                 e,
                 poly_approx));

  Trace("nl-ext-sine") << "*** Tangent plane lemma (pre-rewrite): " << lem
                       << std::endl;
  lem = Rewriter::rewrite(lem);
  Trace("nl-ext-sine") << "*** Tangent plane lemma : " << lem << std::endl;
  Assert(d_data->d_model.computeAbstractModelValue(lem) == d_data->d_false);
  // Figure 3 : line 9
  CDProof* proof = nullptr;
  if (d_data->isProofEnabled())
  {
    proof = d_data->getProof();
    if (convexity == Convexity::CONVEX)
    {
      if (usec)
      {
        proof->addStep(lem,
                       PfRule::ARITH_TRANS_SINE_APPROX_BELOW_NEG,
                       {},
                       {nm->mkConst<Rational>(2 * d),
                        e[0],
                        c,
                        regionToLowerBound(region),
                        c});
      }
      else
      {
        proof->addStep(lem,
                       PfRule::ARITH_TRANS_SINE_APPROX_BELOW_NEG,
                       {},
                       {nm->mkConst<Rational>(2 * d),
                        e[0],
                        c,
                        c,
                        regionToUpperBound(region)});
      }
    }
    else
    {
      if (usec)
      {
        proof->addStep(lem,
                       PfRule::ARITH_TRANS_SINE_APPROX_ABOVE_POS,
                       {},
                       {nm->mkConst<Rational>(2 * d),
                        e[0],
                        c,
                        regionToLowerBound(region),
                        c});
      }
      else
      {
        proof->addStep(lem,
                       PfRule::ARITH_TRANS_SINE_APPROX_ABOVE_POS,
                       {},
                       {nm->mkConst<Rational>(2 * d),
                        e[0],
                        c,
                        c,
                        regionToUpperBound(region)});
      }
    }
  }
  d_data->d_im.addPendingLemma(
      lem, InferenceId::ARITH_NL_T_TANGENT, proof, true);
}

void SineSolver::doSecantLemmas(TNode e,
                                TNode poly_approx,
                                TNode c,
                                TNode poly_approx_c,
                                unsigned d,
                                unsigned actual_d,
                                int region)
{
  d_data->doSecantLemmas(getSecantBounds(e, c, d, region),
                         poly_approx,
                         c,
                         poly_approx_c,
                         e,
                         regionToConvexity(region),
                         d,
                         actual_d);
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
}  // namespace cvc5
