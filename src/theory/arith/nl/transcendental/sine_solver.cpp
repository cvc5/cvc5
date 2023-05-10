/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

SineSolver::SineSolver(Env& env, TranscendentalState* tstate)
    : EnvObj(env), d_data(tstate)
{
  NodeManager* nm = NodeManager::currentNM();
  Node zero = nm->mkConstReal(Rational(0));
  Node one = nm->mkConstReal(Rational(1));
  Node negOne = nm->mkConstReal(Rational(-1));
  d_pi = nm->mkNullaryOperator(nm->realType(), Kind::PI);
  Node pi_2 = nm->mkNode(Kind::MULT, nm->mkConstReal(Rational(1, 2)), d_pi);
  Node pi_neg_2 =
      nm->mkNode(Kind::MULT, nm->mkConstReal(Rational(-1, 2)), d_pi);
  d_neg_pi = nm->mkNode(Kind::MULT, nm->mkConstInt(Rational(-1)), d_pi);
  d_mpoints.push_back(d_pi);
  d_mpointsSine[d_pi] = zero;
  d_mpoints.push_back(pi_2);
  d_mpointsSine[pi_2] = one;
  d_mpoints.push_back(zero);
  d_mpointsSine[zero] = zero;
  d_mpoints.push_back(pi_neg_2);
  d_mpointsSine[pi_neg_2] = negOne;
  d_mpoints.push_back(d_neg_pi);
  d_mpointsSine[d_neg_pi] = zero;
}

SineSolver::~SineSolver() {}

void SineSolver::doReductions()
{
  NodeManager* nm = NodeManager::currentNM();
  std::map<Kind, std::vector<Node> >::iterator it =
      d_data->d_funcMap.find(kind::SINE);
  if (it == d_data->d_funcMap.end())
  {
    return;
  }
  std::map<Node, Node> mpvs;
  for (std::pair<const Node, Node>& m : d_mpointsSine)
  {
    Node mv = d_data->d_model.computeAbstractModelValue(m.first);
    mpvs[mv] = m.first;
  }
  std::map<Node, Node> valForSym;
  std::vector<Node> nreduced;
  for (const Node& tf : it->second)
  {
    Node mva = d_data->d_model.computeAbstractModelValue(tf[0]);
    Node mv = d_data->d_model.computeAbstractModelValue(tf);
    Node mvaNeg = nm->mkConstReal(-mva.getConst<Rational>());
    std::map<Node, Node>::iterator itv = valForSym.find(mvaNeg);
    bool reduced = false;
    if (itv != valForSym.end())
    {
      Node mvs = d_data->d_model.computeAbstractModelValue(itv->second);
      if (mvs.getConst<Rational>() != -mv.getConst<Rational>())
      {
        Node lem =
            nm->mkNode(kind::IMPLIES,
                       tf[0].eqNode(nm->mkNode(kind::NEG, itv->second[0])),
                       tf.eqNode(nm->mkNode(kind::NEG, itv->second)));
        d_data->d_im.addPendingLemma(
            lem, InferenceId::ARITH_NL_T_SINE_SYMM, nullptr);
      }
      // we do not consider it reduced currently, since we require setting
      // approximate bounds for it, alternatively we could carry the negation
      // of the approximation in the transcendental solver
    }
    else
    {
      valForSym[mva] = tf;
      itv = mpvs.find(mva);
      if (itv != mpvs.end())
      {
        Assert(d_mpointsSine.find(itv->second) != d_mpointsSine.end());
        Node mvs = d_mpointsSine[itv->second];
        if (mv != mvs)
        {
          // the argument is a boundary point, we reduce it if not already done
          // so
          Node lem = nm->mkNode(
              kind::IMPLIES, tf[0].eqNode(itv->second), tf.eqNode(mvs));
          d_data->d_im.addPendingLemma(
              lem, InferenceId::ARITH_NL_T_SINE_BOUNDARY_REDUCE, nullptr);
        }
        else
        {
          // remember that the argument is equal to the boundary point
          Trace("nl-ext") << "SineSolver::doReductions: substitution: " << tf[0]
                          << " -> " << itv->second << std::endl;
          d_data->d_model.addSubstitution(tf[0], itv->second);
          // all congruent transcendental functions are exactly equal to its
          // value
          d_data->addModelBoundForPurifyTerm(tf, mvs, mvs);
        }
        reduced = true;
      }
    }
    if (!reduced)
    {
      nreduced.push_back(tf);
    }
  }
  if (nreduced.size() < it->second.size())
  {
    it->second = nreduced;
  }
}

Node SineSolver::getPhaseShiftLemma(const Node& x, const Node& y, const Node& s)
{
  NodeManager* nm = NodeManager::currentNM();
  Node xr = (x.getType().isInteger() ? nm->mkNode(Kind::TO_REAL, x) : x);
  Node yr = (y.getType().isInteger() ? nm->mkNode(Kind::TO_REAL, y) : y);
  Node mone = nm->mkConstReal(Rational(-1));
  Node pi = nm->mkNullaryOperator(nm->realType(), PI);
  return nm->mkAnd(std::vector<Node>{
      nm->mkNode(GEQ, y, nm->mkNode(MULT, mone, pi)),
      nm->mkNode(LEQ, y, pi),
      nm->mkNode(IS_INTEGER, s),
      nm->mkNode(ITE,
                 nm->mkAnd(std::vector<Node>{
                     nm->mkNode(GEQ, x, nm->mkNode(MULT, mone, pi)),
                     nm->mkNode(LEQ, x, pi),
                 }),
                 xr.eqNode(yr),
                 xr.eqNode(nm->mkNode(
                     ADD, y, nm->mkNode(MULT, nm->mkConstReal(2), s, pi)))),
      nm->mkNode(SINE, y).eqNode(nm->mkNode(SINE, x))});
}

void SineSolver::doPhaseShift(TNode a, TNode new_a)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Assert(a.getKind() == Kind::SINE);
  CDProof* proof = nullptr;
  Node lem;
  Trace("nl-ext-tf") << "Basis sine : " << new_a << " for " << a << std::endl;
  InferenceId iid;
  if (TranscendentalState::isSimplePurify(a))
  {
    lem = nm->mkNode(Kind::AND, a.eqNode(new_a), a[0].eqNode(new_a[0]));
    if (d_data->isProofEnabled())
    {
      // simple to justify
      proof = d_data->getProof();
      proof->addStep(lem, PfRule::MACRO_SR_PRED_INTRO, {}, {lem});
    }
    iid = InferenceId::ARITH_NL_T_PURIFY_ARG;
  }
  else
  {
    Node shift = sm->mkDummySkolem("s", nm->realType(), "number of shifts");
    // TODO (cvc4-projects #47) : do not introduce shift here, instead needs
    // model-based refinement for constant shifts (cvc4-projects #1284)
    lem = getPhaseShiftLemma(a[0], new_a[0], shift);
    if (d_data->isProofEnabled())
    {
      proof = d_data->getProof();
      proof->addStep(
          lem, PfRule::ARITH_TRANS_SINE_SHIFT, {}, {a[0], new_a[0], shift});
    }
    iid = InferenceId::ARITH_NL_T_PURIFY_ARG_PHASE_SHIFT;
  }
  // note we must do preprocess on this lemma
  Trace("nl-ext-lemma") << "NonlinearExtension::Lemma : purify : " << lem
                        << std::endl;
  d_data->d_im.addPendingLemma(lem, iid, proof);
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
        Trace("nl-ext-debug") << "Process initial refine " << t << std::endl;
        d_tf_initial_refine[t] = true;
        Assert(d_data->isPurified(t));
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
                  nm->mkNode(Kind::GT, t[0], d_neg_pi),
                  nm->mkNode(
                      Kind::GT, t, nm->mkNode(Kind::SUB, d_neg_pi, t[0]))),
              nm->mkNode(
                  Kind::IMPLIES,
                  nm->mkNode(Kind::LT, t[0], d_pi),
                  nm->mkNode(Kind::LT, t, nm->mkNode(Kind::SUB, d_pi, t[0]))));
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

  // Sound lower (index=0), upper (index=1) bounds for the above points. We
  // compute this by plugging in the upper and lower bound of pi.
  std::vector<Node> mpointsBound[2];
  TNode tpi = d_pi;
  for (size_t j = 0; j < 5; j++)
  {
    Node point = d_mpoints[j];
    for (size_t i = 0; i < 2; i++)
    {
      Node mpointapprox = point;
      if (j != 2)
      {
        // substitute the lower or upper bound of pi
        TNode tb = d_data->d_pi_bound[i];
        mpointapprox = point.substitute(tpi, tb);
        mpointapprox = d_data->d_model.computeConcreteModelValue(mpointapprox);
      }
      Assert(mpointapprox.isConst());
      mpointsBound[i].emplace_back(mpointapprox);
    }
    // bounds are flipped for negative pi
    if (mpointsBound[0].back().getConst<Rational>()
        > mpointsBound[1].back().getConst<Rational>())
    {
      std::swap(mpointsBound[0].back(), mpointsBound[1].back());
    }
  }

  unsigned mdir_index = 0;
  int monotonic_dir = -1;
  Node mono_bounds[2];
  Node targ, targval, t, tval;
  for (const auto& sarg : tf_args)
  {
    Node sargval = d_data->d_model.computeAbstractModelValue(sarg);
    Assert(sargval.isConst());
    const Rational& sargvalr = sargval.getConst<Rational>();
    Node s = tf_arg_to_term[sarg];
    Node sval = d_data->d_model.computeAbstractModelValue(s);
    Assert(sval.isConst());

    // increment to the proper monotonicity region
    bool increment = true;
    while (increment && mdir_index < d_mpoints.size())
    {
      increment = false;
      // if we are less than the upper bound of the next point
      Node pvalUpper = mpointsBound[1][mdir_index];
      Assert(pvalUpper.isConst());
      if (sargvalr < pvalUpper.getConst<Rational>())
      {
        increment = true;
        Trace("nl-ext-tf-mono")
            << "...increment at " << sarg << " since model value is less than "
            << mpointsBound[1][mdir_index] << std::endl;
      }
      if (increment)
      {
        tval = Node::null();
        mono_bounds[1] = d_mpoints[mdir_index];
        mdir_index++;
        monotonic_dir = regionToMonotonicityDir(mdir_index);
        if (mdir_index < d_mpoints.size())
        {
          mono_bounds[0] = d_mpoints[mdir_index];
        }
        else
        {
          mono_bounds[0] = Node::null();
        }
      }
    }
    // must ensure that we are actually less than or equal to the lower bound of
    // the previous point
    if (mdir_index > 0
        && sargvalr > mpointsBound[0][mdir_index - 1].getConst<Rational>())
    {
      // can't take this value into account for monotonicity
      tval = Node::null();
      d_data->d_tf_region[s] = -1;
      Trace("nl-ext-concavity")
          << "Cannot determine the region of transcendental function " << s
          << ", perhaps its value is close to the boundary "
          << mpointsBound[1][mdir_index - 1];
    }
    else
    {
      // store the concavity region
      d_data->d_tf_region[s] = mdir_index;
      Trace("nl-ext-concavity")
          << "Transcendental function " << s << " is in region #" << mdir_index;
    }
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
  Assert(region != -1);

  Trace("nl-ext-sine") << c << " in region " << region << std::endl;
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
                       {nm->mkConstInt(Rational(2 * d)),
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
                       {nm->mkConstInt(Rational(2 * d)),
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
                       {nm->mkConstInt(Rational(2 * d)),
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
                       {nm->mkConstInt(Rational(2 * d)),
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
  Assert(region != -1);
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

bool SineSolver::hasExactModelValue(TNode n) const
{
  Assert(n.getKind() == SINE);
  Node mv = d_data->d_model.computeAbstractModelValue(n[0]);
  return d_mpointsSine.find(mv) != d_mpointsSine.end();
}

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
