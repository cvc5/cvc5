/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
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

#include "theory/arith/nl/transcendental/transcendental_solver.h"

#include <cmath>
#include <set>

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "options/arith_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_subs.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/arith/nl/transcendental/taylor_generator.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

TranscendentalSolver::TranscendentalSolver(Env& env,
                                           TheoryState& state,
                                           InferenceManager& im,
                                           NlModel& m)
    : EnvObj(env),
      d_astate(state),
      d_tstate(env, im, m),
      d_expSlv(env, &d_tstate),
      d_sineSlv(env, &d_tstate)
{
  d_taylor_degree = options().arith.nlExtTfTaylorDegree;
}

TranscendentalSolver::~TranscendentalSolver() {}

void TranscendentalSolver::initLastCall(const std::vector<Node>& xts)
{
  std::vector<Node> needsMaster;
  d_tstate.init(xts, needsMaster);

  if (d_tstate.d_im.hasUsed())
  {
    return;
  }

  // apply reduction reasoning, e.g. x = pi/2 => sin(x) = 1
  d_sineSlv.doReductions();

  if (d_tstate.d_im.hasUsed()) {
    return;
  }

  for (const Node& a : needsMaster)
  {
    Kind k = a.getKind();
    Assert(k == Kind::SINE || k == Kind::EXPONENTIAL);
    Node new_a = d_tstate.getPurifiedForm(a);
    // Check if the transcental function application is equal to its purified
    // form, if so, we already processed the lemma. In rare cases, note that
    // we may require sending a lemma here even if the purified form above had
    // already been allocated, e.g. in the case that the purification lemma
    // below was dropped.
    if (d_astate.areEqual(a, new_a))
    {
      // already processed
      continue;
    }
    switch (k)
    {
      case Kind::SINE: d_sineSlv.doPhaseShift(a, new_a); break;
      case Kind::EXPONENTIAL: d_expSlv.doPurification(a, new_a); break;
      default: AlwaysAssert(false) << "Unexpected Kind " << k;
    }
  }
}

bool TranscendentalSolver::preprocessAssertionsCheckModel(
    std::vector<Node>& assertions)
{
  ArithSubs subs;
  for (const auto& sub : d_tstate.d_trPurify)
  {
    subs.addArith(sub.first, sub.second);
  }

  // initialize representation of assertions
  std::vector<Node> passertions;
  for (const Node& a : assertions)

  {
    Node pa = a;
    if (!subs.empty())
    {
      pa = subs.applyArith(pa);
      pa = rewrite(pa);
    }
    if (!pa.isConst() || !pa.getConst<bool>())
    {
      Trace("nl-ext-cm-assert") << "- assert : " << pa << std::endl;
      passertions.push_back(pa);
    }
  }
  // get model bounds for all transcendental functions
  Trace("nl-ext-cm") << "----- Get bounds for transcendental functions..."
                     << std::endl;
  for (std::pair<const Kind, std::vector<Node> >& tfs : d_tstate.d_funcMap)
  {
    for (const Node& tf : tfs.second)
    {
      Trace("nl-ext-cm") << "- Term: " << tf << std::endl;
      bool success = true;
      // tf is Figure 3 : tf( x )
      std::pair<Node, Node> bounds;
      if (tfs.first == Kind::PI)
      {
        bounds = {d_tstate.d_pi_bound[0], d_tstate.d_pi_bound[1]};
      }
      else
      {
        bounds = d_tstate.d_taylor.getTfModelBounds(
            tf, d_taylor_degree, d_tstate.d_model);
        if (bounds.first != bounds.second)
        {
          d_tstate.d_model.setUsedApproximate();
        }
      }
      if (!bounds.first.isNull() && !bounds.second.isNull())
      {
        success = d_tstate.addModelBoundForPurifyTerm(
            tf, bounds.first, bounds.second);
      }
      else
      {
        Trace("nl-ext-cm") << "...no bound for " << tf << std::endl;
      }
      if (!success)
      {
        // a bound was conflicting
        Trace("nl-ext-cm") << "...failed to set bound for " << tf << std::endl;
        Trace("nl-ext-cm") << "-----" << std::endl;
        return false;
      }
    }
  }
  // replace the assertions
  assertions = std::move(passertions);
  return true;
}

void TranscendentalSolver::incrementTaylorDegree() { d_taylor_degree++; }
unsigned TranscendentalSolver::getTaylorDegree() const
{
  return d_taylor_degree;
}

void TranscendentalSolver::processSideEffect(const NlLemma& se)
{
  for (const std::tuple<Node, unsigned, Node>& sp : se.d_secantPoint)
  {
    Node tf = std::get<0>(sp);
    unsigned d = std::get<1>(sp);
    Node c = std::get<2>(sp);
    // we have a CDList within the maps, creating it requires some care
    auto& secant_points = d_tstate.d_secant_points[tf];
    auto it = secant_points.find(d);
    if (it == secant_points.end())
    {
      it = secant_points.emplace(d, userContext()).first;
    }
    it->second.push_back(c);
  }
}

void TranscendentalSolver::checkTranscendentalInitialRefine()
{
  d_expSlv.checkInitialRefine();
  d_sineSlv.checkInitialRefine();
}

void TranscendentalSolver::checkTranscendentalMonotonic()
{
  d_expSlv.checkMonotonic();
  d_sineSlv.checkMonotonic();
}

void TranscendentalSolver::checkTranscendentalTangentPlanes()
{
  if (TraceIsOn("nl-ext"))
  {
    if (!d_tstate.d_funcMap.empty())
    {
      Trace("nl-ext")
          << "Get tangent plane lemmas for transcendental functions..."
          << std::endl;
    }
  }
  // this implements Figure 3 of "Satisfiaility Modulo Transcendental Functions
  // via Incremental Linearization" by Cimatti et al
  for (const std::pair<const Kind, std::vector<Node> >& tfs :
       d_tstate.d_funcMap)
  {
    Kind k = tfs.first;
    if (k == PI)
    {
      // We do not use Taylor approximation for PI currently.
      // This is because the convergence is extremely slow, and hence an
      // initial approximation is superior.
      continue;
    }

    // we substitute into the Taylor sum P_{n,f(0)}( x )

    for (const Node& tf : tfs.second)
    {
      // tf is Figure 3 : tf( x )
      Trace("nl-ext-tftp") << "Compute tangent planes " << tf << std::endl;
      // go until max degree is reached, or we don't meet bound criteria
      for (unsigned d = 1; d <= d_taylor_degree; d++)
      {
        Trace("nl-ext-tftp") << "- run at degree " << d << "..." << std::endl;
        unsigned prev =
            d_tstate.d_im.numPendingLemmas() + d_tstate.d_im.numWaitingLemmas();
        if (checkTfTangentPlanesFun(tf, d))
        {
          Trace("nl-ext-tftp") << "...fail, #lemmas = "
                               << (d_tstate.d_im.numPendingLemmas()
                                   + d_tstate.d_im.numWaitingLemmas() - prev)
                               << std::endl;
          break;
        }
        else
        {
          Trace("nl-ext-tftp") << "...success" << std::endl;
        }
      }
    }
  }
}

bool TranscendentalSolver::checkTfTangentPlanesFun(Node tf, unsigned d)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = tf.getKind();
  // this should only be run on purified applications
  Assert(d_tstate.isPurified(tf));

  // Figure 3 : c
  Node c = d_tstate.d_model.computeAbstractModelValue(tf[0]);
  Assert(c.isConst());
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
  TaylorGenerator::ApproximationBounds pbounds;
  std::uint64_t actual_d =
      d_tstate.d_taylor.getPolynomialApproximationBoundForArg(k, c, d, pbounds);
  poly_approx_bounds[0][1] = pbounds.d_lower;
  poly_approx_bounds[0][-1] = pbounds.d_lower;
  poly_approx_bounds[1][1] = pbounds.d_upperPos;
  poly_approx_bounds[1][-1] = pbounds.d_upperNeg;

  // Figure 3 : v
  Node v = d_tstate.d_model.computeAbstractModelValue(tf);

  // check value of tf
  Trace("nl-ext-tftp-debug") << "Process tangent plane refinement for " << tf
                             << ", degree " << d << "..." << std::endl;
  Trace("nl-ext-tftp-debug") << "  value in model : " << v << std::endl;
  Trace("nl-ext-tftp-debug") << "  arg value in model : " << c << std::endl;

  // compute the concavity
  int region = -1;
  std::unordered_map<Node, int>::iterator itr = d_tstate.d_tf_region.find(tf);
  if (itr != d_tstate.d_tf_region.end())
  {
    region = itr->second;
    Trace("nl-ext-tftp-debug") << "  region is : " << region << std::endl;
  }
  if (region == -1)
  {
    // the region cannot be assigned, return false without lemma
    return false;
  }
  // Figure 3 : conc
  int concavity = regionToConcavity(k, itr->second);
  Trace("nl-ext-tftp-debug") << "  concavity is : " << concavity << std::endl;
  if (concavity == 0)
  {
    // no secant/tangent plane is necessary
    return true;
  }

  // Figure 3: P
  Node poly_approx;

  // compute whether this is a tangent refinement or a secant refinement
  bool is_tangent = false;
  bool is_secant = false;
  std::pair<Node, Node> mvb =
      d_tstate.d_taylor.getTfModelBounds(tf, d, d_tstate.d_model);
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
      Trace("nl-trans") << "...model value of " << pab << " is " << v_pab
                        << std::endl;

      Assert(v_pab.isConst());
      Node comp = nm->mkNode(r == 0 ? LT : GT, v, v_pab);
      Trace("nl-trans") << "...compare : " << comp << std::endl;
      Node compr = rewrite(comp);
      Trace("nl-trans") << "...got : " << compr << std::endl;
      if (compr == d_tstate.d_true)
      {
        poly_approx_c = rewrite(v_pab);
        // beyond the bounds
        if (r == 0)
        {
          poly_approx = poly_approx_bounds[r][csign];
          is_tangent = concavity == 1;
          is_secant = concavity == -1;
        }
        else
        {
          poly_approx = poly_approx_bounds[r][csign];
          is_tangent = concavity == -1;
          is_secant = concavity == 1;
        }
        if (TraceIsOn("nl-ext-tftp"))
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
    Trace("nl-trans") << "...poly approximation at c is " << poly_approx_c
                      << std::endl;
  }
  else
  {
    // we may want to continue getting better bounds
    return false;
  }

  if (is_tangent)
  {
    if (k == Kind::EXPONENTIAL)
    {
      d_expSlv.doTangentLemma(tf, c, poly_approx_c, d);
    }
    else if (k == Kind::SINE)
    {
      d_sineSlv.doTangentLemma(tf, c, poly_approx_c, region, d);
    }
  }
  else if (is_secant)
  {
    if (k == EXPONENTIAL)
    {
      d_expSlv.doSecantLemmas(tf, poly_approx, c, poly_approx_c, d, actual_d);
    }
    else if (k == Kind::SINE)
    {
      d_sineSlv.doSecantLemmas(
          tf, poly_approx, c, poly_approx_c, d, actual_d, region);
    }
  }
  return true;
}

int TranscendentalSolver::regionToConcavity(Kind k, int region)
{
  if (k == EXPONENTIAL)
  {
    if (region == 1)
    {
      return 1;
    }
  }
  else if (k == SINE)
  {
    if (region == 1 || region == 2)
    {
      return -1;
    }
    else if (region == 3 || region == 4)
    {
      return 1;
    }
  }
  return 0;
}

void TranscendentalSolver::postProcessModel(std::map<Node, Node>& arithModel,
                                            const std::set<Node>& termSet)
{
  Trace("nl-ext") << "TranscendentalSolver::postProcessModel" << std::endl;
  // map from equivalence classes to a transcendental function application,
  // if it exists.
  std::unordered_map<Node, Node> trReps;
  for (const Node& n : termSet)
  {
    Kind k = n.getKind();
    if (!isTranscendentalKind(n.getKind()))
    {
      continue;
    }
    // it might have an exact value, in which case there is nothing to do
    if (k == SINE && d_sineSlv.hasExactModelValue(n))
    {
      continue;
    }
    Node r = d_astate.getRepresentative(n);
    trReps[r] = n;
  }
  if (trReps.empty())
  {
    Trace("nl-ext") << "...no transcendental functions" << std::endl;
    return;
  }
  std::unordered_map<Node, Node>::iterator it;
  for (auto& am : arithModel)
  {
    // skip integer variables
    if (am.first.getType().isInteger())
    {
      Trace("nl-ext") << "...keep model value for integer " << am.first
                      << std::endl;
      continue;
    }
    // cannot erase values for purification arguments
    if (d_tstate.d_trPurifyVars.find(am.first) != d_tstate.d_trPurifyVars.end())
    {
      Trace("nl-ext") << "...keep model value for purification variable "
                      << am.first << std::endl;
      continue;
    }
    Node r = d_astate.getRepresentative(am.first);
    it = trReps.find(r);
    // if it is in the same equivalence class as a trancendental function
    // application, we replace its value in the model with that application
    if (it != trReps.end())
    {
      Trace("nl-ext") << "...abstract value for " << am.first << " to "
                      << it->second << std::endl;
      am.second = it->second;
    }
    else
    {
      Trace("nl-ext") << "...keep model value for " << am.first << std::endl;
    }
  }
}

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
