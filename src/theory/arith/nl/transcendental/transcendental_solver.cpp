/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Tim King
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

#include "theory/arith/nl/transcendental/transcendental_solver.h"

#include <cmath>
#include <set>

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "expr/skolem_manager.h"
#include "options/arith_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/arith/nl/transcendental/taylor_generator.h"
#include "theory/rewriter.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

TranscendentalSolver::TranscendentalSolver(InferenceManager& im,
                                           NlModel& m,
                                           ProofNodeManager* pnm,
                                           context::UserContext* c)
    : d_tstate(im, m, pnm, c), d_expSlv(&d_tstate), d_sineSlv(&d_tstate)
{
  d_taylor_degree = options::nlExtTfTaylorDegree();
}

TranscendentalSolver::~TranscendentalSolver() {}

void TranscendentalSolver::initLastCall(const std::vector<Node>& xts)
{
  std::vector<Node> needsMaster;
  d_tstate.init(xts, needsMaster);

  if (d_tstate.d_im.hasUsed()) {
    return;
  }

  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  for (const Node& a : needsMaster)
  {
    // should not have processed this already
    Assert(d_tstate.d_trMaster.find(a) == d_tstate.d_trMaster.end());
    Kind k = a.getKind();
    Assert(k == Kind::SINE || k == Kind::EXPONENTIAL);
    Node y = sm->mkDummySkolem(
        "y", nm->realType(), "phase shifted trigonometric arg");
    Node new_a = nm->mkNode(k, y);
    d_tstate.d_trSlaves[new_a].insert(new_a);
    d_tstate.d_trSlaves[new_a].insert(a);
    d_tstate.d_trMaster[a] = new_a;
    d_tstate.d_trMaster[new_a] = new_a;
    switch (k)
    {
      case Kind::SINE: d_sineSlv.doPhaseShift(a, new_a, y); break;
      case Kind::EXPONENTIAL: d_expSlv.doPurification(a, new_a, y); break;
      default: AlwaysAssert(false) << "Unexpected Kind " << k;
    }
  }
}

bool TranscendentalSolver::preprocessAssertionsCheckModel(
    std::vector<Node>& assertions)
{
  std::vector<Node> pvars;
  std::vector<Node> psubs;
  for (const std::pair<const Node, Node>& tb : d_tstate.d_trMaster)
  {
    pvars.push_back(tb.first);
    psubs.push_back(tb.second);
  }

  // initialize representation of assertions
  std::vector<Node> passertions;
  for (const Node& a : assertions)

  {
    Node pa = a;
    if (!pvars.empty())
    {
      pa = arithSubstitute(pa, pvars, psubs);
      pa = Rewriter::rewrite(pa);
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
        // for each function in the congruence classe
        for (const Node& ctf : d_tstate.d_funcCongClass[tf])
        {
          // each term in congruence classes should be master terms
          Assert(d_tstate.d_trSlaves.find(ctf) != d_tstate.d_trSlaves.end());
          // we set the bounds for each slave of tf
          for (const Node& stf : d_tstate.d_trSlaves[ctf])
          {
            Trace("nl-ext-cm")
                << "...bound for " << stf << " : [" << bounds.first << ", "
                << bounds.second << "]" << std::endl;
            success = d_tstate.d_model.addCheckModelBound(
                stf, bounds.first, bounds.second);
          }
        }
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
    d_tstate.d_secant_points[tf][d].push_back(c);
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
  if (Trace.isOn("nl-ext"))
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
  // this should only be run on master applications
  Assert(d_tstate.d_trSlaves.find(tf) != d_tstate.d_trSlaves.end());

  // Figure 3 : c
  Node c = d_tstate.d_model.computeAbstractModelValue(tf[0]);
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
      Node compr = Rewriter::rewrite(comp);
      Trace("nl-trans") << "...got : " << compr << std::endl;
      if (compr == d_tstate.d_true)
      {
        poly_approx_c = Rewriter::rewrite(v_pab);
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

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
