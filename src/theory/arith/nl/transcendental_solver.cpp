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

#include "theory/arith/nl/transcendental_solver.h"

#include <cmath>
#include <set>

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "options/arith_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/nl/transcendental/utils.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

TranscendentalSolver::TranscendentalSolver(InferenceManager& im, NlModel& m)
    : d_im(im),
      d_model(m),
      d_tstate(d_im, d_model),
      d_expSlv(&d_tstate),
      d_sineSlv(&d_tstate)
{
  d_taylor_degree = options::nlExtTfTaylorDegree();
}

TranscendentalSolver::~TranscendentalSolver() {}

void TranscendentalSolver::initLastCall(const std::vector<Node>& assertions,
                                        const std::vector<Node>& false_asserts,
                                        const std::vector<Node>& xts)
{
  d_tstate.init(assertions, false_asserts, xts);

  NodeManager* nm = NodeManager::currentNM();

  // for computing congruence
  std::map<Kind, ArgTrie> argTrie;
  for (unsigned i = 0, xsize = xts.size(); i < xsize; i++)
  {
    Node a = xts[i];
    Kind ak = a.getKind();
    bool consider = true;
    // if is an unpurified application of SINE, or it is a transcendental
    // applied to a trancendental, purify.
    if (isTranscendentalKind(ak))
    {
      // if we've already computed master for a
      if (d_tstate.d_trMaster.find(a) != d_tstate.d_trMaster.end())
      {
        // a master has at least one slave
        consider = (d_tstate.d_trSlaves.find(a) != d_tstate.d_trSlaves.end());
      }
      else
      {
        if (ak == SINE)
        {
          // always not a master
          consider = false;
        }
        else
        {
          for (const Node& ac : a)
          {
            if (isTranscendentalKind(ac.getKind()))
            {
              consider = false;
              break;
            }
          }
        }
      }
    }
    if (ak == EXPONENTIAL || ak == SINE)
    {
      // if we didn't indicate that it should be purified above
      if (consider)
      {
        std::vector<Node> repList;
        for (const Node& ac : a)
        {
          Node r = d_model.computeConcreteModelValue(ac);
          repList.push_back(r);
        }
        Node aa = argTrie[ak].add(a, repList);
        if (aa != a)
        {
          // apply congruence to pairs of terms that are disequal and congruent
          Assert(aa.getNumChildren() == a.getNumChildren());
          Node mvaa = d_model.computeAbstractModelValue(a);
          Node mvaaa = d_model.computeAbstractModelValue(aa);
          if (mvaa != mvaaa)
          {
            std::vector<Node> exp;
            for (unsigned j = 0, size = a.getNumChildren(); j < size; j++)
            {
              exp.push_back(a[j].eqNode(aa[j]));
            }
            Node expn = exp.size() == 1 ? exp[0] : nm->mkNode(AND, exp);
            Node cong_lemma = nm->mkNode(OR, expn.negate(), a.eqNode(aa));
            d_im.addPendingArithLemma(cong_lemma, InferenceId::NL_CONGRUENCE);
          }
        }
      }
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
    Kind k = tfs.first;
    for (const Node& tf : tfs.second)
    {
      Trace("nl-ext-cm") << "- Term: " << tf << std::endl;
      bool success = true;
      // tf is Figure 3 : tf( x )
      Node bl;
      Node bu;
      if (k == PI)
      {
        bl = d_tstate.d_pi_bound[0];
        bu = d_tstate.d_pi_bound[1];
      }
      else
      {
        std::pair<Node, Node> bounds = getTfModelBounds(tf, d_taylor_degree);
        bl = bounds.first;
        bu = bounds.second;
        if (bl != bu)
        {
          d_model.setUsedApproximate();
        }
      }
      if (!bl.isNull() && !bu.isNull())
      {
        // for each function in the congruence classe
        for (const Node& ctf : d_tstate.d_funcCongClass[tf])
        {
          // each term in congruence classes should be master terms
          Assert(d_tstate.d_trSlaves.find(ctf) != d_tstate.d_trSlaves.end());
          // we set the bounds for each slave of tf
          for (const Node& stf : d_tstate.d_trSlaves[ctf])
          {
            Trace("nl-ext-cm") << "...bound for " << stf << " : [" << bl << ", "
                               << bu << "]" << std::endl;
            success = d_model.addCheckModelBound(stf, bl, bu);
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
  assertions = passertions;
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
    d_secant_points[tf][d].push_back(c);
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
  Trace("nl-ext") << "Get tangent plane lemmas for transcendental functions..."
                  << std::endl;
  // this implements Figure 3 of "Satisfiaility Modulo Transcendental Functions
  // via Incremental Linearization" by Cimatti et al
  for (std::pair<const Kind, std::vector<Node> >& tfs : d_tstate.d_funcMap)
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
        unsigned prev = d_im.numPendingLemmas() + d_im.numWaitingLemmas();
        if (k == Kind::EXPONENTIAL)
        {
          if (d_expSlv.checkTfTangentPlanesFun(tf, d))
          {
            Trace("nl-ext-tftp")
                << "...fail, #lemmas = "
                << (d_im.numPendingLemmas() + d_im.numWaitingLemmas() - prev)
                << std::endl;
            break;
          }
          else
          {
            Trace("nl-ext-tftp") << "...success" << std::endl;
          }
        }
        else
        {
          if (checkTfTangentPlanesFun(tf, d))
          {
            Trace("nl-ext-tftp")
                << "...fail, #lemmas = "
                << (d_im.numPendingLemmas() + d_im.numWaitingLemmas() - prev)
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
}

bool TranscendentalSolver::checkTfTangentPlanesFun(Node tf, unsigned d)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = tf.getKind();
  if (k == Kind::EXPONENTIAL)
  {
    //return d_expSlv.checkTfTangentPlanesFun(tf, d);
  }
  // this should only be run on master applications
  Assert(d_tstate.d_trSlaves.find(tf) != d_tstate.d_trSlaves.end());

  // Figure 3 : c
  Node c = d_model.computeAbstractModelValue(tf[0]);
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
  d_tstate.d_taylor.getPolynomialApproximationBoundForArg(k, c, d, pbounds);
  poly_approx_bounds[0][1] = pbounds[0];
  poly_approx_bounds[0][-1] = pbounds[1];
  poly_approx_bounds[1][1] = pbounds[2];
  poly_approx_bounds[1][-1] = pbounds[3];

  // Figure 3 : v
  Node v = d_model.computeAbstractModelValue(tf);

  // check value of tf
  Trace("nl-ext-tftp-debug") << "Process tangent plane refinement for " << tf
                             << ", degree " << d << "..." << std::endl;
  Trace("nl-ext-tftp-debug") << "  value in model : " << v << std::endl;
  Trace("nl-ext-tftp-debug") << "  arg value in model : " << c << std::endl;

  std::vector<Node> taylor_vars;
  taylor_vars.push_back(d_tstate.d_taylor.getTaylorVariable());

  // compute the concavity
  int region = -1;
  std::unordered_map<Node, int, NodeHashFunction>::iterator itr =
      d_tstate.d_tf_region.find(tf);
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
  // bounds for which we are this concavity
  // Figure 3: < l, u >
  Node bounds[2];
  if (k == SINE)
  {
    bounds[0] = regionToLowerBound(k, region);
    Assert(!bounds[0].isNull());
    bounds[1] = regionToUpperBound(k, region);
    Assert(!bounds[1].isNull());
  }

  // Figure 3: P
  Node poly_approx;

  // compute whether this is a tangent refinement or a secant refinement
  bool is_tangent = false;
  bool is_secant = false;
  std::pair<Node, Node> mvb = getTfModelBounds(tf, d);
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
      Node comp = nm->mkNode(r == 0 ? LT : GT, v, v_pab);
      Trace("nl-ext-tftp-debug2") << "...compare : " << comp << std::endl;
      Node compr = Rewriter::rewrite(comp);
      Trace("nl-ext-tftp-debug2") << "...got : " << compr << std::endl;
      if (compr == d_tstate.d_true)
      {
        poly_approx_c = v_pab;
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
    if (k == Kind::EXPONENTIAL) {
      d_expSlv.mkTangentLemma(tf, c, poly_approx_c);
    } else {
      d_sineSlv.mkTangentLemma(tf, c, poly_approx_c, region);
    }
  }
  else if (is_secant)
  {
    // bounds are the minimum and maximum previous secant points
    // should not repeat secant points: secant lemmas should suffice to
    // rule out previous assignment
    Assert(std::find(
               d_secant_points[tf][d].begin(), d_secant_points[tf][d].end(), c)
           == d_secant_points[tf][d].end());
    // Insert into the (temporary) vector. We do not update this vector
    // until we are sure this secant plane lemma has been processed. We do
    // this by mapping the lemma to a side effect below.
    std::vector<Node> spoints = d_secant_points[tf][d];
    spoints.push_back(c);

    // sort
    SortNlModel smv;
    smv.d_nlm = &d_model;
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
      if (k == SINE)
      {
        Assert(!bounds[0].isNull());
      }
      else if (k == EXPONENTIAL)
      {
        // pick c-1
        bounds[0] = Rewriter::rewrite(nm->mkNode(MINUS, c, d_tstate.d_one));
      }
    }
    if (index < spoints.size() - 1)
    {
      bounds[1] = spoints[index + 1];
    }
    else
    {
      // otherwise, we use the upper boundary point for this concavity
      // region
      if (k == SINE)
      {
        Assert(!bounds[1].isNull());
      }
      else if (k == EXPONENTIAL)
      {
        // pick c+1
        bounds[1] = Rewriter::rewrite(nm->mkNode(PLUS, c, d_tstate.d_one));
      }
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
      Node b = d_model.computeAbstractModelValue(bounds[s]);
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
        Node rcoeff_n = Rewriter::rewrite(nm->mkNode(MINUS, b, c));
        Assert(rcoeff_n.isConst());
        Rational rcoeff = rcoeff_n.getConst<Rational>();
        Assert(rcoeff.sgn() != 0);
        poly_approx_b = Rewriter::rewrite(poly_approx_b);
        poly_approx_c = Rewriter::rewrite(poly_approx_c);
        splane = nm->mkNode(
            PLUS,
            poly_approx_b,
            nm->mkNode(MULT,
                       nm->mkNode(MINUS, poly_approx_b, poly_approx_c),
                       nm->mkConst(Rational(1) / rcoeff),
                       nm->mkNode(MINUS, tf[0], b)));

        Node lem = nm->mkNode(concavity == 1 ? LEQ : GEQ, tf, splane);
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
            nm->mkNode(AND,
                       nm->mkNode(GEQ, tf[0], s == 0 ? bounds[s] : c),
                       nm->mkNode(LEQ, tf[0], s == 0 ? c : bounds[s]));
        lem = nm->mkNode(IMPLIES, antec_n, lem);
        Trace("nl-ext-tftp-debug2")
            << "*** Secant plane lemma (pre-rewrite) : " << lem << std::endl;
        lem = Rewriter::rewrite(lem);
        Trace("nl-ext-tftp-lemma")
            << "*** Secant plane lemma : " << lem << std::endl;
        lemmaConj.push_back(lem);
        Assert(d_model.computeAbstractModelValue(lem) == d_tstate.d_false);
      }
    }
    // Figure 3 : line 22
    Assert(!lemmaConj.empty());
    Node lem =
        lemmaConj.size() == 1 ? lemmaConj[0] : nm->mkNode(AND, lemmaConj);
    NlLemma nlem(lem, LemmaProperty::NONE, nullptr, InferenceId::NL_T_SECANT);
    // The side effect says that if lem is added, then we should add the
    // secant point c for (tf,d).
    nlem.d_secantPoint.push_back(std::make_tuple(tf, d, c));
    d_im.addPendingArithLemma(nlem, true);
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

Node TranscendentalSolver::regionToLowerBound(Kind k, int region)
{
  Assert(k == Kind::SINE);
  if (region == 1)
  {
    return d_tstate.d_pi_2;
  }
  else if (region == 2)
  {
    return d_tstate.d_zero;
  }
  else if (region == 3)
  {
    return d_tstate.d_pi_neg_2;
  }
  else if (region == 4)
  {
    return d_tstate.d_pi_neg;
  }
  return Node::null();
}

Node TranscendentalSolver::regionToUpperBound(Kind k, int region)
{
  Assert(k == Kind::SINE);
  if (region == 1)
  {
    return d_tstate.d_pi;
  }
  else if (region == 2)
  {
    return d_tstate.d_pi_2;
  }
  else if (region == 3)
  {
    return d_tstate.d_zero;
  }
  else if (region == 4)
  {
    return d_tstate.d_pi_neg_2;
  }
  return Node::null();
}

std::pair<Node, Node> TranscendentalSolver::getTfModelBounds(Node tf,
                                                             unsigned d)
{
  // compute the model value of the argument
  Node c = d_model.computeAbstractModelValue(tf[0]);
  Assert(c.isConst());
  int csign = c.getConst<Rational>().sgn();
  Kind k = tf.getKind();
  if (csign == 0)
  {
    // at zero, its trivial
    if (k == SINE)
    {
      return std::pair<Node, Node>(d_tstate.d_zero, d_tstate.d_zero);
    }
    Assert(k == EXPONENTIAL);
    return std::pair<Node, Node>(d_tstate.d_one, d_tstate.d_one);
  }
  bool isNeg = csign == -1;

  std::vector<Node> pbounds;
  d_tstate.d_taylor.getPolynomialApproximationBoundForArg(k, c, d, pbounds);

  std::vector<Node> bounds;
  TNode tfv = d_tstate.d_taylor.getTaylorVariable();
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
      Node mtfs = d_model.computeAbstractModelValue(tfs);
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

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
