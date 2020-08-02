/*********************                                                        */
/*! \file transcendental_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

TranscendentalSolver::TranscendentalSolver(NlModel& m) : d_model(m)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
  d_neg_one = nm->mkConst(Rational(-1));
  d_taylor_real_fv = nm->mkBoundVar("x", nm->realType());
  d_taylor_real_fv_base = nm->mkBoundVar("a", nm->realType());
  d_taylor_real_fv_base_rem = nm->mkBoundVar("b", nm->realType());
  d_taylor_degree = options::nlExtTfTaylorDegree();
}

TranscendentalSolver::~TranscendentalSolver() {}

void TranscendentalSolver::initLastCall(const std::vector<Node>& assertions,
                                        const std::vector<Node>& false_asserts,
                                        const std::vector<Node>& xts,
                                        std::vector<NlLemma>& lems)
{
  d_funcCongClass.clear();
  d_funcMap.clear();
  d_tf_region.clear();

  NodeManager* nm = NodeManager::currentNM();

  // register the extended function terms
  std::vector<Node> trNeedsMaster;
  bool needPi = false;
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
      if (d_trMaster.find(a) != d_trMaster.end())
      {
        // a master has at least one slave
        consider = (d_trSlaves.find(a) != d_trSlaves.end());
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
        if (!consider)
        {
          // wait to assign a master below
          trNeedsMaster.push_back(a);
        }
        else
        {
          d_trMaster[a] = a;
          d_trSlaves[a].insert(a);
        }
      }
    }
    if (ak == EXPONENTIAL || ak == SINE)
    {
      needPi = needPi || (ak == SINE);
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
            lems.emplace_back(cong_lemma, Inference::CONGRUENCE);
          }
        }
        else
        {
          // new representative of congruence class
          d_funcMap[ak].push_back(a);
        }
        // add to congruence class
        d_funcCongClass[aa].push_back(a);
      }
    }
    else if (ak == PI)
    {
      Assert(consider);
      needPi = true;
      d_funcMap[ak].push_back(a);
      d_funcCongClass[a].push_back(a);
    }
  }
  // initialize pi if necessary
  if (needPi && d_pi.isNull())
  {
    mkPi();
    getCurrentPiBounds(lems);
  }

  if (!lems.empty())
  {
    return;
  }

  // process SINE phase shifting
  for (const Node& a : trNeedsMaster)
  {
    // should not have processed this already
    Assert(d_trMaster.find(a) == d_trMaster.end());
    Kind k = a.getKind();
    Assert(k == SINE || k == EXPONENTIAL);
    Node y =
        nm->mkSkolem("y", nm->realType(), "phase shifted trigonometric arg");
    Node new_a = nm->mkNode(k, y);
    d_trSlaves[new_a].insert(new_a);
    d_trSlaves[new_a].insert(a);
    d_trMaster[a] = new_a;
    d_trMaster[new_a] = new_a;
    Node lem;
    if (k == SINE)
    {
      Trace("nl-ext-tf") << "Basis sine : " << new_a << " for " << a
                         << std::endl;
      Assert(!d_pi.isNull());
      Node shift = nm->mkSkolem("s", nm->integerType(), "number of shifts");
      // TODO : do not introduce shift here, instead needs model-based
      // refinement for constant shifts (cvc4-projects #1284)
      lem = nm->mkNode(
          AND,
          mkValidPhase(y, d_pi),
          nm->mkNode(
              ITE,
              mkValidPhase(a[0], d_pi),
              a[0].eqNode(y),
              a[0].eqNode(nm->mkNode(
                  PLUS,
                  y,
                  nm->mkNode(MULT, nm->mkConst(Rational(2)), shift, d_pi)))),
          new_a.eqNode(a));
    }
    else
    {
      // do both equalities to ensure that new_a becomes a preregistered term
      lem = nm->mkNode(AND, a.eqNode(new_a), a[0].eqNode(y));
    }
    // note we must do preprocess on this lemma
    Trace("nl-ext-lemma") << "NonlinearExtension::Lemma : purify : " << lem
                          << std::endl;
    NlLemma nlem(lem, Inference::T_PURIFY_ARG);
    nlem.d_preprocess = true;
    lems.emplace_back(nlem);
  }

  if (Trace.isOn("nl-ext-mv"))
  {
    Trace("nl-ext-mv") << "Arguments of trancendental functions : "
                       << std::endl;
    for (std::pair<const Kind, std::vector<Node> >& tfl : d_funcMap)
    {
      Kind k = tfl.first;
      if (k == SINE || k == EXPONENTIAL)
      {
        for (const Node& tf : tfl.second)
        {
          Node v = tf[0];
          d_model.computeConcreteModelValue(v);
          d_model.computeAbstractModelValue(v);
          d_model.printModelValue("nl-ext-mv", v);
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
  for (const std::pair<const Node, Node>& tb : d_trMaster)
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
  for (std::pair<const Kind, std::vector<Node> >& tfs : d_funcMap)
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
        bl = d_pi_bound[0];
        bu = d_pi_bound[1];
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
        for (const Node& ctf : d_funcCongClass[tf])
        {
          // each term in congruence classes should be master terms
          Assert(d_trSlaves.find(ctf) != d_trSlaves.end());
          // we set the bounds for each slave of tf
          for (const Node& stf : d_trSlaves[ctf])
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

void TranscendentalSolver::mkPi()
{
  NodeManager* nm = NodeManager::currentNM();
  if (d_pi.isNull())
  {
    d_pi = nm->mkNullaryOperator(nm->realType(), PI);
    d_pi_2 = Rewriter::rewrite(
        nm->mkNode(MULT, d_pi, nm->mkConst(Rational(1) / Rational(2))));
    d_pi_neg_2 = Rewriter::rewrite(
        nm->mkNode(MULT, d_pi, nm->mkConst(Rational(-1) / Rational(2))));
    d_pi_neg =
        Rewriter::rewrite(nm->mkNode(MULT, d_pi, nm->mkConst(Rational(-1))));
    // initialize bounds
    d_pi_bound[0] = nm->mkConst(Rational(103993) / Rational(33102));
    d_pi_bound[1] = nm->mkConst(Rational(104348) / Rational(33215));
  }
}

void TranscendentalSolver::getCurrentPiBounds(std::vector<NlLemma>& lemmas)
{
  NodeManager* nm = NodeManager::currentNM();
  Node pi_lem = nm->mkNode(AND,
                           nm->mkNode(GEQ, d_pi, d_pi_bound[0]),
                           nm->mkNode(LEQ, d_pi, d_pi_bound[1]));
  lemmas.emplace_back(pi_lem, Inference::T_PI_BOUND);
}

std::vector<NlLemma> TranscendentalSolver::checkTranscendentalInitialRefine()
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<NlLemma> lemmas;
  Trace("nl-ext")
      << "Get initial refinement lemmas for transcendental functions..."
      << std::endl;
  for (std::pair<const Kind, std::vector<Node> >& tfl : d_funcMap)
  {
    Kind k = tfl.first;
    for (const Node& t : tfl.second)
    {
      // initial refinements
      if (d_tf_initial_refine.find(t) == d_tf_initial_refine.end())
      {
        d_tf_initial_refine[t] = true;
        Node lem;
        if (k == SINE)
        {
          Node symn = nm->mkNode(SINE, nm->mkNode(MULT, d_neg_one, t[0]));
          symn = Rewriter::rewrite(symn);
          // Can assume it is its own master since phase is split over 0,
          // hence  -pi <= t[0] <= pi implies -pi <= -t[0] <= pi.
          d_trMaster[symn] = symn;
          d_trSlaves[symn].insert(symn);
          Assert(d_trSlaves.find(t) != d_trSlaves.end());
          std::vector<Node> children;

          lem = nm->mkNode(AND,
                           // bounds
                           nm->mkNode(AND,
                                      nm->mkNode(LEQ, t, d_one),
                                      nm->mkNode(GEQ, t, d_neg_one)),
                           // symmetry
                           nm->mkNode(PLUS, t, symn).eqNode(d_zero),
                           // sign
                           nm->mkNode(EQUAL,
                                      nm->mkNode(LT, t[0], d_zero),
                                      nm->mkNode(LT, t, d_zero)),
                           // zero val
                           nm->mkNode(EQUAL,
                                      nm->mkNode(GT, t[0], d_zero),
                                      nm->mkNode(GT, t, d_zero)));
          lem = nm->mkNode(
              AND,
              lem,
              // zero tangent
              nm->mkNode(AND,
                         nm->mkNode(IMPLIES,
                                    nm->mkNode(GT, t[0], d_zero),
                                    nm->mkNode(LT, t, t[0])),
                         nm->mkNode(IMPLIES,
                                    nm->mkNode(LT, t[0], d_zero),
                                    nm->mkNode(GT, t, t[0]))),
              // pi tangent
              nm->mkNode(
                  AND,
                  nm->mkNode(IMPLIES,
                             nm->mkNode(LT, t[0], d_pi),
                             nm->mkNode(LT, t, nm->mkNode(MINUS, d_pi, t[0]))),
                  nm->mkNode(
                      IMPLIES,
                      nm->mkNode(GT, t[0], d_pi_neg),
                      nm->mkNode(GT, t, nm->mkNode(MINUS, d_pi_neg, t[0])))));
        }
        else if (k == EXPONENTIAL)
        {
          // ( exp(x) > 0 ) ^ ( x=0 <=> exp( x ) = 1 ) ^ ( x < 0 <=> exp( x ) <
          // 1 ) ^ ( x <= 0 V exp( x ) > x + 1 )
          lem = nm->mkNode(
              AND,
              nm->mkNode(GT, t, d_zero),
              nm->mkNode(EQUAL, t[0].eqNode(d_zero), t.eqNode(d_one)),
              nm->mkNode(EQUAL,
                         nm->mkNode(LT, t[0], d_zero),
                         nm->mkNode(LT, t, d_one)),
              nm->mkNode(OR,
                         nm->mkNode(LEQ, t[0], d_zero),
                         nm->mkNode(GT, t, nm->mkNode(PLUS, t[0], d_one))));
        }
        if (!lem.isNull())
        {
          lemmas.emplace_back(lem, Inference::T_INIT_REFINE);
        }
      }
    }
  }

  return lemmas;
}

std::vector<NlLemma> TranscendentalSolver::checkTranscendentalMonotonic()
{
  std::vector<NlLemma> lemmas;
  Trace("nl-ext") << "Get monotonicity lemmas for transcendental functions..."
                  << std::endl;

  // sort arguments of all transcendentals
  std::map<Kind, std::vector<Node> > sorted_tf_args;
  std::map<Kind, std::map<Node, Node> > tf_arg_to_term;

  for (std::pair<const Kind, std::vector<Node> >& tfl : d_funcMap)
  {
    Kind k = tfl.first;
    if (k == EXPONENTIAL || k == SINE)
    {
      for (const Node& tf : tfl.second)
      {
        Node a = tf[0];
        Node mvaa = d_model.computeAbstractModelValue(a);
        if (mvaa.isConst())
        {
          Trace("nl-ext-tf-mono-debug") << "...tf term : " << a << std::endl;
          sorted_tf_args[k].push_back(a);
          tf_arg_to_term[k][a] = tf;
        }
      }
    }
  }

  SortNlModel smv;
  smv.d_nlm = &d_model;
  // sort by concrete values
  smv.d_isConcrete = true;
  smv.d_reverse_order = true;
  for (std::pair<const Kind, std::vector<Node> >& tfl : d_funcMap)
  {
    Kind k = tfl.first;
    if (!sorted_tf_args[k].empty())
    {
      std::sort(sorted_tf_args[k].begin(), sorted_tf_args[k].end(), smv);
      Trace("nl-ext-tf-mono") << "Sorted transcendental function list for " << k
                              << " : " << std::endl;
      for (unsigned i = 0; i < sorted_tf_args[k].size(); i++)
      {
        Node targ = sorted_tf_args[k][i];
        Node mvatarg = d_model.computeAbstractModelValue(targ);
        Trace("nl-ext-tf-mono")
            << "  " << targ << " -> " << mvatarg << std::endl;
        Node t = tf_arg_to_term[k][targ];
        Node mvat = d_model.computeAbstractModelValue(t);
        Trace("nl-ext-tf-mono") << "     f-val : " << mvat << std::endl;
      }
      std::vector<Node> mpoints;
      std::vector<Node> mpoints_vals;
      if (k == SINE)
      {
        mpoints.push_back(d_pi);
        mpoints.push_back(d_pi_2);
        mpoints.push_back(d_zero);
        mpoints.push_back(d_pi_neg_2);
        mpoints.push_back(d_pi_neg);
      }
      else if (k == EXPONENTIAL)
      {
        mpoints.push_back(Node::null());
      }
      if (!mpoints.empty())
      {
        // get model values for points
        for (unsigned i = 0; i < mpoints.size(); i++)
        {
          Node mpv;
          if (!mpoints[i].isNull())
          {
            mpv = d_model.computeAbstractModelValue(mpoints[i]);
            Assert(mpv.isConst());
          }
          mpoints_vals.push_back(mpv);
        }

        unsigned mdir_index = 0;
        int monotonic_dir = -1;
        Node mono_bounds[2];
        Node targ, targval, t, tval;
        for (unsigned i = 0, size = sorted_tf_args[k].size(); i < size; i++)
        {
          Node sarg = sorted_tf_args[k][i];
          Node sargval = d_model.computeAbstractModelValue(sarg);
          Assert(sargval.isConst());
          Node s = tf_arg_to_term[k][sarg];
          Node sval = d_model.computeAbstractModelValue(s);
          Assert(sval.isConst());

          // increment to the proper monotonicity region
          bool increment = true;
          while (increment && mdir_index < mpoints.size())
          {
            increment = false;
            if (mpoints[mdir_index].isNull())
            {
              increment = true;
            }
            else
            {
              Node pval = mpoints_vals[mdir_index];
              Assert(pval.isConst());
              if (sargval.getConst<Rational>() < pval.getConst<Rational>())
              {
                increment = true;
                Trace("nl-ext-tf-mono") << "...increment at " << sarg
                                        << " since model value is less than "
                                        << mpoints[mdir_index] << std::endl;
              }
            }
            if (increment)
            {
              tval = Node::null();
              mono_bounds[1] = mpoints[mdir_index];
              mdir_index++;
              monotonic_dir = regionToMonotonicityDir(k, mdir_index);
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
          d_tf_region[s] = mdir_index;
          Trace("nl-ext-concavity") << "Transcendental function " << s
                                    << " is in region #" << mdir_index;
          Trace("nl-ext-concavity")
              << ", arg model value = " << sargval << std::endl;

          if (!tval.isNull())
          {
            NodeManager* nm = NodeManager::currentNM();
            Node mono_lem;
            if (monotonic_dir == 1
                && sval.getConst<Rational>() > tval.getConst<Rational>())
            {
              mono_lem = nm->mkNode(
                  IMPLIES, nm->mkNode(GEQ, targ, sarg), nm->mkNode(GEQ, t, s));
            }
            else if (monotonic_dir == -1
                     && sval.getConst<Rational>() < tval.getConst<Rational>())
            {
              mono_lem = nm->mkNode(
                  IMPLIES, nm->mkNode(LEQ, targ, sarg), nm->mkNode(LEQ, t, s));
            }
            if (!mono_lem.isNull())
            {
              if (!mono_bounds[0].isNull())
              {
                Assert(!mono_bounds[1].isNull());
                mono_lem = nm->mkNode(
                    IMPLIES,
                    nm->mkNode(AND,
                               mkBounded(mono_bounds[0], targ, mono_bounds[1]),
                               mkBounded(mono_bounds[0], sarg, mono_bounds[1])),
                    mono_lem);
              }
              Trace("nl-ext-tf-mono")
                  << "Monotonicity lemma : " << mono_lem << std::endl;
              lemmas.emplace_back(mono_lem, Inference::T_MONOTONICITY);
            }
          }
          // store the previous values
          targ = sarg;
          targval = sargval;
          t = s;
          tval = sval;
        }
      }
    }
  }
  return lemmas;
}

std::vector<NlLemma> TranscendentalSolver::checkTranscendentalTangentPlanes()
{
  std::vector<NlLemma> lemmas;
  Trace("nl-ext") << "Get tangent plane lemmas for transcendental functions..."
                  << std::endl;
  // this implements Figure 3 of "Satisfiaility Modulo Transcendental Functions
  // via Incremental Linearization" by Cimatti et al
  for (std::pair<const Kind, std::vector<Node> >& tfs : d_funcMap)
  {
    Kind k = tfs.first;
    if (k == PI)
    {
      // We do not use Taylor approximation for PI currently.
      // This is because the convergence is extremely slow, and hence an
      // initial approximation is superior.
      continue;
    }
    Trace("nl-ext-tftp-debug2") << "Taylor variables: " << std::endl;
    Trace("nl-ext-tftp-debug2")
        << "          taylor_real_fv : " << d_taylor_real_fv << std::endl;
    Trace("nl-ext-tftp-debug2")
        << "     taylor_real_fv_base : " << d_taylor_real_fv_base << std::endl;
    Trace("nl-ext-tftp-debug2")
        << " taylor_real_fv_base_rem : " << d_taylor_real_fv_base_rem
        << std::endl;
    Trace("nl-ext-tftp-debug2") << std::endl;

    // we substitute into the Taylor sum P_{n,f(0)}( x )

    for (const Node& tf : tfs.second)
    {
      // tf is Figure 3 : tf( x )
      Trace("nl-ext-tftp") << "Compute tangent planes " << tf << std::endl;
      // go until max degree is reached, or we don't meet bound criteria
      for (unsigned d = 1; d <= d_taylor_degree; d++)
      {
        Trace("nl-ext-tftp") << "- run at degree " << d << "..." << std::endl;
        unsigned prev = lemmas.size();
        if (checkTfTangentPlanesFun(tf, d, lemmas))
        {
          Trace("nl-ext-tftp")
              << "...fail, #lemmas = " << (lemmas.size() - prev) << std::endl;
          break;
        }
        else
        {
          Trace("nl-ext-tftp") << "...success" << std::endl;
        }
      }
    }
  }

  return lemmas;
}

bool TranscendentalSolver::checkTfTangentPlanesFun(Node tf,
                                                   unsigned d,
                                                   std::vector<NlLemma>& lemmas)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = tf.getKind();
  // this should only be run on master applications
  Assert(d_trSlaves.find(tf) != d_trSlaves.end());

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
  getPolynomialApproximationBoundForArg(k, c, d, pbounds);
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
  taylor_vars.push_back(d_taylor_real_fv);

  // compute the concavity
  int region = -1;
  std::unordered_map<Node, int, NodeHashFunction>::iterator itr =
      d_tf_region.find(tf);
  if (itr != d_tf_region.end())
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
      if (compr == d_true)
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
    // compute tangent plane
    // Figure 3: T( x )
    // We use zero slope tangent planes, since the concavity of the Taylor
    // approximation cannot be easily established.
    Node tplane = poly_approx_c;

    Node lem = nm->mkNode(concavity == 1 ? GEQ : LEQ, tf, tplane);
    std::vector<Node> antec;
    int mdir = regionToMonotonicityDir(k, region);
    for (unsigned i = 0; i < 2; i++)
    {
      // Tangent plane is valid in the interval [c,u) if the slope of the
      // function matches its concavity, and is valid in (l, c] otherwise.
      Node use_bound = (mdir == concavity) == (i == 0) ? c : bounds[i];
      if (!use_bound.isNull())
      {
        Node ant = nm->mkNode(i == 0 ? GEQ : LEQ, tf[0], use_bound);
        antec.push_back(ant);
      }
    }
    if (!antec.empty())
    {
      Node antec_n = antec.size() == 1 ? antec[0] : nm->mkNode(AND, antec);
      lem = nm->mkNode(IMPLIES, antec_n, lem);
    }
    Trace("nl-ext-tftp-debug2")
        << "*** Tangent plane lemma (pre-rewrite): " << lem << std::endl;
    lem = Rewriter::rewrite(lem);
    Trace("nl-ext-tftp-lemma")
        << "*** Tangent plane lemma : " << lem << std::endl;
    Assert(d_model.computeAbstractModelValue(lem) == d_false);
    // Figure 3 : line 9
    lemmas.emplace_back(lem, Inference::T_TANGENT);
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
        bounds[0] = Rewriter::rewrite(nm->mkNode(MINUS, c, d_one));
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
        bounds[1] = Rewriter::rewrite(nm->mkNode(PLUS, c, d_one));
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
        Assert(d_model.computeAbstractModelValue(lem) == d_false);
      }
    }
    // Figure 3 : line 22
    Assert(!lemmaConj.empty());
    Node lem =
        lemmaConj.size() == 1 ? lemmaConj[0] : nm->mkNode(AND, lemmaConj);
    NlLemma nlem(lem, Inference::T_SECANT);
    // The side effect says that if lem is added, then we should add the
    // secant point c for (tf,d).
    nlem.d_secantPoint.push_back(std::make_tuple(tf, d, c));
    lemmas.emplace_back(nlem);
  }
  return true;
}

int TranscendentalSolver::regionToMonotonicityDir(Kind k, int region)
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
    if (region == 1 || region == 4)
    {
      return -1;
    }
    else if (region == 2 || region == 3)
    {
      return 1;
    }
  }
  return 0;
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
  if (k == SINE)
  {
    if (region == 1)
    {
      return d_pi_2;
    }
    else if (region == 2)
    {
      return d_zero;
    }
    else if (region == 3)
    {
      return d_pi_neg_2;
    }
    else if (region == 4)
    {
      return d_pi_neg;
    }
  }
  return Node::null();
}

Node TranscendentalSolver::regionToUpperBound(Kind k, int region)
{
  if (k == SINE)
  {
    if (region == 1)
    {
      return d_pi;
    }
    else if (region == 2)
    {
      return d_pi_2;
    }
    else if (region == 3)
    {
      return d_zero;
    }
    else if (region == 4)
    {
      return d_pi_neg_2;
    }
  }
  return Node::null();
}

Node TranscendentalSolver::getDerivative(Node n, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  Assert(x.isVar());
  // only handle the cases of the taylor expansion of d
  if (n.getKind() == EXPONENTIAL)
  {
    if (n[0] == x)
    {
      return n;
    }
  }
  else if (n.getKind() == SINE)
  {
    if (n[0] == x)
    {
      Node na = nm->mkNode(MINUS, d_pi_2, n[0]);
      Node ret = nm->mkNode(SINE, na);
      ret = Rewriter::rewrite(ret);
      return ret;
    }
  }
  else if (n.getKind() == PLUS)
  {
    std::vector<Node> dchildren;
    for (unsigned i = 0; i < n.getNumChildren(); i++)
    {
      // PLUS is flattened in rewriter, recursion depth is bounded by 1
      Node dc = getDerivative(n[i], x);
      if (dc.isNull())
      {
        return dc;
      }
      else
      {
        dchildren.push_back(dc);
      }
    }
    return nm->mkNode(PLUS, dchildren);
  }
  else if (n.getKind() == MULT)
  {
    Assert(n[0].isConst());
    Node dc = getDerivative(n[1], x);
    if (!dc.isNull())
    {
      return nm->mkNode(MULT, n[0], dc);
    }
  }
  else if (n.getKind() == NONLINEAR_MULT)
  {
    unsigned xcount = 0;
    std::vector<Node> children;
    unsigned xindex = 0;
    for (unsigned i = 0, size = n.getNumChildren(); i < size; i++)
    {
      if (n[i] == x)
      {
        xcount++;
        xindex = i;
      }
      children.push_back(n[i]);
    }
    if (xcount == 0)
    {
      return d_zero;
    }
    else
    {
      children[xindex] = nm->mkConst(Rational(xcount));
    }
    return nm->mkNode(MULT, children);
  }
  else if (n.isVar())
  {
    return n == x ? d_one : d_zero;
  }
  else if (n.isConst())
  {
    return d_zero;
  }
  Trace("nl-ext-debug") << "No derivative computed for " << n;
  Trace("nl-ext-debug") << " for d/d{" << x << "}" << std::endl;
  return Node::null();
}

std::pair<Node, Node> TranscendentalSolver::getTaylor(Node fa, unsigned n)
{
  NodeManager* nm = NodeManager::currentNM();
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
  std::unordered_map<unsigned, Node>::iterator itt = d_taylor_sum[fac].find(n);
  if (itt == d_taylor_sum[fac].end())
  {
    Node i_exp_base;
    if (fa[0] == d_zero)
    {
      i_exp_base = d_taylor_real_fv;
    }
    else
    {
      i_exp_base = Rewriter::rewrite(
          nm->mkNode(MINUS, d_taylor_real_fv, d_taylor_real_fv_base));
    }
    Node i_derv = fac;
    Node i_fact = d_one;
    Node i_exp = d_one;
    int i_derv_status = 0;
    unsigned counter = 0;
    std::vector<Node> sum;
    do
    {
      counter++;
      if (fa.getKind() == EXPONENTIAL)
      {
        // unchanged
      }
      else if (fa.getKind() == SINE)
      {
        if (i_derv_status % 2 == 1)
        {
          Node arg = nm->mkNode(PLUS, d_pi_2, d_taylor_real_fv_base);
          i_derv = nm->mkNode(SINE, arg);
        }
        else
        {
          i_derv = fa;
        }
        if (i_derv_status >= 2)
        {
          i_derv = nm->mkNode(MINUS, d_zero, i_derv);
        }
        i_derv = Rewriter::rewrite(i_derv);
        i_derv_status = i_derv_status == 3 ? 0 : i_derv_status + 1;
      }
      if (counter == (n + 1))
      {
        TNode x = d_taylor_real_fv_base;
        i_derv = i_derv.substitute(x, d_taylor_real_fv_base_rem);
      }
      Node curr = nm->mkNode(MULT, nm->mkNode(DIVISION, i_derv, i_fact), i_exp);
      if (counter == (n + 1))
      {
        taylor_rem = curr;
      }
      else
      {
        sum.push_back(curr);
        i_fact = Rewriter::rewrite(
            nm->mkNode(MULT, nm->mkConst(Rational(counter)), i_fact));
        i_exp = Rewriter::rewrite(nm->mkNode(MULT, i_exp_base, i_exp));
      }
    } while (counter <= n);
    taylor_sum = sum.size() == 1 ? sum[0] : nm->mkNode(PLUS, sum);

    if (fac[0] != d_taylor_real_fv_base)
    {
      TNode x = d_taylor_real_fv_base;
      taylor_sum = taylor_sum.substitute(x, fac[0]);
    }

    // cache
    d_taylor_sum[fac][n] = taylor_sum;
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

void TranscendentalSolver::getPolynomialApproximationBounds(
    Kind k, unsigned d, std::vector<Node>& pbounds)
{
  if (d_poly_bounds[k][d].empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    Node tft = nm->mkNode(k, d_zero);
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
    Assert(taylor.second.getKind() == MULT);
    Assert(taylor.second.getNumChildren() == 2);
    Assert(taylor.second[0].getKind() == DIVISION);
    Trace("nl-ext-tftp-debug2")
        << "Taylor remainder for " << k << " is " << taylor.second << std::endl;
    // ru is x^{n+1}/(n+1)!
    Node ru = nm->mkNode(DIVISION, taylor.second[1], taylor.second[0][1]);
    ru = Rewriter::rewrite(ru);
    Trace("nl-ext-tftp-debug2")
        << "Taylor remainder factor is (post-rewrite) : " << ru << std::endl;
    if (k == EXPONENTIAL)
    {
      pbounds.push_back(taylor_sum);
      pbounds.push_back(taylor_sum);
      pbounds.push_back(Rewriter::rewrite(
          nm->mkNode(MULT, taylor_sum, nm->mkNode(PLUS, d_one, ru))));
      pbounds.push_back(Rewriter::rewrite(nm->mkNode(PLUS, taylor_sum, ru)));
    }
    else
    {
      Assert(k == SINE);
      Node l = Rewriter::rewrite(nm->mkNode(MINUS, taylor_sum, ru));
      Node u = Rewriter::rewrite(nm->mkNode(PLUS, taylor_sum, ru));
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

void TranscendentalSolver::getPolynomialApproximationBoundForArg(
    Kind k, Node c, unsigned d, std::vector<Node>& pbounds)
{
  getPolynomialApproximationBounds(k, d, pbounds);
  Assert(c.isConst());
  if (k == EXPONENTIAL && c.getConst<Rational>().sgn() == 1)
  {
    NodeManager* nm = NodeManager::currentNM();
    Node tft = nm->mkNode(k, d_zero);
    bool success = false;
    unsigned ds = d;
    TNode ttrf = d_taylor_real_fv;
    TNode tc = c;
    do
    {
      success = true;
      unsigned n = 2 * ds;
      std::pair<Node, Node> taylor = getTaylor(tft, n);
      // check that 1-c^{n+1}/(n+1)! > 0
      Node ru = nm->mkNode(DIVISION, taylor.second[1], taylor.second[0][1]);
      Node rus = ru.substitute(ttrf, tc);
      rus = Rewriter::rewrite(rus);
      Assert(rus.isConst());
      if (rus.getConst<Rational>() > d_one.getConst<Rational>())
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
  }
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
      return std::pair<Node, Node>(d_zero, d_zero);
    }
    Assert(k == EXPONENTIAL);
    return std::pair<Node, Node>(d_one, d_one);
  }
  bool isNeg = csign == -1;

  std::vector<Node> pbounds;
  getPolynomialApproximationBoundForArg(k, c, d, pbounds);

  std::vector<Node> bounds;
  TNode tfv = d_taylor_real_fv;
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
      Assert (pab.isConst());
      bounds.push_back(pab);
    }
    else
    {
      bounds.push_back(Node::null());
    }
  }
  return std::pair<Node, Node>(bounds[0], bounds[1]);
}

Node TranscendentalSolver::mkValidPhase(Node a, Node pi)
{
  return mkBounded(
      NodeManager::currentNM()->mkNode(MULT, mkRationalNode(-1), pi), a, pi);
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
