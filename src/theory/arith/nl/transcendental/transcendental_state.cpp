/*********************                                                        */
/*! \file transcendental_state.cpp
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

#include "theory/arith/nl/transcendental/transcendental_state.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/nl/transcendental/taylor_generator.h"

namespace CVC4 {
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

TranscendentalState::TranscendentalState(InferenceManager& im, NlModel& model)
    : d_im(im), d_model(model)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
  d_neg_one = NodeManager::currentNM()->mkConst(Rational(-1));
}

void TranscendentalState::init(const std::vector<Node>& assertions,
                               const std::vector<Node>& false_asserts,
                               const std::vector<Node>& xts)
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
        if (ak == Kind::SINE)
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
    if (ak == Kind::EXPONENTIAL || ak == Kind::SINE)
    {
      needPi = needPi || (ak == Kind::SINE);
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
            Node expn = exp.size() == 1 ? exp[0] : nm->mkNode(Kind::AND, exp);
            Node cong_lemma = nm->mkNode(Kind::OR, expn.negate(), a.eqNode(aa));
            d_im.addPendingArithLemma(cong_lemma, InferenceId::NL_CONGRUENCE);
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
    else if (ak == Kind::PI)
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
    getCurrentPiBounds();
  }

  if (d_im.hasUsed())
  {
    return;
  }

  // process SINE phase shifting
  for (const Node& a : trNeedsMaster)
  {
    // should not have processed this already
    Assert(d_trMaster.find(a) == d_trMaster.end());
    Kind k = a.getKind();
    Assert(k == Kind::SINE || k == Kind::EXPONENTIAL);
    Node y =
        nm->mkSkolem("y", nm->realType(), "phase shifted trigonometric arg");
    Node new_a = nm->mkNode(k, y);
    d_trSlaves[new_a].insert(new_a);
    d_trSlaves[new_a].insert(a);
    d_trMaster[a] = new_a;
    d_trMaster[new_a] = new_a;
    Node lem;
    if (k == Kind::SINE)
    {
      Trace("nl-ext-tf") << "Basis sine : " << new_a << " for " << a
                         << std::endl;
      Assert(!d_pi.isNull());
      Node shift = nm->mkSkolem("s", nm->integerType(), "number of shifts");
      // TODO : do not introduce shift here, instead needs model-based
      // refinement for constant shifts (cvc4-projects #1284)
      lem = nm->mkNode(
          Kind::AND,
          transcendental::mkValidPhase(y, d_pi),
          nm->mkNode(
              Kind::ITE,
              transcendental::mkValidPhase(a[0], d_pi),
              a[0].eqNode(y),
              a[0].eqNode(nm->mkNode(
                  Kind::PLUS,
                  y,
                  nm->mkNode(
                      Kind::MULT, nm->mkConst(Rational(2)), shift, d_pi)))),
          new_a.eqNode(a));
    }
    else
    {
      // do both equalities to ensure that new_a becomes a preregistered term
      lem = nm->mkNode(Kind::AND, a.eqNode(new_a), a[0].eqNode(y));
    }
    // note we must do preprocess on this lemma
    Trace("nl-ext-lemma") << "NonlinearExtension::Lemma : purify : " << lem
                          << std::endl;
    NlLemma nlem(
        lem, LemmaProperty::PREPROCESS, nullptr, InferenceId::NL_T_PURIFY_ARG);
    d_im.addPendingArithLemma(nlem);
  }

  if (Trace.isOn("nl-ext-mv"))
  {
    Trace("nl-ext-mv") << "Arguments of trancendental functions : "
                       << std::endl;
    for (std::pair<const Kind, std::vector<Node> >& tfl : d_funcMap)
    {
      Kind k = tfl.first;
      if (k == Kind::SINE || k == Kind::EXPONENTIAL)
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

void TranscendentalState::mkPi()
{
  NodeManager* nm = NodeManager::currentNM();
  if (d_pi.isNull())
  {
    d_pi = nm->mkNullaryOperator(nm->realType(), Kind::PI);
    d_pi_2 = Rewriter::rewrite(
        nm->mkNode(Kind::MULT, d_pi, nm->mkConst(Rational(1) / Rational(2))));
    d_pi_neg_2 = Rewriter::rewrite(
        nm->mkNode(Kind::MULT, d_pi, nm->mkConst(Rational(-1) / Rational(2))));
    d_pi_neg = Rewriter::rewrite(
        nm->mkNode(Kind::MULT, d_pi, nm->mkConst(Rational(-1))));
    // initialize bounds
    d_pi_bound[0] = nm->mkConst(Rational(103993) / Rational(33102));
    d_pi_bound[1] = nm->mkConst(Rational(104348) / Rational(33215));
  }
}

void TranscendentalState::getCurrentPiBounds()
{
  NodeManager* nm = NodeManager::currentNM();
  Node pi_lem = nm->mkNode(Kind::AND,
                           nm->mkNode(Kind::GEQ, d_pi, d_pi_bound[0]),
                           nm->mkNode(Kind::LEQ, d_pi, d_pi_bound[1]));
  d_im.addPendingArithLemma(pi_lem, InferenceId::NL_T_PI_BOUND);
}

std::pair<Node, Node> TranscendentalState::getClosestSecantPoints(TNode e,
                                                                  TNode c,
                                                                  unsigned d)
{
  // bounds are the minimum and maximum previous secant points
  // should not repeat secant points: secant lemmas should suffice to
  // rule out previous assignment
  Assert(
      std::find(d_secant_points[e][d].begin(), d_secant_points[e][d].end(), c)
      == d_secant_points[e][d].end());
  // Insert into the (temporary) vector. We do not update this vector
  // until we are sure this secant plane lemma has been processed. We do
  // this by mapping the lemma to a side effect below.
  std::vector<Node> spoints = d_secant_points[e][d];
  spoints.push_back(c);

  // sort
  sortByNlModel(spoints.begin(), spoints.end(), &d_model);
  // get the resulting index of c
  unsigned index =
      std::find(spoints.begin(), spoints.end(), c) - spoints.begin();

  // bounds are the next closest upper/lower bound values
  return {index > 0 ? spoints[index - 1] : Node(),
          index < spoints.size() - 1 ? spoints[index + 1] : Node()};
}

Node TranscendentalState::mkSecantPlane(
    TNode arg, TNode b, TNode c, TNode approx_b, TNode approx_c)
{
  NodeManager* nm = NodeManager::currentNM();
  // Figure 3: S_l( x ), S_u( x ) for s = 0,1
  Node rcoeff_n = Rewriter::rewrite(nm->mkNode(Kind::MINUS, b, c));
  Assert(rcoeff_n.isConst());
  Rational rcoeff = rcoeff_n.getConst<Rational>();
  Assert(rcoeff.sgn() != 0);
  return nm->mkNode(Kind::PLUS,
                    approx_b,
                    nm->mkNode(Kind::MULT,
                               nm->mkNode(Kind::MINUS, approx_b, approx_c),
                               nm->mkConst(rcoeff.inverse()),
                               nm->mkNode(Kind::MINUS, arg, b)));
}

NlLemma TranscendentalState::mkSecantLemma(
    TNode lower, TNode upper, int concavity, TNode tf, TNode splane)
{
  NodeManager* nm = NodeManager::currentNM();
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
  Node antec_n = nm->mkNode(Kind::AND,
                            nm->mkNode(Kind::GEQ, tf[0], lower),
                            nm->mkNode(Kind::LEQ, tf[0], upper));
  Node lem = nm->mkNode(
      Kind::IMPLIES,
      antec_n,
      nm->mkNode(concavity == 1 ? Kind::LEQ : Kind::GEQ, tf, splane));
  Trace("nl-ext-tftp-debug2")
      << "*** Secant plane lemma (pre-rewrite) : " << lem << std::endl;
  lem = Rewriter::rewrite(lem);
  Trace("nl-ext-tftp-lemma") << "*** Secant plane lemma : " << lem << std::endl;
  Assert(d_model.computeAbstractModelValue(lem) == d_false);
  return NlLemma(lem, LemmaProperty::NONE, nullptr, InferenceId::NL_T_SECANT);
}

void TranscendentalState::doSecantLemmas(const std::pair<Node, Node>& bounds,
                                         TNode poly_approx,
                                         TNode c,
                                         TNode approx_c,
                                         TNode tf,
                                         unsigned d,
                                         int concavity)
{
  Trace("nl-ext-tftp-debug2") << "...secant bounds are : " << bounds.first
                              << " ... " << bounds.second << std::endl;
  // take the model value of l or u (since may contain PI)
  // Make secant from bounds.first to c
  Node lval = d_model.computeAbstractModelValue(bounds.first);
  Trace("nl-ext-tftp-debug2") << "...model value of bound " << bounds.first
                              << " is " << lval << std::endl;
  if (lval != c)
  {
    // Figure 3 : P(l), P(u), for s = 0
    Node approx_l = Rewriter::rewrite(
        poly_approx.substitute(d_taylor.getTaylorVariable(), lval));
    Node splane = mkSecantPlane(tf[0], lval, c, approx_l, approx_c);
    NlLemma nlem = mkSecantLemma(lval, c, concavity, tf, splane);
    // The side effect says that if lem is added, then we should add the
    // secant point c for (tf,d).
    nlem.d_secantPoint.push_back(std::make_tuple(tf, d, c));
    d_im.addPendingArithLemma(nlem, true);
  }

  // Make secant from c to bounds.second
  Node uval = d_model.computeAbstractModelValue(bounds.second);
  Trace("nl-ext-tftp-debug2") << "...model value of bound " << bounds.second
                              << " is " << uval << std::endl;
  if (c != uval)
  {
    // Figure 3 : P(l), P(u), for s = 1
    Node approx_u = Rewriter::rewrite(
        poly_approx.substitute(d_taylor.getTaylorVariable(), uval));
    Node splane = mkSecantPlane(tf[0], c, uval, approx_c, approx_u);
    NlLemma nlem = mkSecantLemma(c, uval, concavity, tf, splane);
    // The side effect says that if lem is added, then we should add the
    // secant point c for (tf,d).
    nlem.d_secantPoint.push_back(std::make_tuple(tf, d, c));
    d_im.addPendingArithLemma(nlem, true);
  }
}

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
