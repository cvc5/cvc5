/*********************                                                        */
/*! \file transcendental_state.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Gereon Kremer
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

TranscendentalState::TranscendentalState(InferenceManager& im,
                                         NlModel& model,
                                         ProofNodeManager* pnm,
                                         context::UserContext* c)
    : d_im(im), d_model(model), d_pnm(pnm), d_ctx(c)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
  d_neg_one = NodeManager::currentNM()->mkConst(Rational(-1));
  if (d_pnm != nullptr)
  {
    d_proof.reset(new CDProofSet<CDProof>(d_pnm, d_ctx, "nl-trans"));
    d_proofChecker.reset(new TranscendentalProofRuleChecker());
    d_proofChecker->registerTo(pnm->getChecker());
  }
}

bool TranscendentalState::isProofEnabled() const
{
  return d_proof.get() != nullptr;
}

CDProof* TranscendentalState::getProof()
{
  Assert(isProofEnabled());
  return d_proof->allocateProof(d_ctx);
}

void TranscendentalState::init(const std::vector<Node>& xts,
                               std::vector<Node>& needsMaster)
{
  d_funcCongClass.clear();
  d_funcMap.clear();
  d_tf_region.clear();

  bool needPi = false;
  // for computing congruence
  std::map<Kind, ArgTrie> argTrie;
  for (std::size_t i = 0, xsize = xts.size(); i < xsize; ++i)
  {
    // Ignore if it is not a transcendental
    if (!isTranscendentalKind(xts[i].getKind()))
    {
      continue;
    }
    Node a = xts[i];
    Kind ak = a.getKind();
    bool consider = true;
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
        needsMaster.push_back(a);
      }
      else
      {
        d_trMaster[a] = a;
        d_trSlaves[a].insert(a);
      }
    }
    if (ak == Kind::EXPONENTIAL || ak == Kind::SINE)
    {
      needPi = needPi || (ak == Kind::SINE);
      // if we didn't indicate that it should be purified above
      if (consider)
      {
        ensureCongruence(a, argTrie);
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

void TranscendentalState::ensureCongruence(TNode a,
                                           std::map<Kind, ArgTrie>& argTrie)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> repList;
  for (const Node& ac : a)
  {
    Node r = d_model.computeConcreteModelValue(ac);
    repList.push_back(r);
  }
  Node aa = argTrie[a.getKind()].add(a, repList);
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
      Node cong_lemma = expn.impNode(a.eqNode(aa));
      d_im.addPendingArithLemma(cong_lemma, InferenceId::NL_CONGRUENCE);
    }
  }
  else
  {
    // new representative of congruence class
    d_funcMap[a.getKind()].push_back(a);
  }
  // add to congruence class
  d_funcCongClass[aa].push_back(a);
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
  CDProof* proof = nullptr;
  if (isProofEnabled())
  {
    proof = getProof();
    proof->addStep(
        pi_lem, PfRule::ARITH_TRANS_PI, {}, {d_pi_bound[0], d_pi_bound[1]});
  }
  d_im.addPendingArithLemma(pi_lem, InferenceId::NL_T_PI_BOUND, proof);
}

std::pair<Node, Node> TranscendentalState::getClosestSecantPoints(TNode e,
                                                                  TNode center,
                                                                  unsigned d)
{
  // bounds are the minimum and maximum previous secant points
  // should not repeat secant points: secant lemmas should suffice to
  // rule out previous assignment
  Assert(std::find(
             d_secant_points[e][d].begin(), d_secant_points[e][d].end(), center)
         == d_secant_points[e][d].end());
  // Insert into the (temporary) vector. We do not update this vector
  // until we are sure this secant plane lemma has been processed. We do
  // this by mapping the lemma to a side effect below.
  std::vector<Node> spoints = d_secant_points[e][d];
  spoints.push_back(center);

  // sort
  sortByNlModel(spoints.begin(), spoints.end(), &d_model);
  // get the resulting index of c
  unsigned index =
      std::find(spoints.begin(), spoints.end(), center) - spoints.begin();

  // bounds are the next closest upper/lower bound values
  return {index > 0 ? spoints[index - 1] : Node(),
          index < spoints.size() - 1 ? spoints[index + 1] : Node()};
}

Node TranscendentalState::mkSecantPlane(
    TNode arg, TNode lower, TNode upper, TNode lval, TNode uval)
{
  NodeManager* nm = NodeManager::currentNM();
  // Figure 3: S_l( x ), S_u( x ) for s = 0,1
  Node rcoeff_n = Rewriter::rewrite(nm->mkNode(Kind::MINUS, lower, upper));
  Assert(rcoeff_n.isConst());
  Rational rcoeff = rcoeff_n.getConst<Rational>();
  Assert(rcoeff.sgn() != 0);
  Node res =
      nm->mkNode(Kind::PLUS,
                 lval,
                 nm->mkNode(Kind::MULT,
                            nm->mkNode(Kind::DIVISION,
                                       nm->mkNode(Kind::MINUS, lval, uval),
                                       nm->mkNode(Kind::MINUS, lower, upper)),
                            nm->mkNode(Kind::MINUS, arg, lower)));
  Trace("nl-trans") << "Creating secant plane for transcendental function of "
                    << arg << std::endl;
  Trace("nl-trans") << "\tfrom ( " << lower << " ; " << lval << " ) to ( "
                    << upper << " ; " << uval << " )" << std::endl;
  Trace("nl-trans") << "\t" << res << std::endl;
  Trace("nl-trans") << "\trewritten: " << Rewriter::rewrite(res) << std::endl;
  return res;
}

NlLemma TranscendentalState::mkSecantLemma(TNode lower,
                                           TNode upper,
                                           TNode lapprox,
                                           TNode uapprox,
                                           int csign,
                                           Convexity convexity,
                                           TNode tf,
                                           TNode splane,
                                           unsigned actual_d)
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
  Trace("nl-trans") << "Bound for secant plane: " << lower << " <= " << tf[0]
                    << " <= " << upper << std::endl;
  Trace("nl-trans") << "\t" << antec_n << std::endl;
  // Convex: actual value is below the secant
  // Concave: actual value is above the secant
  Node lem = nm->mkNode(
      Kind::IMPLIES,
      antec_n,
      nm->mkNode(
          convexity == Convexity::CONVEX ? Kind::LEQ : Kind::GEQ, tf, splane));
  Trace("nl-trans-lemma") << "*** Secant plane lemma (pre-rewrite) : " << lem
                          << std::endl;
  lem = Rewriter::rewrite(lem);
  Trace("nl-trans-lemma") << "*** Secant plane lemma : " << lem << std::endl;
  Assert(d_model.computeAbstractModelValue(lem) == d_false);
  return NlLemma(lem, LemmaProperty::NONE, nullptr, InferenceId::NL_T_SECANT);
}

void TranscendentalState::doSecantLemmas(const std::pair<Node, Node>& bounds,
                                         TNode poly_approx,
                                         TNode center,
                                         TNode cval,
                                         TNode tf,
                                         Convexity convexity,
                                         unsigned d,
                                         unsigned actual_d)
{
  int csign = center.getConst<Rational>().sgn();
  Trace("nl-trans") << "...do secant lemma with center " << center << " val "
                    << cval << " sign " << csign << std::endl;
  Trace("nl-trans") << "...secant bounds are : " << bounds.first << " ... "
                    << bounds.second << std::endl;
  // take the model value of lower (since may contain PI)
  // Make secant from bounds.first to center
  Node lower = d_model.computeAbstractModelValue(bounds.first);
  Trace("nl-trans") << "...model value of bound " << bounds.first << " is "
                    << lower << std::endl;
  if (lower != center)
  {
    // Figure 3 : P(l), P(u), for s = 0
    Node lval = Rewriter::rewrite(
        poly_approx.substitute(d_taylor.getTaylorVariable(), lower));
    Node splane = mkSecantPlane(tf[0], lower, center, lval, cval);
    NlLemma nlem = mkSecantLemma(
        lower, center, lval, cval, csign, convexity, tf, splane, actual_d);
    // The side effect says that if lem is added, then we should add the
    // secant point c for (tf,d).
    nlem.d_secantPoint.push_back(std::make_tuple(tf, d, center));
    d_im.addPendingArithLemma(nlem, true);
  }

  // take the model value of upper (since may contain PI)
  // Make secant from center to bounds.second
  Node upper = d_model.computeAbstractModelValue(bounds.second);
  Trace("nl-trans") << "...model value of bound " << bounds.second << " is "
                    << upper << std::endl;
  if (center != upper)
  {
    // Figure 3 : P(l), P(u), for s = 1
    Node uval = Rewriter::rewrite(
        poly_approx.substitute(d_taylor.getTaylorVariable(), upper));
    Node splane = mkSecantPlane(tf[0], center, upper, cval, uval);
    NlLemma nlem = mkSecantLemma(
        center, upper, cval, uval, csign, convexity, tf, splane, actual_d);
    // The side effect says that if lem is added, then we should add the
    // secant point c for (tf,d).
    nlem.d_secantPoint.push_back(std::make_tuple(tf, d, center));
    d_im.addPendingArithLemma(nlem, true);
  }
}

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
