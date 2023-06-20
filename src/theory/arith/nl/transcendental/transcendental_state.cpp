/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Aina Niemetz
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

#include "theory/arith/nl/transcendental/transcendental_state.h"

#include "expr/skolem_manager.h"
#include "proof/proof.h"
#include "proof/proof_node_manager.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/arith/nl/transcendental/taylor_generator.h"
#include "theory/rewriter.h"
#include "theory/theory_state.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

TranscendentalState::TranscendentalState(Env& env,
                                         InferenceManager& im,
                                         NlModel& model)
    : EnvObj(env),
      d_im(im),
      d_model(model),
      d_trPurify(userContext()),
      d_trPurifies(userContext()),
      d_trPurifyVars(userContext())
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_zero = NodeManager::currentNM()->mkConstInt(Rational(0));
  d_one = NodeManager::currentNM()->mkConstInt(Rational(1));
  d_neg_one = NodeManager::currentNM()->mkConstInt(Rational(-1));
  if (d_env.isTheoryProofProducing())
  {
    d_proof.reset(
        new CDProofSet<CDProof>(d_env, d_env.getUserContext(), "nl-trans"));
  }
}

bool TranscendentalState::isProofEnabled() const
{
  return d_proof.get() != nullptr;
}

CDProof* TranscendentalState::getProof()
{
  Assert(isProofEnabled());
  return d_proof->allocateProof(d_env.getUserContext());
}

void TranscendentalState::init(const std::vector<Node>& xts,
                               std::vector<Node>& needsPurify)
{
  d_funcCongClass.clear();
  d_funcMap.clear();
  d_tf_region.clear();

  Trace("nl-ext-trans-init") << "TranscendentalState::init" << std::endl;
  bool needPi = false;
  // for computing congruence
  std::map<Kind, ArgTrie> argTrie;
  NodeMap::const_iterator itp;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    // Ignore if it is not a transcendental
    if (!isTranscendentalKind(ak))
    {
      continue;
    }
    bool consider = true;
    // if we've already assigned a purified term
    itp = d_trPurify.find(a);
    if (itp != d_trPurify.end())
    {
      consider = itp->second == a;
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
        // for others, if all arguments are variables or constants, we don't
        // have to purify
        for (const Node& ac : a)
        {
          if (!ac.isVar() && !ac.isConst())
          {
            consider = false;
            break;
          }
        }
      }
      if (consider)
      {
        // assume own purified
        d_trPurify[a] = a;
        d_trPurifies[a] = a;
      }
    }
    Trace("nl-ext-trans-init") << "extf: " << a << ", consider=" << consider << std::endl;
    if (!consider)
    {
      // must assign a purified term
      needsPurify.push_back(a);
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
  if (needPi)
  {
    if (d_pi.isNull())
    {
      mkPi();
    }
    getCurrentPiBounds();
  }

  if (TraceIsOn("nl-ext-mv"))
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
    Trace("nl-ext-trans-init") << "...congruent to " << aa << std::endl;
    if (mvaa != mvaaa)
    {
      std::vector<Node> exp;
      for (uint64_t j = 0, size = a.getNumChildren(); j < size; j++)
      {
        exp.push_back(a[j].eqNode(aa[j]));
      }
      Node expn = exp.size() == 1 ? exp[0] : nm->mkNode(Kind::AND, exp);
      Node cong_lemma = expn.impNode(a.eqNode(aa));
      d_im.addPendingLemma(cong_lemma, InferenceId::ARITH_NL_CONGRUENCE);
      Trace("nl-ext-trans-init") << "...needs lemma" << std::endl;
    }
  }
  else
  {
    // new representative of congruence class
    d_funcMap[a.getKind()].push_back(a);
    Trace("nl-ext-trans-init") << "...new rep" << std::endl;
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
    // initialize bounds
    d_pi_bound[0] = nm->mkConstReal(getPiInitialLowerBound());
    d_pi_bound[1] = nm->mkConstReal(getPiInitialUpperBound());
  }
}

void TranscendentalState::getCurrentPiBounds()
{
  Assert(!d_pi.isNull());
  Node piv = d_model.computeAbstractModelValue(d_pi);
  // If the current value of PI is not initialized, or not within bounds, add
  // the lemma. Notice that this preempts the need to explicitly track which
  // lemmas regarding the bound of PI have been added.
  if (!piv.isConst()
      || piv.getConst<Rational>() < d_pi_bound[0].getConst<Rational>()
      || piv.getConst<Rational>() > d_pi_bound[1].getConst<Rational>())
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
    d_im.addPendingLemma(pi_lem, InferenceId::ARITH_NL_T_PI_BOUND, proof);
  }
}

std::pair<Node, Node> TranscendentalState::getClosestSecantPoints(TNode e,
                                                                  TNode center,
                                                                  unsigned d)
{
  auto spit = d_secant_points[e].find(d);
  if (spit == d_secant_points[e].end())
  {
    spit = d_secant_points[e].emplace(d, d_env.getUserContext()).first;
  }
  // bounds are the minimum and maximum previous secant points
  // should not repeat secant points: secant lemmas should suffice to
  // rule out previous assignment
  Assert(std::find(spit->second.begin(), spit->second.end(), center)
         == spit->second.end());
  // Insert into the (temporary) vector. We do not update this vector
  // until we are sure this secant plane lemma has been processed. We do
  // this by mapping the lemma to a side effect below.
  std::vector<Node> spoints{spit->second.begin(), spit->second.end()};
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
  Node rcoeff_n = rewrite(nm->mkNode(Kind::SUB, lower, upper));
  Assert(rcoeff_n.isConst());
  Rational rcoeff = rcoeff_n.getConst<Rational>();
  Assert(rcoeff.sgn() != 0);
  Node res =
      nm->mkNode(Kind::ADD,
                 lval,
                 nm->mkNode(Kind::MULT,
                            nm->mkNode(Kind::DIVISION,
                                       nm->mkNode(Kind::SUB, lval, uval),
                                       nm->mkNode(Kind::SUB, lower, upper)),
                            nm->mkNode(Kind::SUB, arg, lower)));
  Trace("nl-trans") << "Creating secant plane for transcendental function of "
                    << arg << std::endl;
  Trace("nl-trans") << "\tfrom ( " << lower << " ; " << lval << " ) to ( "
                    << upper << " ; " << uval << " )" << std::endl;
  Trace("nl-trans") << "\t" << res << std::endl;
  Trace("nl-trans") << "\trewritten: " << rewrite(res) << std::endl;
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
  Assert(lower.isConst() && upper.isConst());
  Assert(lower.getConst<Rational>() < upper.getConst<Rational>());
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
  Trace("nl-trans-lemma") << "*** Secant plane lemma : " << lem << ", value="
                          << d_model.computeAbstractModelValue(lem)
                          << std::endl;
  Assert(d_model.computeAbstractModelValue(lem) == d_false);
  CDProof* proof = nullptr;
  if (isProofEnabled())
  {
    proof = getProof();
    if (tf.getKind() == Kind::EXPONENTIAL)
    {
      if (csign == 1)
      {
        proof->addStep(lem,
                       PfRule::ARITH_TRANS_EXP_APPROX_ABOVE_POS,
                       {},
                       {nm->mkConstInt(2 * actual_d), tf[0], lower, upper});
      }
      else
      {
        proof->addStep(lem,
                       PfRule::ARITH_TRANS_EXP_APPROX_ABOVE_NEG,
                       {},
                       {nm->mkConstInt(2 * actual_d), tf[0], lower, upper});
      }
    }
    else if (tf.getKind() == Kind::SINE)
    {
      if (convexity == Convexity::CONCAVE)
      {
        proof->addStep(
            lem,
            PfRule::ARITH_TRANS_SINE_APPROX_BELOW_POS,
            {},
            {nm->mkConstInt(2 * actual_d), tf[0], lower, upper, lapprox, uapprox

            });
      }
      else
      {
        proof->addStep(lem,
                       PfRule::ARITH_TRANS_SINE_APPROX_ABOVE_NEG,
                       {},
                       {nm->mkConstInt(2 * actual_d),
                        tf[0],
                        lower,
                        upper,
                        lapprox,
                        uapprox});
      }
    }
  }
  return NlLemma(
      InferenceId::ARITH_NL_T_SECANT, lem, LemmaProperty::NONE, proof);
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
    Node lval =
        rewrite(poly_approx.substitute(d_taylor.getTaylorVariable(), lower));
    Node splane = mkSecantPlane(tf[0], lower, center, lval, cval);
    NlLemma nlem = mkSecantLemma(
        lower, center, lval, cval, csign, convexity, tf, splane, actual_d);
    // The side effect says that if lem is added, then we should add the
    // secant point c for (tf,d).
    nlem.d_secantPoint.push_back(std::make_tuple(tf, d, center));
    d_im.addPendingLemma(nlem, true);
  }

  // take the model value of upper (since may contain PI)
  // Make secant from center to bounds.second
  Node upper = d_model.computeAbstractModelValue(bounds.second);
  Trace("nl-trans") << "...model value of bound " << bounds.second << " is "
                    << upper << std::endl;
  if (center != upper)
  {
    // Figure 3 : P(l), P(u), for s = 1
    Node uval =
        rewrite(poly_approx.substitute(d_taylor.getTaylorVariable(), upper));
    Node splane = mkSecantPlane(tf[0], center, upper, cval, uval);
    NlLemma nlem = mkSecantLemma(
        center, upper, cval, uval, csign, convexity, tf, splane, actual_d);
    // The side effect says that if lem is added, then we should add the
    // secant point c for (tf,d).
    nlem.d_secantPoint.push_back(std::make_tuple(tf, d, center));
    d_im.addPendingLemma(nlem, true);
  }
}

bool TranscendentalState::isPurified(TNode n) const
{
  return d_trPurifies.find(n) != d_trPurifies.end();
}

Node TranscendentalState::getPurifiedForm(TNode n)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  NodeMap::const_iterator it = d_trPurify.find(n);
  if (it != d_trPurify.end())
  {
    return it->second;
  }
  Kind k = n.getKind();
  Assert(k == Kind::SINE || k == Kind::EXPONENTIAL);
  Node y;
  if (isSimplePurify(n))
  {
    y = sm->mkPurifySkolem(n[0]);
  }
  else
  {
    y = sm->mkSkolemFunction(
        SkolemFunId::TRANSCENDENTAL_PURIFY_ARG, nm->realType(), n);
  }
  Node new_n = nm->mkNode(k, y);
  d_trPurify[n] = new_n;
  d_trPurify[new_n] = new_n;
  d_trPurifies[new_n] = n;
  d_trPurifyVars.insert(y);
  return new_n;
}

bool TranscendentalState::isSimplePurify(TNode n)
{
  if (n.getKind() != kind::SINE)
  {
    return true;
  }
  if (!n[0].isConst())
  {
    return false;
  }
  Rational r = n[0].getConst<Rational>();
  // use a fixed value of pi
  Rational piLower = getPiInitialLowerBound();
  return -piLower <= r && r <= piLower;
}

bool TranscendentalState::addModelBoundForPurifyTerm(TNode n, TNode l, TNode u)
{
  Assert(d_funcCongClass.find(n) != d_funcCongClass.end());
  // for each function in the congruence classe
  for (const Node& ctf : d_funcCongClass[n])
  {
    std::vector<Node> mset{ctf};
    // if this purifies another term, we set a bound on the term it
    // purifies as well
    context::CDHashMap<Node, Node>::const_iterator itp = d_trPurifies.find(ctf);
    if (itp != d_trPurifies.end() && itp->second != ctf)
    {
      mset.push_back(itp->second);
    }
    for (const Node& stf : mset)
    {
      Trace("nl-ext-cm") << "...bound for " << stf << " : [" << l << ", " << u
                         << "]" << std::endl;
      if (!d_model.addBound(stf, l, u))
      {
        return false;
      }
    }
  }
  return true;
}

Rational TranscendentalState::getPiInitialLowerBound()
{
  return Rational(103993) / Rational(33102);
}

Rational TranscendentalState::getPiInitialUpperBound()
{
  return Rational(104348) / Rational(33215);
}

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
