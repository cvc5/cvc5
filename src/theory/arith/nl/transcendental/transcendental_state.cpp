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
#include "theory/arith/nl/transcendental/utils.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

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
                  nm->mkNode(Kind::MULT, nm->mkConst(Rational(2)), shift, d_pi)))),
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
    d_pi_neg =
        Rewriter::rewrite(nm->mkNode(Kind::MULT, d_pi, nm->mkConst(Rational(-1))));
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

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
