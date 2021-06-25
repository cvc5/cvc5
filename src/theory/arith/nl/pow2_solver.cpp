/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Makai Mann, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of pow2 solver.
 */

#include "theory/arith/nl/pow2_solver.h"

#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_state.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {

Pow2Solver::Pow2Solver(InferenceManager& im, ArithState& state, NlModel& model)
    : d_im(im), d_model(model), d_initRefine(state.getUserContext())
{
  NodeManager* nm = NodeManager::currentNM();
  d_false = nm->mkConst(false);
  d_true = nm->mkConst(true);
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
  d_two = nm->mkConst(Rational(2));
}

Pow2Solver::~Pow2Solver() {}

void Pow2Solver::initLastCall(const std::vector<Node>& assertions,
                              const std::vector<Node>& false_asserts,
                              const std::vector<Node>& xts)
{
  d_pow2s.clear();
  Trace("pow2-mv") << "POW2 terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak != POW2)
    {
      // don't care about other terms
      continue;
    }
    d_pow2s.push_back(a);
  }
  Trace("pow2") << "We have " << d_pow2s.size() << " pow2 terms." << std::endl;
}

void Pow2Solver::checkInitialRefine()
{
  Trace("pow2-check") << "Pow2Solver::checkInitialRefine" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& i : d_pow2s)
  {
    if (d_initRefine.find(i) != d_initRefine.end())
    {
      // already sent initial axioms for i in this user context
      continue;
    }
    d_initRefine.insert(i);
    // initial refinement lemmas
    std::vector<Node> conj;
    // x>=0 -> x < pow2(x)
    Node xgeq0 = nm->mkNode(LEQ, d_zero, i[0]);
    Node xltpow2x = nm->mkNode(LT, i[0], i);
    conj.push_back(nm->mkNode(IMPLIES, xgeq0, xltpow2x));
    Node lem = nm->mkAnd(conj);
    Trace("pow2-lemma") << "Pow2Solver::Lemma: " << lem << " ; INIT_REFINE"
                        << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_POW2_INIT_REFINE);
  }
}

void Pow2Solver::sortPow2sBasedOnModel()
{
  struct
  {
    bool operator()(Node a, Node b, NlModel& model) const
    {
      return model.computeConcreteModelValue(a[0])
             < model.computeConcreteModelValue(b[0]);
    }
  } modelSort;
  using namespace std::placeholders;
  std::sort(
      d_pow2s.begin(), d_pow2s.end(), std::bind(modelSort, _1, _2, d_model));
}

void Pow2Solver::checkFullRefine()
{
  Trace("pow2-check") << "Pow2Solver::checkFullRefine" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  sortPow2sBasedOnModel();
  // add lemmas for each pow2 term
  for (uint64_t i = 0, size = d_pow2s.size(); i < size; i++)
  {
    Node n = d_pow2s[i];
    Node valPow2xAbstract = d_model.computeAbstractModelValue(n);
    Node valPow2xConcrete = d_model.computeConcreteModelValue(n);
    Node valXConcrete = d_model.computeConcreteModelValue(n[0]);
    if (Trace.isOn("pow2-check"))
    {
      Trace("pow2-check") << "* " << i << ", value = " << valPow2xAbstract
                          << std::endl;
      Trace("pow2-check") << "  actual (" << valXConcrete << ", "
                          << ") = " << valPow2xConcrete << std::endl;
    }
    if (valPow2xAbstract == valPow2xConcrete)
    {
      Trace("pow2-check") << "...already correct" << std::endl;
      continue;
    }

    // add monotinicity lemmas
    for (uint64_t j = i + 1; j < size; j++)
    {
      Node m = d_pow2s[j];
      Node valPow2yConcrete = d_model.computeConcreteModelValue(m);
      Node valYConcrete = d_model.computeConcreteModelValue(m[0]);

      Integer x = valXConcrete.getConst<Rational>().getNumerator();
      Integer y = valYConcrete.getConst<Rational>().getNumerator();
      Integer pow2x = valPow2xConcrete.getConst<Rational>().getNumerator();
      Integer pow2y = valPow2yConcrete.getConst<Rational>().getNumerator();

      if (x <= y && pow2x > pow2y)
      {
        Node assumption = nm->mkNode(LEQ, n[0], m[0]);
        Node conclusion = nm->mkNode(LEQ, n, m);
        Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
        d_im.addPendingLemma(
            lem, InferenceId::ARITH_NL_POW2_MONOTONE_REFINE, nullptr, true);
        }
    }

    // Place holder for additional lemma schemas

    // End of additional lemma schemas

    // this is the most naive model-based schema based on model values
    Node lem = valueBasedLemma(n);
    Trace("pow2-lemma") << "Pow2Solver::Lemma: " << lem << " ; VALUE_REFINE"
                        << std::endl;
    // send the value lemma
    d_im.addPendingLemma(
        lem, InferenceId::ARITH_NL_POW2_VALUE_REFINE, nullptr, true);
  }
}
Node Pow2Solver::valueBasedLemma(Node i)
{
  Assert(i.getKind() == POW2);
  Node x = i[0];

  Node valX = d_model.computeConcreteModelValue(x);

  NodeManager* nm = NodeManager::currentNM();
  Node valC = nm->mkNode(POW2, valX);
  valC = Rewriter::rewrite(valC);

  Node lem = nm->mkNode(IMPLIES, x.eqNode(valX), i.eqNode(valC));
  return lem;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
