/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of pow2 solver.
 */

#include "theory/arith/nl/pow2_solver.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
#include "preprocessing/passes/bv_to_int.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

Pow2Solver::Pow2Solver(Env& env,
                       InferenceManager& im,
                       NlModel& model)
    : EnvObj(env), d_im(im), d_model(model), d_initRefine(userContext())
{
  NodeManager* nm = nodeManager();
  d_false = nm->mkConst(false);
  d_true = nm->mkConst(true);
  d_zero = nm->mkConstInt(Rational(0));
  d_one = nm->mkConstInt(Rational(1));
  d_two = nm->mkConstInt(Rational(2));
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
    if (ak != Kind::POW2)
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
  NodeManager* nm = nodeManager();
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
    // x>=0 -> pow2(x) > 0
    Node xgeq0 = nm->mkNode(Kind::GEQ, i[0], d_zero);
    Node nonegative = nm->mkNode(Kind::GT, i, d_zero);
    conj.push_back(nm->mkNode(Kind::IMPLIES, xgeq0, nonegative));

    // even: x != 0 -> pow2(x) mod 2 = 0
    Node xgt0 = nm->mkNode(Kind::DISTINCT, i[0], d_zero);
    Node mod2 = nm->mkNode(Kind::INTS_MODULUS, i, d_two);
    Node even = nm->mkNode(Kind::EQUAL, mod2, d_zero);
    conj.push_back(nm->mkNode(Kind::IMPLIES, xgt0, even));

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
  NodeManager* nm = nodeManager();
  sortPow2sBasedOnModel();
  // add lemmas for each pow2 term
  for (uint64_t i = 0, size = d_pow2s.size(); i < size; i++)
  {
    Node n = d_pow2s[i];
    Node valPow2xAbstract = d_model.computeAbstractModelValue(n);
    Node valPow2xConcrete = d_model.computeConcreteModelValue(n);
    Node valXConcrete = d_model.computeConcreteModelValue(n[0]);
    if (TraceIsOn("pow2-check"))
    {
      Trace("pow2-check") << "* " << i << ", value = " << valPow2xAbstract
                          << std::endl;
      Trace("pow2-check") << "  actual " << valXConcrete << " = "
                          << valPow2xConcrete << std::endl;
    }
    if (valPow2xAbstract == valPow2xConcrete)
    {
      Trace("pow2-check") << "...already correct" << std::endl;
      continue;
    }

    Integer x = valXConcrete.getConst<Rational>().getNumerator();
    Integer pow2x = valPow2xAbstract.getConst<Rational>().getNumerator();
    // add monotinicity lemmas
    for (uint64_t j = i + 1; j < size; j++)
    {
      Node m = d_pow2s[j];
      Node valPow2yAbstract = d_model.computeAbstractModelValue(m);
      Node valYConcrete = d_model.computeConcreteModelValue(m[0]);

      Integer y = valYConcrete.getConst<Rational>().getNumerator();
      Integer pow2y = valPow2yAbstract.getConst<Rational>().getNumerator();

      if (x >= 0 && x < y && pow2x >= pow2y)
      {
        // 0 <= x /\ x < y => pow2(x) < pow2(y)
        Node x_lt_y = nm->mkNode(Kind::LT, n[0], m[0]);
        Node xgeq0 = nm->mkNode(Kind::LEQ, d_zero, n[0]);
        Node assumption = nm->mkNode(Kind::AND, xgeq0, x_lt_y);
        Node conclusion = nm->mkNode(Kind::LT, n, m);
        Node lem = nm->mkNode(Kind::IMPLIES, assumption, conclusion);
        d_im.addPendingLemma(
            lem, InferenceId::ARITH_NL_POW2_MONOTONE_REFINE, nullptr, true);
      }
      else if (y <= 0 && y < x && pow2x <= pow2y)
      {
        // 0 <= y /\ y < x => pow2(y) < pow2(x)
        Node assumption = nm->mkNode(Kind::LT, m[0], n[0]);
        Node conclusion = nm->mkNode(Kind::LT, m, n);
        Node lem = nm->mkNode(Kind::IMPLIES, assumption, conclusion);
        d_im.addPendingLemma(
            lem, InferenceId::ARITH_NL_POW2_MONOTONE_REFINE, nullptr, true);
      }
    }

    // neg lemmas: pow2(x) = 0 whenever x < 0
    if (x < 0 && pow2x != 0)
    {
      Node assumption = nm->mkNode(Kind::LT, n[0], d_zero);
      Node conclusion = nm->mkNode(Kind::EQUAL, n, mkZero(n.getType()));
      Node lem = nm->mkNode(Kind::IMPLIES, assumption, conclusion);
      d_im.addPendingLemma(
          lem, InferenceId::ARITH_NL_POW2_NEG_REFINE, nullptr, true);
    }

    // div 0: x div pow2(x) = 0 whenever x >= 0
    if (x >= 0 && x > pow2x)
    {
      Node assumption = nm->mkNode(Kind::GEQ, n[0], d_zero);
      Node div_zero = nm->mkNode(Kind::INTS_DIVISION, n[0], n);
      Node conclusion = nm->mkNode(Kind::EQUAL, div_zero, d_zero);
      Node lem = nm->mkNode(Kind::IMPLIES, assumption, conclusion);
      d_im.addPendingLemma(
          lem, InferenceId::ARITH_NL_POW2_DIV0_CASE_REFINE, nullptr, true);
    }

    // lower bound: x >= 7 => pow2(x) > kx + k^2
    if (x >= 7 && pow2x <= x * x * 2)
    {
      Node d_seven = nm->mkConstInt(Rational(7));
      Node k_gt_5 = nm->mkNode(Kind::GEQ, valXConcrete, d_seven);
      Node x_gt_k = nm->mkNode(Kind::GEQ, n[0], valXConcrete);
      Node assumption = nm->mkNode(Kind::AND, x_gt_k, k_gt_5);
      Node kx = nm->mkNode(Kind::MULT, valXConcrete, n[0]);
      Node k_squar = nm->mkNode(Kind::MULT, valXConcrete, valXConcrete);
      Node kx_plus_k_squar = nm->mkNode(Kind::ADD, kx, k_squar);
      Node conclusion = nm->mkNode(Kind::GT, n, kx_plus_k_squar);
      Node lem = nm->mkNode(Kind::IMPLIES, assumption, conclusion);
      d_im.addPendingLemma(lem,
                           InferenceId::ARITH_NL_POW2_LOWER_BOUND_CASE_REFINE,
                           nullptr,
                           true);
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
  Assert(i.getKind() == Kind::POW2);
  Node x = i[0];

  Node valX = d_model.computeConcreteModelValue(x);

  NodeManager* nm = nodeManager();
  Node valC = nm->mkNode(Kind::POW2, valX);
  valC = rewrite(valC);

  return nm->mkNode(Kind::IMPLIES, x.eqNode(valX), i.eqNode(valC));
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
