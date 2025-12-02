/******************************************************************************
 * Top contributors (to current version):
 *    Zvika Berger
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of parametric integer and (PIAND) solver.
 */

#include "theory/arith/nl/piand_solver.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
#include "preprocessing/passes/bv_to_int.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"
#include "util/iand.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

PIAndSolver::PIAndSolver(Env& env, InferenceManager& im, NlModel& model)
    : EnvObj(env),
      d_im(im),
      d_model(model),
      d_iandUtils(env.getNodeManager()),
      d_initRefine(userContext())
{
  NodeManager* nm = nodeManager();
  d_false = nm->mkConst(false);
  d_true = nm->mkConst(true);
  d_zero = nm->mkConstInt(Rational(0));
  d_one = nm->mkConstInt(Rational(1));
  d_two = nm->mkConstInt(Rational(2));
}

PIAndSolver::~PIAndSolver() {}

void PIAndSolver::initLastCall(const std::vector<Node>& assertions,
                               const std::vector<Node>& false_asserts,
                               const std::vector<Node>& xts)
{
  d_piands.clear();

  Trace("piand-mv") << "PIAND terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak != Kind::PIAND)
    {
      // don't care about other terms
      continue;
    }
    d_piands[a[0]].push_back(a);
  }
  Trace("piand") << "We have " << d_piands.size() << " PIAND bit-width."
                 << std::endl;
}

void PIAndSolver::checkInitialRefine()
{
  Trace("piand-check") << "PIAndSolver::checkInitialRefine" << std::endl;
  NodeManager* nm = nodeManager();
  for (const std::pair<const Node, std::vector<Node> >& is : d_piands)
  {
    // the reference bitwidth
    Node k = is.first;
    for (const Node& i : is.second)
    {
      Node x = i[1];
      Node y = i[2];
      if (d_initRefine.find(i) != d_initRefine.end())
      {
        // already sent initial axioms for i in this user context
        continue;
      }
      d_initRefine.insert(i);
      Node twok = nm->mkNode(Kind::POW2, k);
      Node arg0Mod = nm->mkNode(Kind::INTS_MODULUS, x, twok);
      Node arg1Mod = nm->mkNode(Kind::INTS_MODULUS, y, twok);
      Node arg0Mod2 = nm->mkNode(Kind::INTS_MODULUS, x, d_two);
      Node arg1Mod2 = nm->mkNode(Kind::INTS_MODULUS, y, d_two);
      Node plus = nm->mkNode(Kind::ADD, x, y);
      Node twok_minus_one = nm->mkNode(Kind::SUB, twok, d_one);
      Node k_gt_0 = nm->mkNode(Kind::GT, k, d_zero);
      Node x_geq_zero = nm->mkNode(Kind::GEQ, x, d_zero);
      Node x_lt_pow2 = nm->mkNode(Kind::LT, x, twok);
      Node x_range = nm->mkNode(Kind::AND, x_geq_zero, x_lt_pow2);
      Node y_geq_zero = nm->mkNode(Kind::GEQ, y, d_zero);
      Node y_lt_pow2 = nm->mkNode(Kind::LT, y, twok);
      Node y_range = nm->mkNode(Kind::AND, y_geq_zero, y_lt_pow2);
      // initial refinement lemmas
      std::vector<Node> conj;
      Assert(x <= y);
      // max: x > 0 && x < 2^k && y = 2^k -1 -> piand(k,x,y) = x
      Node y_modpow2_eq_max = nm->mkNode(Kind::EQUAL, y, twok_minus_one);
      Node assum_max = nm->mkNode(Kind::AND, k_gt_0, y_modpow2_eq_max, x_range);
      conj.push_back(nm->mkNode(Kind::IMPLIES, assum_max, i.eqNode(x)));
      // max: y > 0 && y < 2^k && x = 2^k -1 -> piand(k,x,y) = y
      Node x_modpow2_eq_max = nm->mkNode(Kind::EQUAL, x, twok_minus_one);
      Node assum_max_x =
          nm->mkNode(Kind::AND, k_gt_0, x_modpow2_eq_max, y_range);
      conj.push_back(nm->mkNode(Kind::IMPLIES, assum_max_x, i.eqNode(y)));
      // min: y = 0 -> piand(k,x,y) = 0
      Node eq_y_zero = nm->mkNode(Kind::EQUAL, y, d_zero);
      conj.push_back(nm->mkNode(Kind::IMPLIES, eq_y_zero, i.eqNode(d_zero)));
      // min-x: x = 0 -> piand(k,x,y) = 0
      Node eq_x_zero = nm->mkNode(Kind::EQUAL, x, d_zero);
      conj.push_back(nm->mkNode(Kind::IMPLIES, eq_x_zero, i.eqNode(d_zero)));
      // idempotence: k > 0 && x > 0 && x < 2^k && x = y -> piand(k,x,y) = x
      Node eq_y_x = nm->mkNode(Kind::EQUAL, y, x);
      Node assum_idempotence = nm->mkNode(Kind::AND, k_gt_0, eq_y_x, x_range);
      conj.push_back(nm->mkNode(Kind::IMPLIES, assum_idempotence, i.eqNode(x)));
      // symmetry: piand(k,x,y) = piand(k,y,x)
      Node piand_y_x = nm->mkNode(Kind::PIAND, k, y, x);
      conj.push_back(nm->mkNode(Kind::EQUAL, i, piand_y_x));
      // range1: 0 <= piand(k,x,y)
      conj.push_back(nm->mkNode(Kind::LEQ, d_zero, i));
      // range 2: 0 <= x -> piand(k,x,y) <= x
      Node i_leq_x = nm->mkNode(Kind::LEQ, i, x);
      conj.push_back(nm->mkNode(Kind::IMPLIES, x_geq_zero, i_leq_x));
      // range 3: 0 <= y -> piand(k,x,y) <= y
      Node i_leq_y = nm->mkNode(Kind::LEQ, i, y);
      conj.push_back(nm->mkNode(Kind::IMPLIES, y_geq_zero, i_leq_y));
      // negative bitwidth: k <= 0 -> piand(k,x, y) = 0
      Node k_le_0 = nm->mkNode(Kind::LEQ, k, d_zero);
      conj.push_back(nm->mkNode(Kind::IMPLIES, k_le_0, i.eqNode(d_zero)));
      // lsb lemmas: x mod 2 = 0 => piand(k,x,y) % 2 = 0
      Node piand_mod_two = nm->mkNode(Kind::INTS_MODULUS, i, d_two);
      Node arg1Mod2_eq_zero = nm->mkNode(Kind::EQUAL, arg1Mod2, d_zero);
      conj.push_back(nm->mkNode(
          Kind::IMPLIES, arg1Mod2_eq_zero, piand_mod_two.eqNode(d_zero)));
      // lsb lemmas: y mod 2 = 0 => piand(k,x,y) % 2 = 0
      Node arg0Mod2_eq_zero = nm->mkNode(Kind::EQUAL, arg0Mod2, d_zero);
      conj.push_back(nm->mkNode(
          Kind::IMPLIES, arg0Mod2_eq_zero, piand_mod_two.eqNode(d_zero)));

      // insert lemmas
      Node lem = conj.size() == 1 ? conj[0] : nm->mkNode(Kind::AND, conj);
      Trace("piand-lemma") << "PIAndSolver::Lemma: " << lem << " ; INIT_REFINE"
                           << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_PIAND_INIT_REFINE);
    }
  }
}

void PIAndSolver::checkFullRefine() {}

Node PIAndSolver::valueBasedLemma(Node i)
{
  Assert(i.getKind() == Kind::PIAND);

  Node k = i[0];
  Node x = i[1];
  Node y = i[2];

  Node valK = d_model.computeConcreteModelValue(k);
  Node valX = d_model.computeConcreteModelValue(x);
  Node valY = d_model.computeConcreteModelValue(y);

  NodeManager* nm = nodeManager();
  Node valC = nm->mkNode(Kind::PIAND, valK, valX, valY);

  valC = rewrite(valC);
  Node lem = nm->mkNode(
      Kind::IMPLIES,
      nm->mkNode(Kind::AND, k.eqNode(valK), x.eqNode(valX), y.eqNode(valY)),
      i.eqNode(valC));
  return lem;
}

Node PIAndSolver::sumBasedLemma(Node i, Kind kind)
{
  Assert(i.getKind() == Kind::PIAND);
  Node k = d_model.computeConcreteModelValue(i[0]);
  Node x = i[1];
  Node y = i[2];
  uint64_t granularity = options().smt.BVAndIntegerGranularity;
  uint64_t int_k = k.getConst<Rational>().getNumerator().toUnsignedInt();
  NodeManager* nm = nodeManager();
  // i[0] >= k => i = sum
  Node width = nm->mkNode(kind, i[0], k);
  Node condition;
  kind = Kind::EQUAL;
  Node pow2_k = nm->mkConstInt(Integer(2).pow(int_k));
  Node zero = nm->mkConstInt(Rational(0));
  Node x_pos = nm->mkNode(Kind::GEQ, x, zero);
  Node y_pos = nm->mkNode(Kind::GEQ, y, zero);
  Node x_lt_pow2 = nm->mkNode(Kind::LT, x, pow2_k);
  Node y_lt_pow2 = nm->mkNode(Kind::LT, y, pow2_k);
  Node bound_x = nm->mkNode(Kind::AND, x_lt_pow2, x_pos);
  Node bound_y = nm->mkNode(Kind::AND, y_lt_pow2, y_pos);
  condition = nm->mkNode(Kind::AND, bound_x, width);
  Node then =
      nm->mkNode(kind, i, d_iandUtils.createSumNode(x, y, int_k, granularity));
  Node lem = nm->mkNode(Kind::IMPLIES, condition, then);
  return lem;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
