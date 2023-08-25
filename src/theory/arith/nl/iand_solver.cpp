/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Makai Mann, Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of integer and (IAND) solver.
 */

#include "theory/arith/nl/iand_solver.h"

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

IAndSolver::IAndSolver(Env& env,
                       InferenceManager& im,
                       NlModel& model)
    : EnvObj(env),
      d_im(im),
      d_model(model),
      d_initRefine(userContext())
{
  NodeManager* nm = NodeManager::currentNM();
  d_false = nm->mkConst(false);
  d_true = nm->mkConst(true);
  d_zero = nm->mkConstInt(Rational(0));
  d_one = nm->mkConstInt(Rational(1));
  d_two = nm->mkConstInt(Rational(2));
}

IAndSolver::~IAndSolver() {}

void IAndSolver::initLastCall(const std::vector<Node>& assertions,
                              const std::vector<Node>& false_asserts,
                              const std::vector<Node>& xts)
{
  d_iands.clear();

  Trace("iand-mv") << "IAND terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak != IAND)
    {
      // don't care about other terms
      continue;
    }
    size_t bsize = a.getOperator().getConst<IntAnd>().d_size;
    d_iands[bsize].push_back(a);
    Trace("iand-mv") << "- " << a << std::endl;
  }
}

void IAndSolver::checkInitialRefine()
{
  Trace("iand-check") << "IAndSolver::checkInitialRefine" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const unsigned, std::vector<Node> >& is : d_iands)
  {
    // the reference bitwidth
    unsigned k = is.first;
    for (const Node& i : is.second)
    {
      if (d_initRefine.find(i) != d_initRefine.end())
      {
        // already sent initial axioms for i in this user context
        continue;
      }
      d_initRefine.insert(i);
      Node op = i.getOperator();
      uint32_t bsize = op.getConst<IntAnd>().d_size;
      Node twok = nm->mkConstInt(Rational(Integer(2).pow(bsize)));
      Node arg0Mod = nm->mkNode(kind::INTS_MODULUS, i[0], twok);
      Node arg1Mod = nm->mkNode(kind::INTS_MODULUS, i[1], twok);
      // initial refinement lemmas
      std::vector<Node> conj;
      // iand(x,y)=iand(y,x) is guaranteed by rewriting
      Assert(i[0] <= i[1]);
      // conj.push_back(i.eqNode(nm->mkNode(IAND, op, i[1], i[0])));
      // 0 <= iand(x,y) < 2^k
      conj.push_back(nm->mkNode(LEQ, d_zero, i));
      conj.push_back(nm->mkNode(LT, i, rewrite(d_iandUtils.twoToK(k))));
      // iand(x,y)<=mod(x, 2^k)
      conj.push_back(nm->mkNode(LEQ, i, arg0Mod));
      // iand(x,y)<=mod(y, 2^k)
      conj.push_back(nm->mkNode(LEQ, i, arg1Mod));
      // x=y => iand(x,y)=mod(x, 2^k)
      conj.push_back(nm->mkNode(IMPLIES, i[0].eqNode(i[1]), i.eqNode(arg0Mod)));
      Node lem = conj.size() == 1 ? conj[0] : nm->mkNode(AND, conj);
      Trace("iand-lemma") << "IAndSolver::Lemma: " << lem << " ; INIT_REFINE"
                          << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_IAND_INIT_REFINE);
    }
  }
}

void IAndSolver::checkFullRefine()
{
  Trace("iand-check") << "IAndSolver::checkFullRefine";
  Trace("iand-check") << "IAND terms: " << std::endl;
  for (const std::pair<const unsigned, std::vector<Node> >& is : d_iands)
  {
    // the reference bitwidth
    unsigned k = is.first;
    for (const Node& i : is.second)
    {
      Node valAndXY = d_model.computeAbstractModelValue(i);
      Node valAndXYC = d_model.computeConcreteModelValue(i);
      if (TraceIsOn("iand-check"))
      {
        Node x = i[0];
        Node y = i[1];

        Node valX = d_model.computeConcreteModelValue(x);
        Node valY = d_model.computeConcreteModelValue(y);

        Trace("iand-check")
            << "* " << i << ", value = " << valAndXY << std::endl;
        Trace("iand-check") << "  actual (" << valX << ", " << valY
                            << ") = " << valAndXYC << std::endl;
        // print the bit-vector versions
        Node bvalX = convertToBvK(k, valX);
        Node bvalY = convertToBvK(k, valY);
        Node bvalAndXY = convertToBvK(k, valAndXY);
        Node bvalAndXYC = convertToBvK(k, valAndXYC);

        Trace("iand-check") << "  bv-value = " << bvalAndXY << std::endl;
        Trace("iand-check") << "  bv-actual (" << bvalX << ", " << bvalY
                            << ") = " << bvalAndXYC << std::endl;
      }
      if (valAndXY == valAndXYC)
      {
        Trace("iand-check") << "...already correct" << std::endl;
        continue;
      }

      // ************* additional lemma schemas go here
      if (options().smt.iandMode == options::IandMode::SUM)
      {
        Node lem = sumBasedLemma(i);  // add lemmas based on sum mode
        Trace("iand-lemma")
            << "IAndSolver::Lemma: " << lem << " ; SUM_REFINE" << std::endl;
        // note that lemma can contain div/mod, and will be preprocessed in the
        // prop engine
        d_im.addPendingLemma(
            lem, InferenceId::ARITH_NL_IAND_SUM_REFINE, nullptr, true);
      }
      else if (options().smt.iandMode == options::IandMode::BITWISE)
      {
        Node lem = bitwiseLemma(i);  // check for violated bitwise axioms
        Trace("iand-lemma")
            << "IAndSolver::Lemma: " << lem << " ; BITWISE_REFINE" << std::endl;
        // note that lemma can contain div/mod, and will be preprocessed in the
        // prop engine
        d_im.addPendingLemma(
            lem, InferenceId::ARITH_NL_IAND_BITWISE_REFINE, nullptr, true);
      }
      else
      {
        // this is the most naive model-based schema based on model values
        Node lem = valueBasedLemma(i);
        Trace("iand-lemma")
            << "IAndSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
        // send the value lemma
        d_im.addPendingLemma(lem,
                             InferenceId::ARITH_NL_IAND_VALUE_REFINE,
                             nullptr,
                             true);
      }
    }
  }
}

Node IAndSolver::convertToBvK(unsigned k, Node n) const
{
  Assert(n.isConst() && n.getType().isInteger());
  NodeManager* nm = NodeManager::currentNM();
  Node iToBvOp = nm->mkConst(IntToBitVector(k));
  Node bn = nm->mkNode(kind::INT_TO_BITVECTOR, iToBvOp, n);
  return rewrite(bn);
}

Node IAndSolver::mkIAnd(unsigned k, Node x, Node y) const
{
  NodeManager* nm = NodeManager::currentNM();
  Node iAndOp = nm->mkConst(IntAnd(k));
  Node ret = nm->mkNode(IAND, iAndOp, x, y);
  ret = rewrite(ret);
  return ret;
}

Node IAndSolver::mkIOr(unsigned k, Node x, Node y) const
{
  Node ret = mkINot(k, mkIAnd(k, mkINot(k, x), mkINot(k, y)));
  ret = rewrite(ret);
  return ret;
}

Node IAndSolver::mkINot(unsigned k, Node x) const
{
  NodeManager* nm = NodeManager::currentNM();
  Node ret = nm->mkNode(SUB, d_iandUtils.twoToKMinusOne(k), x);
  ret = rewrite(ret);
  return ret;
}

Node IAndSolver::valueBasedLemma(Node i)
{
  NodeManager* nm = NodeManager::currentNM();
  Assert(i.getKind() == IAND);
  Node x = i[0];
  Node y = i[1];

  uint32_t bvsize = i.getOperator().getConst<IntAnd>().d_size;
  Node twok = nm->mkConstInt(Rational(Integer(2).pow(bvsize)));
  Node valX = d_model.computeConcreteModelValue(x);
  Node valY = d_model.computeConcreteModelValue(y);
  valX = nm->mkNode(kind::INTS_MODULUS, valX, twok);
  valY = nm->mkNode(kind::INTS_MODULUS, valY, twok);

  Node valC = nm->mkNode(IAND, i.getOperator(), valX, valY);
  valC = rewrite(valC);

  Node xm = nm->mkNode(kind::INTS_MODULUS, x, twok);
  Node ym = nm->mkNode(kind::INTS_MODULUS, y, twok);

  // (=>
  //   (and (= (mod x 2^n) (mod c1 2^n)) (= (mod y 2^n) (mod c2 2^n)))
  //   (= ((_ iand n) x y) rewrite(((_ iand n) (mod c1 2^n) (mod c2 2^n))))
  // Note we use mod above since it ensures the the set of possible literals
  // introduced is finite, since there are finitely many values mod 2^n.
  Node lem = nm->mkNode(IMPLIES,
                        nm->mkNode(AND, xm.eqNode(valX), ym.eqNode(valY)),
                        i.eqNode(valC));
  return lem;
}

Node IAndSolver::sumBasedLemma(Node i)
{
  Assert(i.getKind() == IAND);
  Node x = i[0];
  Node y = i[1];
  uint32_t bvsize = i.getOperator().getConst<IntAnd>().d_size;
  Assert(options().smt.BVAndIntegerGranularity <= 8);
  uint32_t granularity = static_cast<uint32_t>(options().smt.BVAndIntegerGranularity);
  NodeManager* nm = NodeManager::currentNM();
  Node lem = nm->mkNode(
      EQUAL, i, d_iandUtils.createSumNode(x, y, bvsize, granularity));
  return lem;
}

Node IAndSolver::bitwiseLemma(Node i)
{
  Assert(i.getKind() == IAND);
  Node x = i[0];
  Node y = i[1];

  unsigned bvsize = i.getOperator().getConst<IntAnd>().d_size;
  Assert(options().smt.BVAndIntegerGranularity <= 8);
  uint32_t granularity = static_cast<uint32_t>(options().smt.BVAndIntegerGranularity);

  Rational absI = d_model.computeAbstractModelValue(i).getConst<Rational>();
  Rational concI = d_model.computeConcreteModelValue(i).getConst<Rational>();

  Assert(absI.isIntegral());
  Assert(concI.isIntegral());

  BitVector bvAbsI = BitVector(bvsize, absI.getNumerator());
  BitVector bvConcI = BitVector(bvsize, concI.getNumerator());

  NodeManager* nm = NodeManager::currentNM();
  Node lem = d_true;

  // compare each bit to bvI
  Node cond;
  Node bitIAnd;
  uint32_t high_bit;
  for (uint32_t j = 0; j < bvsize; j += granularity)
  {
    high_bit = j + granularity - 1;
    // don't let high_bit pass bvsize
    if (high_bit >= bvsize)
    {
      high_bit = bvsize - 1;
    }

    // check if the abstraction differs from the concrete one on these bits
    if (bvAbsI.extract(high_bit, j) != bvConcI.extract(high_bit, j))
    {
      bitIAnd = d_iandUtils.createBitwiseIAndNode(x, y, high_bit, j);
      // enforce bitwise equality
      lem = nm->mkNode(
          AND,
          lem,
          rewrite(d_iandUtils.iextract(high_bit, j, i)).eqNode(bitIAnd));
    }
  }
  return lem;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
