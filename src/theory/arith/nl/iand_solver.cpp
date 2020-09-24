/*********************                                                        */
/*! \file iand_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Gereon Kremer, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of integer and (IAND) solver
 **/

#include "theory/arith/nl/iand_solver.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
#include "preprocessing/passes/bv_to_int.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "util/iand.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

IAndSolver::IAndSolver(InferenceManager& im, ArithState& state, NlModel& model)
    : d_im(im),
      d_model(model),
      d_initRefine(state.getUserContext())
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
  d_two = nm->mkConst(Rational(2));
  d_neg_one = nm->mkConst(Rational(-1));
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
  }

  Trace("iand") << "We have " << d_iands.size() << " IAND terms." << std::endl;
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
      // initial refinement lemmas
      std::vector<Node> conj;
      // iand(x,y)=iand(y,x) is guaranteed by rewriting
      Assert(i[0] <= i[1]);
      // conj.push_back(i.eqNode(nm->mkNode(IAND, op, i[1], i[0])));
      // 0 <= iand(x,y) < 2^k
      conj.push_back(nm->mkNode(LEQ, d_zero, i));
      conj.push_back(nm->mkNode(LT, i, twoToK(k)));
      // iand(x,y)<=x
      conj.push_back(nm->mkNode(LEQ, i, i[0]));
      // iand(x,y)<=y
      conj.push_back(nm->mkNode(LEQ, i, i[1]));
      // x=y => iand(x,y)=x
      conj.push_back(nm->mkNode(IMPLIES, i[0].eqNode(i[1]), i.eqNode(i[0])));
      Node lem = conj.size() == 1 ? conj[0] : nm->mkNode(AND, conj);
      Trace("iand-lemma") << "IAndSolver::Lemma: " << lem << " ; INIT_REFINE"
                          << std::endl;
      d_im.addPendingArithLemma(lem, InferenceId::NL_IAND_INIT_REFINE);
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
      if (Trace.isOn("iand-check"))
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
      if (options::iandMode() == options::IandMode::SUM)
      {
        // add lemmas based on sum mode
      }
      else if (options::iandMode() == options::IandMode::BITWISE)
      {
        // add lemmas based on sum mode
      }
      else
      {
        // this is the most naive model-based schema based on model values
        Node lem = valueBasedLemma(i);
        Trace("iand-lemma")
            << "IAndSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
        d_im.addPendingArithLemma(lem, InferenceId::NL_IAND_VALUE_REFINE, true);
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
  return Rewriter::rewrite(bn);
}

Node IAndSolver::twoToK(unsigned k) const
{
  // could be faster
  NodeManager* nm = NodeManager::currentNM();
  Node ret = nm->mkNode(POW, d_two, nm->mkConst(Rational(k)));
  ret = Rewriter::rewrite(ret);
  return ret;
}

Node IAndSolver::twoToKMinusOne(unsigned k) const
{
  // could be faster
  NodeManager* nm = NodeManager::currentNM();
  Node ret = nm->mkNode(MINUS, twoToK(k), d_one);
  ret = Rewriter::rewrite(ret);
  return ret;
}

Node IAndSolver::mkIAnd(unsigned k, Node x, Node y) const
{
  NodeManager* nm = NodeManager::currentNM();
  Node iAndOp = nm->mkConst(IntAnd(k));
  Node ret = nm->mkNode(IAND, iAndOp, x, y);
  ret = Rewriter::rewrite(ret);
  return ret;
}

Node IAndSolver::mkIOr(unsigned k, Node x, Node y) const
{
  Node ret = mkINot(k, mkIAnd(k, mkINot(k, x), mkINot(k, y)));
  ret = Rewriter::rewrite(ret);
  return ret;
}

Node IAndSolver::mkINot(unsigned k, Node x) const
{
  NodeManager* nm = NodeManager::currentNM();
  Node ret = nm->mkNode(MINUS, twoToKMinusOne(k), x);
  ret = Rewriter::rewrite(ret);
  return ret;
}

Node IAndSolver::iextract(unsigned i, unsigned j, Node n) const
{
  NodeManager* nm = NodeManager::currentNM();
  //  ((_ extract i j) n) is n / 2^j mod 2^{i-j+1}
  Node n2j = nm->mkNode(INTS_DIVISION_TOTAL, n, twoToK(j));
  Node ret = nm->mkNode(INTS_MODULUS_TOTAL, n2j, twoToK(i - j + 1));
  ret = Rewriter::rewrite(ret);
  return ret;
}

Node IAndSolver::valueBasedLemma(Node i)
{
  Assert(i.getKind() == IAND);
  Node x = i[0];
  Node y = i[1];

  Node valX = d_model.computeConcreteModelValue(x);
  Node valY = d_model.computeConcreteModelValue(y);

  NodeManager* nm = NodeManager::currentNM();
  Node valC = nm->mkNode(IAND, i.getOperator(), valX, valY);
  valC = Rewriter::rewrite(valC);

  Node lem = nm->mkNode(
      IMPLIES, nm->mkNode(AND, x.eqNode(valX), y.eqNode(valY)), i.eqNode(valC));
  return lem;
}

bool oneBitAnd(bool a, bool b) { return (a && b); }

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
