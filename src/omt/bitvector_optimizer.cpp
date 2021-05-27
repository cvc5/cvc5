/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou, Michael Chang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Optimizer for BitVector type.
 */

#include "omt/bitvector_optimizer.h"

#include "options/smt_options.h"
#include "smt/smt_engine.h"
#include "util/bitvector.h"

using namespace cvc5::smt;
namespace cvc5::omt {

OMTOptimizerBitVector::OMTOptimizerBitVector(bool isSigned)
    : d_isSigned(isSigned)
{
}

BitVector OMTOptimizerBitVector::computeAverage(const BitVector& a,
                                                const BitVector& b,
                                                bool isSigned)
{
  // computes (a + b) / 2 without overflow
  // rounding towards -infinity: -1.5 --> -2,  1.5 --> 1
  // average = (a / 2) + (b / 2) + (((a % 2) + (b % 2)) / 2)
  uint32_t aMod2 = static_cast<uint32_t>(a.isBitSet(0));
  uint32_t bMod2 = static_cast<uint32_t>(b.isBitSet(0));
  BitVector aMod2PlusbMod2Div2(a.getSize(), (aMod2 + bMod2) / 2);
  BitVector bv1 = BitVector::mkOne(a.getSize());
  return (isSigned) ? ((a.arithRightShift(bv1) + b.arithRightShift(bv1)
                        + aMod2PlusbMod2Div2))
                    : ((a.logicalRightShift(bv1) + b.logicalRightShift(bv1)
                        + aMod2PlusbMod2Div2));
}

OptimizationResult OMTOptimizerBitVector::minimize(SmtEngine* optChecker,
                                                   TNode target)
{
  // the smt engine to which we send intermediate queries
  // for the binary search.
  NodeManager* nm = optChecker->getNodeManager();
  Result intermediateSatResult = optChecker->checkSat();
  // Model-value of objective (used in optimization loop)
  Node value;
  if (intermediateSatResult.isUnknown())
  {
    return OptimizationResult(OptimizationResult::UNKNOWN, value);
  }
  if (intermediateSatResult.isSat() == Result::UNSAT)
  {
    return OptimizationResult(OptimizationResult::UNSAT, value);
  }

  // value equals to upperBound
  value = optChecker->getValue(target);

  // this gets the bitvector!
  BitVector bvValue = value.getConst<BitVector>();
  unsigned int bvSize = bvValue.getSize();

  // lowerbound
  BitVector lowerBound = ((this->d_isSigned) ? (BitVector::mkMinSigned(bvSize))
                                             : (BitVector::mkZero(bvSize)));
  // upperbound must be a satisfying value
  // and value == upperbound
  BitVector upperBound = bvValue;

  Kind LTOperator =
      ((d_isSigned) ? (kind::BITVECTOR_SLT) : (kind::BITVECTOR_ULT));
  Kind GEOperator =
      ((d_isSigned) ? (kind::BITVECTOR_SGE) : (kind::BITVECTOR_UGE));

  // the pivot value for binary search,
  // pivot = (lowerBound + upperBound) / 2
  // rounded towards -infinity
  BitVector pivot;
  while ((d_isSigned && lowerBound.signedLessThan(upperBound))
         || (!d_isSigned && lowerBound.unsignedLessThan(upperBound)))
  {
    pivot = computeAverage(lowerBound, upperBound, d_isSigned);
    optChecker->push();
    if (lowerBound == pivot)
    {
      optChecker->assertFormula(
          nm->mkNode(kind::EQUAL, target, nm->mkConst(lowerBound)));
    }
    else
    {
      // lowerBound <= target < pivot
      optChecker->assertFormula(
          nm->mkNode(kind::AND,
                     nm->mkNode(GEOperator, target, nm->mkConst(lowerBound)),
                     nm->mkNode(LTOperator, target, nm->mkConst(pivot))));
    }
    intermediateSatResult = optChecker->checkSat();
    if (intermediateSatResult.isUnknown() || intermediateSatResult.isNull())
    {
      return OptimizationResult(OptimizationResult::UNKNOWN, value);
    }
    if (intermediateSatResult.isSat() == Result::SAT)
    {
      value = optChecker->getValue(target);
      upperBound = value.getConst<BitVector>();
    }
    else if (intermediateSatResult.isSat() == Result::UNSAT)
    {
      if (lowerBound == pivot)
      {
        // lowerBound == pivot ==> upperbound = lowerbound + 1
        // and lowerbound <= target < upperbound is UNSAT
        // return the upperbound
        return OptimizationResult(OptimizationResult::OPTIMAL, value);
      }
      else
      {
        lowerBound = pivot;
      }
    }
    else
    {
      return OptimizationResult(OptimizationResult::UNKNOWN, value);
    }
    optChecker->pop();
  }
  return OptimizationResult(OptimizationResult::OPTIMAL, value);
}

OptimizationResult OMTOptimizerBitVector::maximize(SmtEngine* optChecker,
                                                   TNode target)
{
  // the smt engine to which we send intermediate queries
  // for the binary search.
  NodeManager* nm = optChecker->getNodeManager();
  Result intermediateSatResult = optChecker->checkSat();
  // Model-value of objective (used in optimization loop)
  Node value;
  if (intermediateSatResult.isUnknown())
  {
    return OptimizationResult(OptimizationResult::UNKNOWN, value);
  }
  if (intermediateSatResult.isSat() == Result::UNSAT)
  {
    return OptimizationResult(OptimizationResult::UNSAT, value);
  }

  // value equals to upperBound
  value = optChecker->getValue(target);

  // this gets the bitvector!
  BitVector bvValue = value.getConst<BitVector>();
  unsigned int bvSize = bvValue.getSize();

  // lowerbound must be a satisfying value
  // and value == lowerbound
  BitVector lowerBound = bvValue;

  // upperbound
  BitVector upperBound = ((this->d_isSigned) ? (BitVector::mkMaxSigned(bvSize))
                                             : (BitVector::mkOnes(bvSize)));

  Kind LEOperator =
      ((d_isSigned) ? (kind::BITVECTOR_SLE) : (kind::BITVECTOR_ULE));
  Kind GTOperator =
      ((d_isSigned) ? (kind::BITVECTOR_SGT) : (kind::BITVECTOR_UGT));

  // the pivot value for binary search,
  // pivot = (lowerBound + upperBound) / 2
  // rounded towards -infinity
  BitVector pivot;
  while ((d_isSigned && lowerBound.signedLessThan(upperBound))
         || (!d_isSigned && lowerBound.unsignedLessThan(upperBound)))
  {
    pivot = computeAverage(lowerBound, upperBound, d_isSigned);

    optChecker->push();
    // notice that we don't have boundary condition here
    // because lowerBound == pivot / lowerBound == upperBound + 1 is also
    // covered
    // pivot < target <= upperBound
    optChecker->assertFormula(
        nm->mkNode(kind::AND,
                   nm->mkNode(GTOperator, target, nm->mkConst(pivot)),
                   nm->mkNode(LEOperator, target, nm->mkConst(upperBound))));
    intermediateSatResult = optChecker->checkSat();
    if (intermediateSatResult.isUnknown() || intermediateSatResult.isNull())
    {
      return OptimizationResult(OptimizationResult::UNKNOWN, value);
    }
    if (intermediateSatResult.isSat() == Result::SAT)
    {
      value = optChecker->getValue(target);
      lowerBound = value.getConst<BitVector>();
    }
    else if (intermediateSatResult.isSat() == Result::UNSAT)
    {
      if (lowerBound == pivot)
      {
        // upperbound = lowerbound + 1
        // and lowerbound < target <= upperbound is UNSAT
        // return the lowerbound
        return OptimizationResult(OptimizationResult::OPTIMAL, value);
      }
      else
      {
        upperBound = pivot;
      }
    }
    else
    {
      return OptimizationResult(OptimizationResult::UNKNOWN, value);
    }
    optChecker->pop();
  }
  return OptimizationResult(OptimizationResult::OPTIMAL, value);
}

}  // namespace cvc5::omt
