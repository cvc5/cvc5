/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for representing abstract types.
 */

#include "theory/builtin/generic_op.h"

#include <iostream>

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "util/bitvector.h"
#include "util/floatingpoint.h"
#include "util/iand.h"
#include "util/rational.h"
#include "util/regexp.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const GenericOp& op)
{
  return out << "(GenericOp " << op.getKind() << ')';
}

size_t GenericOpHashFunction::operator()(const GenericOp& op) const
{
  return kind::KindHashFunction()(op.getKind());
}

GenericOp::GenericOp(Kind k) : d_kind(k) {}

GenericOp::GenericOp(const GenericOp& op) : d_kind(op.getKind()) {}

Kind GenericOp::getKind() const { return d_kind; }

bool GenericOp::operator==(const GenericOp& op) const
{
  return getKind() == op.getKind();
}

bool GenericOp::isNumeralIndexedOperatorKind(Kind k)
{
  return k == REGEXP_LOOP || k == BITVECTOR_EXTRACT || k == BITVECTOR_REPEAT
         || k == BITVECTOR_ZERO_EXTEND || k == BITVECTOR_SIGN_EXTEND
         || k == BITVECTOR_ROTATE_LEFT || k == BITVECTOR_ROTATE_RIGHT
         || k == INT_TO_BITVECTOR || k == IAND
         || k == FLOATINGPOINT_TO_FP_FROM_FP
         || k == FLOATINGPOINT_TO_FP_FROM_IEEE_BV
         || k == FLOATINGPOINT_TO_FP_FROM_SBV
         || k == FLOATINGPOINT_TO_FP_FROM_REAL || k == FLOATINGPOINT_TO_SBV
         || k == FLOATINGPOINT_TO_UBV || k == FLOATINGPOINT_TO_SBV_TOTAL
         || k == FLOATINGPOINT_TO_UBV_TOTAL;
}

bool GenericOp::isIndexedOperatorKind(Kind k)
{
  return isNumeralIndexedOperatorKind(k) || k == APPLY_UPDATER
         || k == APPLY_TESTER;
}

std::vector<Node> GenericOp::getIndicesForOperator(Kind k, Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> indices;
  switch (k)
  {
    case REGEXP_LOOP:
    {
      const RegExpLoop& op = n.getConst<RegExpLoop>();
      indices.push_back(nm->mkConstInt(Rational(op.d_loopMinOcc)));
      indices.push_back(nm->mkConstInt(Rational(op.d_loopMaxOcc)));
      break;
    }
    case BITVECTOR_EXTRACT:
    {
      const BitVectorExtract& p = n.getConst<BitVectorExtract>();
      indices.push_back(nm->mkConstInt(Rational(p.d_high)));
      indices.push_back(nm->mkConstInt(Rational(p.d_low)));
      break;
    }
    case BITVECTOR_REPEAT:
      indices.push_back(nm->mkConstInt(
          Rational(n.getConst<BitVectorRepeat>().d_repeatAmount)));
      break;
    case BITVECTOR_ZERO_EXTEND:
      indices.push_back(nm->mkConstInt(
          Rational(n.getConst<BitVectorZeroExtend>().d_zeroExtendAmount)));
      break;
    case BITVECTOR_SIGN_EXTEND:
      indices.push_back(nm->mkConstInt(
          Rational(n.getConst<BitVectorSignExtend>().d_signExtendAmount)));
      break;
    case BITVECTOR_ROTATE_LEFT:
      indices.push_back(nm->mkConstInt(
          Rational(n.getConst<BitVectorRotateLeft>().d_rotateLeftAmount)));
      break;
    case BITVECTOR_ROTATE_RIGHT:
      indices.push_back(nm->mkConstInt(
          Rational(n.getConst<BitVectorRotateRight>().d_rotateRightAmount)));
      break;
    case INT_TO_BITVECTOR:
      indices.push_back(
          nm->mkConstInt(Rational(n.getConst<IntToBitVector>().d_size)));
      break;
    case IAND:
      indices.push_back(nm->mkConstInt(Rational(n.getConst<IntAnd>().d_size)));
      break;
    case FLOATINGPOINT_TO_FP_FROM_FP:
    {
      const FloatingPointToFPFloatingPoint& ffp =
          n.getConst<FloatingPointToFPFloatingPoint>();
      indices.push_back(nm->mkConstInt(ffp.getSize().exponentWidth()));
      indices.push_back(nm->mkConstInt(ffp.getSize().significandWidth()));
    }
    break;
    case FLOATINGPOINT_TO_FP_FROM_IEEE_BV:
    {
      const FloatingPointToFPIEEEBitVector& fbv =
          n.getConst<FloatingPointToFPIEEEBitVector>();
      indices.push_back(nm->mkConstInt(fbv.getSize().exponentWidth()));
      indices.push_back(nm->mkConstInt(fbv.getSize().significandWidth()));
    }
    break;
    case FLOATINGPOINT_TO_FP_FROM_SBV:
    {
      const FloatingPointToFPSignedBitVector& fsbv =
          n.getConst<FloatingPointToFPSignedBitVector>();
      indices.push_back(nm->mkConstInt(fsbv.getSize().exponentWidth()));
      indices.push_back(nm->mkConstInt(fsbv.getSize().significandWidth()));
    }
    break;
    case FLOATINGPOINT_TO_FP_FROM_REAL:
    {
      const FloatingPointToFPReal& fr = n.getConst<FloatingPointToFPReal>();
      indices.push_back(nm->mkConstInt(fr.getSize().exponentWidth()));
      indices.push_back(nm->mkConstInt(fr.getSize().significandWidth()));
    }
    break;
    case FLOATINGPOINT_TO_SBV:
    {
      const FloatingPointToSBV& fsbv = n.getConst<FloatingPointToSBV>();
      indices.push_back(nm->mkConstInt(Rational(fsbv)));
    }
    break;
    case FLOATINGPOINT_TO_UBV:
    {
      const FloatingPointToUBV& fubv = n.getConst<FloatingPointToUBV>();
      indices.push_back(nm->mkConstInt(Rational(fubv)));
    }
    break;
    case FLOATINGPOINT_TO_SBV_TOTAL:
    {
      const FloatingPointToSBVTotal& fsbv =
          n.getConst<FloatingPointToSBVTotal>();
      indices.push_back(nm->mkConstInt(Rational(fsbv)));
    }
    break;
    case FLOATINGPOINT_TO_UBV_TOTAL:
    {
      const FloatingPointToUBVTotal& fubv =
          n.getConst<FloatingPointToUBVTotal>();
      indices.push_back(nm->mkConstInt(Rational(fubv)));
    }
    break;
    case APPLY_TESTER:
    {
      unsigned index = DType::indexOf(n);
      const DType& dt = DType::datatypeOf(n);
      indices.push_back(dt[index].getConstructor());
    }
    break;
    case APPLY_UPDATER:
    {
      unsigned index = DType::indexOf(n);
      const DType& dt = DType::datatypeOf(n);
      unsigned cindex = DType::cindexOf(n);
      indices.push_back(dt[cindex][index].getSelector());
    }
    break;
    default:
      Unhandled() << "GenericOp::getOperatorIndices: unhandled kind " << k;
      break;
  }
  return indices;
}

/** Converts a list of constant integer terms to a list of unsigned integers */
bool convertToNumeralList(const std::vector<Node>& indices,
                          std::vector<uint32_t>& numerals)
{
  for (const Node& i : indices)
  {
    if (i.getKind() != CONST_INTEGER)
    {
      return false;
    }
    const Integer& ii = i.getConst<Rational>().getNumerator();
    if (!ii.fitsUnsignedInt())
    {
      return false;
    }
    numerals.push_back(ii.toUnsignedInt());
  }
  return true;
}

Node GenericOp::getOperatorForIndices(Kind k, const std::vector<Node>& indices)
{
  // all indices should be constant!
  Assert(isIndexedOperatorKind(k));
  NodeManager* nm = NodeManager::currentNM();
  if (isNumeralIndexedOperatorKind(k))
  {
    std::vector<uint32_t> numerals;
    if (!convertToNumeralList(indices, numerals))
    {
      // failed to convert due to non-constant, or overflow on index
      return Node::null();
    }
    switch (k)
    {
      case REGEXP_LOOP:
        Assert(numerals.size() == 2);
        return nm->mkConst(RegExpLoop(numerals[0], numerals[1]));
      case BITVECTOR_EXTRACT:
        Assert(numerals.size() == 2);
        return nm->mkConst(BitVectorExtract(numerals[0], numerals[1]));
      case BITVECTOR_REPEAT:
        Assert(numerals.size() == 1);
        return nm->mkConst(BitVectorRepeat(numerals[0]));
      case BITVECTOR_ZERO_EXTEND:
        Assert(numerals.size() == 1);
        return nm->mkConst(BitVectorZeroExtend(numerals[0]));
      case BITVECTOR_SIGN_EXTEND:
        Assert(numerals.size() == 1);
        return nm->mkConst(BitVectorSignExtend(numerals[0]));
      case BITVECTOR_ROTATE_LEFT:
        Assert(numerals.size() == 1);
        return nm->mkConst(BitVectorRotateLeft(numerals[0]));
      case BITVECTOR_ROTATE_RIGHT:
        Assert(numerals.size() == 1);
        return nm->mkConst(BitVectorRotateRight(numerals[0]));
      case INT_TO_BITVECTOR:
        Assert(numerals.size() == 1);
        return nm->mkConst(IntToBitVector(numerals[0]));
      case IAND:
        Assert(numerals.size() == 1);
        return nm->mkConst(IntAnd(numerals[0]));
      case FLOATINGPOINT_TO_FP_FROM_FP:
        Assert(numerals.size() == 2);
        return nm->mkConst(
            FloatingPointToFPFloatingPoint(numerals[0], numerals[1]));
      case FLOATINGPOINT_TO_FP_FROM_IEEE_BV:
        Assert(numerals.size() == 2);
        return nm->mkConst(
            FloatingPointToFPIEEEBitVector(numerals[0], numerals[1]));
      case FLOATINGPOINT_TO_FP_FROM_SBV:
        Assert(numerals.size() == 2);
        return nm->mkConst(
            FloatingPointToFPSignedBitVector(numerals[0], numerals[1]));
      case FLOATINGPOINT_TO_FP_FROM_REAL:
        Assert(numerals.size() == 2);
        return nm->mkConst(FloatingPointToFPReal(numerals[0], numerals[1]));
      case FLOATINGPOINT_TO_SBV:
        Assert(numerals.size() == 1);
        return nm->mkConst(FloatingPointToSBV(numerals[0]));
      case FLOATINGPOINT_TO_UBV:
        Assert(numerals.size() == 1);
        return nm->mkConst(FloatingPointToUBV(numerals[0]));
      case FLOATINGPOINT_TO_SBV_TOTAL:
        Assert(numerals.size() == 1);
        return nm->mkConst(FloatingPointToSBVTotal(numerals[0]));
      case FLOATINGPOINT_TO_UBV_TOTAL:
        Assert(numerals.size() == 1);
        return nm->mkConst(FloatingPointToUBVTotal(numerals[0]));
      default:
        Unhandled() << "GenericOp::getOperatorForIndices: unhandled kind " << k;
        break;
    }
  }
  else
  {
    switch (k)
    {
      case APPLY_TESTER:
      {
        Assert(indices.size() == 1);
        unsigned index = DType::indexOf(indices[0]);
        const DType& dt = DType::datatypeOf(indices[0]);
        return dt[index].getTester();
      }
      break;
      case APPLY_UPDATER:
      {
        Assert(indices.size() == 1);
        unsigned index = DType::indexOf(indices[0]);
        const DType& dt = DType::datatypeOf(indices[0]);
        unsigned cindex = DType::cindexOf(indices[0]);
        return dt[cindex][index].getUpdater();
      }
      break;
      default:
        Unhandled() << "GenericOp::getOperatorForIndices: unhandled kind" << k;
        break;
    }
  }
  return Node::null();
}

Node GenericOp::getConcreteApp(const Node& app)
{
  Trace("generic-op") << "getConcreteApp " << app << std::endl;
  Assert(app.getKind() == kind::APPLY_INDEXED_SYMBOLIC);
  Kind okind = app.getOperator().getConst<GenericOp>().getKind();
  // determine how many arguments should be passed to the end function. This is
  // usually one, but we handle cases where it is >1.
  size_t nargs = metakind::getMinArityForKind(okind);
  std::vector<Node> indices(app.begin(), app.end() - nargs);
  Node op = getOperatorForIndices(okind, indices);
  // could have a bad index, in which case we don't rewrite
  if (op.isNull())
  {
    return app;
  }
  std::vector<Node> args;
  args.push_back(op);
  args.insert(args.end(), app.end() - nargs, app.end());
  Node ret = NodeManager::currentNM()->mkNode(okind, args);
  // could be ill typed, in which case we don't rewrite
  if (ret.getTypeOrNull(true).isNull())
  {
    return app;
  }
  return ret;
}

}  // namespace cvc5::internal
