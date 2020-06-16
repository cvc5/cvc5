/*********************                                                        */
/*! \file fp_converter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Mathias Preiner, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Conversion of floating-point operations to bit-vectors using symfpu.
 **/

#include "theory/fp/fp_converter.h"
#include "theory/theory.h"
// theory.h Only needed for the leaf test

#include <vector>

#ifdef CVC4_USE_SYMFPU
#include "symfpu/core/add.h"
#include "symfpu/core/classify.h"
#include "symfpu/core/compare.h"
#include "symfpu/core/convert.h"
#include "symfpu/core/divide.h"
#include "symfpu/core/fma.h"
#include "symfpu/core/ite.h"
#include "symfpu/core/multiply.h"
#include "symfpu/core/packing.h"
#include "symfpu/core/remainder.h"
#include "symfpu/core/sign.h"
#include "symfpu/core/sqrt.h"
#include "symfpu/utils/numberOfRoundingModes.h"
#include "symfpu/utils/properties.h"
#endif

#ifdef CVC4_USE_SYMFPU
namespace symfpu {
using namespace ::CVC4::theory::fp::symfpuSymbolic;

#define CVC4_SYM_ITE_DFN(T)                                                \
  template <>                                                              \
  struct ite<symbolicProposition, T>                                       \
  {                                                                        \
    static const T iteOp(const symbolicProposition &_cond,                 \
                         const T &_l,                                      \
                         const T &_r)                                      \
    {                                                                      \
      ::CVC4::NodeManager *nm = ::CVC4::NodeManager::currentNM();          \
                                                                           \
      ::CVC4::Node cond = _cond;                                           \
      ::CVC4::Node l = _l;                                                 \
      ::CVC4::Node r = _r;                                                 \
                                                                           \
      /* Handle some common symfpu idioms */                               \
      if (cond.isConst())                                                  \
      {                                                                    \
        return (cond == nm->mkConst(::CVC4::BitVector(1U, 1U))) ? l : r;   \
      }                                                                    \
      else                                                                 \
      {                                                                    \
        if (l.getKind() == ::CVC4::kind::BITVECTOR_ITE)                    \
        {                                                                  \
          if (l[1] == r)                                                   \
          {                                                                \
            return nm->mkNode(                                             \
                ::CVC4::kind::BITVECTOR_ITE,                               \
                nm->mkNode(::CVC4::kind::BITVECTOR_AND,                    \
                           cond,                                           \
                           nm->mkNode(::CVC4::kind::BITVECTOR_NOT, l[0])), \
                l[2],                                                      \
                r);                                                        \
          }                                                                \
          else if (l[2] == r)                                              \
          {                                                                \
            return nm->mkNode(                                             \
                ::CVC4::kind::BITVECTOR_ITE,                               \
                nm->mkNode(::CVC4::kind::BITVECTOR_AND, cond, l[0]),       \
                l[1],                                                      \
                r);                                                        \
          }                                                                \
        }                                                                  \
        else if (r.getKind() == ::CVC4::kind::BITVECTOR_ITE)               \
        {                                                                  \
          if (r[1] == l)                                                   \
          {                                                                \
            return nm->mkNode(                                             \
                ::CVC4::kind::BITVECTOR_ITE,                               \
                nm->mkNode(::CVC4::kind::BITVECTOR_AND,                    \
                           nm->mkNode(::CVC4::kind::BITVECTOR_NOT, cond),  \
                           nm->mkNode(::CVC4::kind::BITVECTOR_NOT, r[0])), \
                r[2],                                                      \
                l);                                                        \
          }                                                                \
          else if (r[2] == l)                                              \
          {                                                                \
            return nm->mkNode(                                             \
                ::CVC4::kind::BITVECTOR_ITE,                               \
                nm->mkNode(::CVC4::kind::BITVECTOR_AND,                    \
                           nm->mkNode(::CVC4::kind::BITVECTOR_NOT, cond),  \
                           r[0]),                                          \
                r[1],                                                      \
                l);                                                        \
          }                                                                \
        }                                                                  \
      }                                                                    \
      return T(nm->mkNode(::CVC4::kind::BITVECTOR_ITE, cond, l, r));       \
    }                                                                      \
  }

// Can (unsurprisingly) only ITE things which contain Nodes
CVC4_SYM_ITE_DFN(traits::rm);
CVC4_SYM_ITE_DFN(traits::prop);
CVC4_SYM_ITE_DFN(traits::sbv);
CVC4_SYM_ITE_DFN(traits::ubv);

#undef CVC4_SYM_ITE_DFN

template <>
traits::ubv orderEncode<traits, traits::ubv>(const traits::ubv &b)
{
  return orderEncodeBitwise<traits, traits::ubv>(b);
}

template <>
stickyRightShiftResult<traits> stickyRightShift(const traits::ubv &input,
                                                const traits::ubv &shiftAmount)
{
  return stickyRightShiftBitwise<traits>(input, shiftAmount);
}

template <>
void probabilityAnnotation<traits, traits::prop>(const traits::prop &p,
                                                 const probability &pr)
{
  // For now, do nothing...
  return;
}
};
#endif

#ifndef CVC4_USE_SYMFPU
#define PRECONDITION(X) Assert((X))
#define SYMFPU_NUMBER_OF_ROUNDING_MODES 5
#endif

namespace CVC4 {
namespace theory {
namespace fp {
namespace symfpuSymbolic {

symbolicRoundingMode traits::RNE(void) { return symbolicRoundingMode(0x01); };
symbolicRoundingMode traits::RNA(void) { return symbolicRoundingMode(0x02); };
symbolicRoundingMode traits::RTP(void) { return symbolicRoundingMode(0x04); };
symbolicRoundingMode traits::RTN(void) { return symbolicRoundingMode(0x08); };
symbolicRoundingMode traits::RTZ(void) { return symbolicRoundingMode(0x10); };
void traits::precondition(const bool b)
{
  AlwaysAssert(b);
  return;
}
void traits::postcondition(const bool b)
{
  AlwaysAssert(b);
  return;
}
void traits::invariant(const bool b)
{
  AlwaysAssert(b);
  return;
}

void traits::precondition(const prop &p) { return; }
void traits::postcondition(const prop &p) { return; }
void traits::invariant(const prop &p) { return; }
// This allows us to use the symfpu literal / symbolic assertions in the
// symbolic back-end
typedef traits t;

bool symbolicProposition::checkNodeType(const TNode node)
{
  TypeNode tn = node.getType(false);
  return tn.isBitVector() && tn.getBitVectorSize() == 1;
}

symbolicProposition::symbolicProposition(const Node n) : nodeWrapper(n)
{
  PRECONDITION(checkNodeType(*this));
}  // Only used within this header so could be friend'd
symbolicProposition::symbolicProposition(bool v)
    : nodeWrapper(
          NodeManager::currentNM()->mkConst(BitVector(1U, (v ? 1U : 0U))))
{
  PRECONDITION(checkNodeType(*this));
}
symbolicProposition::symbolicProposition(const symbolicProposition &old)
    : nodeWrapper(old)
{
  PRECONDITION(checkNodeType(*this));
}

symbolicProposition symbolicProposition::operator!(void)const
{
  return symbolicProposition(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_NOT, *this));
}

symbolicProposition symbolicProposition::operator&&(
    const symbolicProposition &op) const
{
  return symbolicProposition(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_AND, *this, op));
}

symbolicProposition symbolicProposition::operator||(
    const symbolicProposition &op) const
{
  return symbolicProposition(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_OR, *this, op));
}

symbolicProposition symbolicProposition::operator==(
    const symbolicProposition &op) const
{
  return symbolicProposition(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_COMP, *this, op));
}

symbolicProposition symbolicProposition::operator^(
    const symbolicProposition &op) const
{
  return symbolicProposition(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_XOR, *this, op));
}

bool symbolicRoundingMode::checkNodeType(const TNode n)
{
#ifdef CVC4_USE_SYMFPU
  return n.getType(false).isBitVector(SYMFPU_NUMBER_OF_ROUNDING_MODES);
#else
  return false;
#endif
}

symbolicRoundingMode::symbolicRoundingMode(const Node n) : nodeWrapper(n)
{
  PRECONDITION(checkNodeType(*this));
}

#ifdef CVC4_USE_SYMFPU
symbolicRoundingMode::symbolicRoundingMode(const unsigned v)
    : nodeWrapper(NodeManager::currentNM()->mkConst(
          BitVector(SYMFPU_NUMBER_OF_ROUNDING_MODES, v)))
{
  PRECONDITION((v & (v - 1)) == 0 && v != 0);  // Exactly one bit set
  PRECONDITION(checkNodeType(*this));
}
#else
symbolicRoundingMode::symbolicRoundingMode(const unsigned v)
    : nodeWrapper(NodeManager::currentNM()->mkConst(
          BitVector(SYMFPU_NUMBER_OF_ROUNDING_MODES, v)))
{
  Unreachable();
}
#endif

symbolicRoundingMode::symbolicRoundingMode(const symbolicRoundingMode &old)
    : nodeWrapper(old)
{
  PRECONDITION(checkNodeType(*this));
}

symbolicProposition symbolicRoundingMode::valid(void) const
{
  NodeManager *nm = NodeManager::currentNM();
  Node zero(nm->mkConst(BitVector(SYMFPU_NUMBER_OF_ROUNDING_MODES, 0u)));

  // Is there a better encoding of this?
  return symbolicProposition(nm->mkNode(
      kind::BITVECTOR_AND,
      nm->mkNode(
          kind::BITVECTOR_COMP,
          nm->mkNode(kind::BITVECTOR_AND,
                     *this,
                     nm->mkNode(kind::BITVECTOR_SUB,
                                *this,
                                nm->mkConst(BitVector(
                                    SYMFPU_NUMBER_OF_ROUNDING_MODES, 1u)))),
          zero),
      nm->mkNode(kind::BITVECTOR_NOT,
                 nm->mkNode(kind::BITVECTOR_COMP, *this, zero))));
}

symbolicProposition symbolicRoundingMode::operator==(
    const symbolicRoundingMode &op) const
{
  return symbolicProposition(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_COMP, *this, op));
}

template <bool isSigned>
Node symbolicBitVector<isSigned>::boolNodeToBV(Node node) const
{
  Assert(node.getType().isBoolean());
  NodeManager *nm = NodeManager::currentNM();
  return nm->mkNode(kind::ITE,
                    node,
                    nm->mkConst(BitVector(1U, 1U)),
                    nm->mkConst(BitVector(1U, 0U)));
}

template <bool isSigned>
Node symbolicBitVector<isSigned>::BVToBoolNode(Node node) const
{
  Assert(node.getType().isBitVector());
  Assert(node.getType().getBitVectorSize() == 1);
  NodeManager *nm = NodeManager::currentNM();
  return nm->mkNode(kind::EQUAL, node, nm->mkConst(BitVector(1U, 1U)));
}

template <bool isSigned>
Node symbolicBitVector<isSigned>::fromProposition(Node node) const
{
  return node;
}
template <bool isSigned>
Node symbolicBitVector<isSigned>::toProposition(Node node) const
{
  return boolNodeToBV(node);
}

template <bool isSigned>
symbolicBitVector<isSigned>::symbolicBitVector(const Node n) : nodeWrapper(n)
{
  PRECONDITION(checkNodeType(*this));
}

template <bool isSigned>
bool symbolicBitVector<isSigned>::checkNodeType(const TNode n)
{
  return n.getType(false).isBitVector();
}

template <bool isSigned>
symbolicBitVector<isSigned>::symbolicBitVector(const bwt w, const unsigned v)
    : nodeWrapper(NodeManager::currentNM()->mkConst(BitVector(w, v)))
{
  PRECONDITION(checkNodeType(*this));
}
template <bool isSigned>
symbolicBitVector<isSigned>::symbolicBitVector(const symbolicProposition &p)
    : nodeWrapper(fromProposition(p))
{
}
template <bool isSigned>
symbolicBitVector<isSigned>::symbolicBitVector(
    const symbolicBitVector<isSigned> &old)
    : nodeWrapper(old)
{
  PRECONDITION(checkNodeType(*this));
}
template <bool isSigned>
symbolicBitVector<isSigned>::symbolicBitVector(const BitVector &old)
    : nodeWrapper(NodeManager::currentNM()->mkConst(old))
{
  PRECONDITION(checkNodeType(*this));
}

template <bool isSigned>
bwt symbolicBitVector<isSigned>::getWidth(void) const
{
  return this->getType(false).getBitVectorSize();
}

/*** Constant creation and test ***/
template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::one(const bwt &w)
{
  return symbolicBitVector<isSigned>(w, 1);
}
template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::zero(const bwt &w)
{
  return symbolicBitVector<isSigned>(w, 0);
}
template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::allOnes(const bwt &w)
{
  return symbolicBitVector<isSigned>(~zero(w));
}

template <bool isSigned>
symbolicProposition symbolicBitVector<isSigned>::isAllOnes() const
{
  return (*this == symbolicBitVector<isSigned>::allOnes(this->getWidth()));
}
template <bool isSigned>
symbolicProposition symbolicBitVector<isSigned>::isAllZeros() const
{
  return (*this == symbolicBitVector<isSigned>::zero(this->getWidth()));
}

template <>
symbolicBitVector<true> symbolicBitVector<true>::maxValue(const bwt &w)
{
  symbolicBitVector<true> leadingZero(symbolicBitVector<true>::zero(1));
  symbolicBitVector<true> base(symbolicBitVector<true>::allOnes(w - 1));

  return symbolicBitVector<true>(::CVC4::NodeManager::currentNM()->mkNode(
      ::CVC4::kind::BITVECTOR_CONCAT, leadingZero, base));
}

template <>
symbolicBitVector<false> symbolicBitVector<false>::maxValue(const bwt &w)
{
  return symbolicBitVector<false>::allOnes(w);
}

template <>
symbolicBitVector<true> symbolicBitVector<true>::minValue(const bwt &w)
{
  symbolicBitVector<true> leadingOne(symbolicBitVector<true>::one(1));
  symbolicBitVector<true> base(symbolicBitVector<true>::zero(w - 1));

  return symbolicBitVector<true>(::CVC4::NodeManager::currentNM()->mkNode(
      ::CVC4::kind::BITVECTOR_CONCAT, leadingOne, base));
}

template <>
symbolicBitVector<false> symbolicBitVector<false>::minValue(const bwt &w)
{
  return symbolicBitVector<false>::zero(w);
}

/*** Operators ***/
template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator<<(
    const symbolicBitVector<isSigned> &op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_SHL, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator>>(
    const symbolicBitVector<isSigned> &op) const
{
  return symbolicBitVector<isSigned>(NodeManager::currentNM()->mkNode(
      (isSigned) ? kind::BITVECTOR_ASHR : kind::BITVECTOR_LSHR, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator|(
    const symbolicBitVector<isSigned> &op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_OR, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator&(
    const symbolicBitVector<isSigned> &op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_AND, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator+(
    const symbolicBitVector<isSigned> &op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_PLUS, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator-(
    const symbolicBitVector<isSigned> &op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_SUB, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator*(
    const symbolicBitVector<isSigned> &op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_MULT, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator/(
    const symbolicBitVector<isSigned> &op) const
{
  return symbolicBitVector<isSigned>(NodeManager::currentNM()->mkNode(
      (isSigned) ? kind::BITVECTOR_SDIV : kind::BITVECTOR_UDIV_TOTAL,
      *this,
      op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator%(
    const symbolicBitVector<isSigned> &op) const
{
  return symbolicBitVector<isSigned>(NodeManager::currentNM()->mkNode(
      (isSigned) ? kind::BITVECTOR_SREM : kind::BITVECTOR_UREM_TOTAL,
      *this,
      op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator-(void) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_NEG, *this));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator~(void)const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_NOT, *this));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::increment() const
{
  return symbolicBitVector<isSigned>(NodeManager::currentNM()->mkNode(
      kind::BITVECTOR_PLUS, *this, one(this->getWidth())));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::decrement() const
{
  return symbolicBitVector<isSigned>(NodeManager::currentNM()->mkNode(
      kind::BITVECTOR_SUB, *this, one(this->getWidth())));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::signExtendRightShift(
    const symbolicBitVector<isSigned> &op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_ASHR, *this, op));
}

/*** Modular operations ***/
// No overflow checking so these are the same as other operations
template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::modularLeftShift(
    const symbolicBitVector<isSigned> &op) const
{
  return *this << op;
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::modularRightShift(
    const symbolicBitVector<isSigned> &op) const
{
  return *this >> op;
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::modularIncrement()
    const
{
  return this->increment();
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::modularDecrement()
    const
{
  return this->decrement();
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::modularAdd(
    const symbolicBitVector<isSigned> &op) const
{
  return *this + op;
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::modularNegate() const
{
  return -(*this);
}

/*** Comparisons ***/

template <bool isSigned>
symbolicProposition symbolicBitVector<isSigned>::operator==(
    const symbolicBitVector<isSigned> &op) const
{
  return symbolicProposition(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_COMP, *this, op));
}

template <bool isSigned>
symbolicProposition symbolicBitVector<isSigned>::operator<=(
    const symbolicBitVector<isSigned> &op) const
{
  // Consider adding kind::BITVECTOR_SLEBV and BITVECTOR_ULEBV
  return (*this < op) || (*this == op);
}

template <bool isSigned>
symbolicProposition symbolicBitVector<isSigned>::operator>=(
    const symbolicBitVector<isSigned> &op) const
{
  return (*this > op) || (*this == op);
}

template <bool isSigned>
symbolicProposition symbolicBitVector<isSigned>::operator<(
    const symbolicBitVector<isSigned> &op) const
{
  return symbolicProposition(NodeManager::currentNM()->mkNode(
      (isSigned) ? kind::BITVECTOR_SLTBV : kind::BITVECTOR_ULTBV, *this, op));
}

template <bool isSigned>
symbolicProposition symbolicBitVector<isSigned>::operator>(
    const symbolicBitVector<isSigned> &op) const
{
  return symbolicProposition(NodeManager::currentNM()->mkNode(
      (isSigned) ? kind::BITVECTOR_SLTBV : kind::BITVECTOR_ULTBV, op, *this));
}

/*** Type conversion ***/
// CVC4 nodes make no distinction between signed and unsigned, thus ...
template <bool isSigned>
symbolicBitVector<true> symbolicBitVector<isSigned>::toSigned(void) const
{
  return symbolicBitVector<true>(*this);
}
template <bool isSigned>
symbolicBitVector<false> symbolicBitVector<isSigned>::toUnsigned(void) const
{
  return symbolicBitVector<false>(*this);
}

/*** Bit hacks ***/
template <>
symbolicBitVector<true> symbolicBitVector<true>::extend(bwt extension) const
{
  NodeBuilder<> construct(kind::BITVECTOR_SIGN_EXTEND);
  construct << NodeManager::currentNM()->mkConst<BitVectorSignExtend>(
                   BitVectorSignExtend(extension))
            << *this;

  return symbolicBitVector<true>(construct);
}

template <>
symbolicBitVector<false> symbolicBitVector<false>::extend(bwt extension) const
{
  NodeBuilder<> construct(kind::BITVECTOR_ZERO_EXTEND);
  construct << NodeManager::currentNM()->mkConst<BitVectorZeroExtend>(
                   BitVectorZeroExtend(extension))
            << *this;

  return symbolicBitVector<false>(construct);
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::contract(
    bwt reduction) const
{
  PRECONDITION(this->getWidth() > reduction);

  NodeBuilder<> construct(kind::BITVECTOR_EXTRACT);
  construct << NodeManager::currentNM()->mkConst<BitVectorExtract>(
                   BitVectorExtract((this->getWidth() - 1) - reduction, 0))
            << *this;

  return symbolicBitVector<isSigned>(construct);
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::resize(
    bwt newSize) const
{
  bwt width = this->getWidth();

  if (newSize > width)
  {
    return this->extend(newSize - width);
  }
  else if (newSize < width)
  {
    return this->contract(width - newSize);
  }
  else
  {
    return *this;
  }
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::matchWidth(
    const symbolicBitVector<isSigned> &op) const
{
  PRECONDITION(this->getWidth() <= op.getWidth());
  return this->extend(op.getWidth() - this->getWidth());
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::append(
    const symbolicBitVector<isSigned> &op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_CONCAT, *this, op));
}

// Inclusive of end points, thus if the same, extracts just one bit
template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::extract(
    bwt upper, bwt lower) const
{
  PRECONDITION(upper >= lower);

  NodeBuilder<> construct(kind::BITVECTOR_EXTRACT);
  construct << NodeManager::currentNM()->mkConst<BitVectorExtract>(
                   BitVectorExtract(upper, lower))
            << *this;

  return symbolicBitVector<isSigned>(construct);
}

floatingPointTypeInfo::floatingPointTypeInfo(const TypeNode type)
    : FloatingPointSize(type.getConst<FloatingPointSize>())
{
  PRECONDITION(type.isFloatingPoint());
}
floatingPointTypeInfo::floatingPointTypeInfo(unsigned exp, unsigned sig)
    : FloatingPointSize(exp, sig)
{
}
floatingPointTypeInfo::floatingPointTypeInfo(const floatingPointTypeInfo &old)
    : FloatingPointSize(old)
{
}

TypeNode floatingPointTypeInfo::getTypeNode(void) const
{
  return NodeManager::currentNM()->mkFloatingPointType(*this);
}
}

FpConverter::FpConverter(context::UserContext* user)
    :
#ifdef CVC4_USE_SYMFPU
      d_fpMap(user),
      d_rmMap(user),
      d_boolMap(user),
      d_ubvMap(user),
      d_sbvMap(user),
#endif
      d_additionalAssertions(user)
{
}

#ifdef CVC4_USE_SYMFPU
Node FpConverter::ufToNode(const fpt &format, const uf &u) const
{
  NodeManager *nm = NodeManager::currentNM();

  FloatingPointSize fps(format.getTypeNode().getConst<FloatingPointSize>());

  // This is not entirely obvious but it builds a float from components
  // Particularly, if the components can be constant folded, it should
  // build a Node containing a constant FloatingPoint number

  ubv packed(symfpu::pack<traits>(format, u));
  Node value =
      nm->mkNode(nm->mkConst(FloatingPointToFPIEEEBitVector(fps)), packed);
  return value;
}

Node FpConverter::rmToNode(const rm &r) const
{
  NodeManager *nm = NodeManager::currentNM();

  Node transVar = r;

  Node RNE = traits::RNE();
  Node RNA = traits::RNA();
  Node RTP = traits::RTP();
  Node RTN = traits::RTN();
  Node RTZ = traits::RTZ();

  Node value = nm->mkNode(
      kind::ITE,
      nm->mkNode(kind::EQUAL, transVar, RNE),
      nm->mkConst(roundNearestTiesToEven),
      nm->mkNode(kind::ITE,
                 nm->mkNode(kind::EQUAL, transVar, RNA),
                 nm->mkConst(roundNearestTiesToAway),
                 nm->mkNode(kind::ITE,
                            nm->mkNode(kind::EQUAL, transVar, RTP),
                            nm->mkConst(roundTowardPositive),
                            nm->mkNode(kind::ITE,
                                       nm->mkNode(kind::EQUAL, transVar, RTN),
                                       nm->mkConst(roundTowardNegative),
                                       nm->mkConst(roundTowardZero)))));
  return value;
}

Node FpConverter::propToNode(const prop &p) const
{
  NodeManager *nm = NodeManager::currentNM();
  Node value =
      nm->mkNode(kind::EQUAL, p, nm->mkConst(::CVC4::BitVector(1U, 1U)));
  return value;
}
Node FpConverter::ubvToNode(const ubv &u) const { return u; }
Node FpConverter::sbvToNode(const sbv &s) const { return s; }
// Creates the components constraint
FpConverter::uf FpConverter::buildComponents(TNode current)
{
  Assert(Theory::isLeafOf(current, THEORY_FP)
         || current.getKind() == kind::FLOATINGPOINT_TO_FP_REAL);

  NodeManager *nm = NodeManager::currentNM();
  uf tmp(nm->mkNode(kind::FLOATINGPOINT_COMPONENT_NAN, current),
         nm->mkNode(kind::FLOATINGPOINT_COMPONENT_INF, current),
         nm->mkNode(kind::FLOATINGPOINT_COMPONENT_ZERO, current),
         nm->mkNode(kind::FLOATINGPOINT_COMPONENT_SIGN, current),
         nm->mkNode(kind::FLOATINGPOINT_COMPONENT_EXPONENT, current),
         nm->mkNode(kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND, current));

  d_additionalAssertions.push_back(tmp.valid(fpt(current.getType())));

  return tmp;
}
#endif

// Non-convertible things should only be added to the stack at the very start,
// thus...
#define CVC4_FPCONV_PASSTHROUGH Assert(workStack.empty())

Node FpConverter::convert(TNode node)
{
#ifdef CVC4_USE_SYMFPU
  std::vector<TNode> workStack;
  TNode result = node;

  workStack.push_back(node);

  NodeManager *nm = NodeManager::currentNM();

  while (!workStack.empty())
  {
    TNode current = workStack.back();
    workStack.pop_back();
    result = current;

    TypeNode t(current.getType());

    if (t.isRoundingMode())
    {
      rmMap::const_iterator i(d_rmMap.find(current));

      if (i == d_rmMap.end())
      {
        if (Theory::isLeafOf(current, THEORY_FP))
        {
          if (current.getKind() == kind::CONST_ROUNDINGMODE)
          {
            /******** Constants ********/
            switch (current.getConst<RoundingMode>())
            {
              case roundNearestTiesToEven:
                d_rmMap.insert(current, traits::RNE());
                break;
              case roundNearestTiesToAway:
                d_rmMap.insert(current, traits::RNA());
                break;
              case roundTowardPositive:
                d_rmMap.insert(current, traits::RTP());
                break;
              case roundTowardNegative:
                d_rmMap.insert(current, traits::RTN());
                break;
              case roundTowardZero:
                d_rmMap.insert(current, traits::RTZ());
                break;
              default: Unreachable() << "Unknown rounding mode"; break;
            }
          }
          else
          {
            /******** Variables ********/
            rm tmp(nm->mkNode(kind::ROUNDINGMODE_BITBLAST, current));
            d_rmMap.insert(current, tmp);
            d_additionalAssertions.push_back(tmp.valid());
          }
        }
        else
        {
          Unreachable() << "Unknown kind of type RoundingMode";
        }
      }
      // Returns a rounding-mode type so don't alter the return value
    }
    else if (t.isFloatingPoint())
    {
      fpMap::const_iterator i(d_fpMap.find(current));

      if (i == d_fpMap.end())
      {
        if (Theory::isLeafOf(current, THEORY_FP))
        {
          if (current.getKind() == kind::CONST_FLOATINGPOINT)
          {
            /******** Constants ********/
            d_fpMap.insert(current,
                           symfpu::unpackedFloat<traits>(
                               current.getConst<FloatingPoint>().getLiteral()));
          }
          else
          {
            /******** Variables ********/
            d_fpMap.insert(current, buildComponents(current));
          }
        }
        else
        {
          switch (current.getKind())
          {
            case kind::CONST_FLOATINGPOINT:
            case kind::VARIABLE:
            case kind::BOUND_VARIABLE:
            case kind::SKOLEM:
              Unreachable() << "Kind should have been handled as a leaf.";
              break;

            /******** Operations ********/
            case kind::FLOATINGPOINT_ABS:
            case kind::FLOATINGPOINT_NEG:
            {
              fpMap::const_iterator arg1(d_fpMap.find(current[0]));

              if (arg1 == d_fpMap.end())
              {
                workStack.push_back(current);
                workStack.push_back(current[0]);
                continue;  // i.e. recurse!
              }

              switch (current.getKind())
              {
                case kind::FLOATINGPOINT_ABS:
                  d_fpMap.insert(current,
                                 symfpu::absolute<traits>(
                                     fpt(current.getType()), (*arg1).second));
                  break;
                case kind::FLOATINGPOINT_NEG:
                  d_fpMap.insert(current,
                                 symfpu::negate<traits>(fpt(current.getType()),
                                                        (*arg1).second));
                  break;
                default:
                  Unreachable() << "Unknown unary floating-point function";
                  break;
              }
            }
            break;

            case kind::FLOATINGPOINT_SQRT:
            case kind::FLOATINGPOINT_RTI:
            {
              rmMap::const_iterator mode(d_rmMap.find(current[0]));
              fpMap::const_iterator arg1(d_fpMap.find(current[1]));
              bool recurseNeeded =
                  (mode == d_rmMap.end()) || (arg1 == d_fpMap.end());

              if (recurseNeeded)
              {
                workStack.push_back(current);
                if (mode == d_rmMap.end())
                {
                  workStack.push_back(current[0]);
                }
                if (arg1 == d_fpMap.end())
                {
                  workStack.push_back(current[1]);
                }
                continue;  // i.e. recurse!
              }

              switch (current.getKind())
              {
                case kind::FLOATINGPOINT_SQRT:
                  d_fpMap.insert(current,
                                 symfpu::sqrt<traits>(fpt(current.getType()),
                                                      (*mode).second,
                                                      (*arg1).second));
                  break;
                case kind::FLOATINGPOINT_RTI:
                  d_fpMap.insert(
                      current,
                      symfpu::roundToIntegral<traits>(fpt(current.getType()),
                                                      (*mode).second,
                                                      (*arg1).second));
                  break;
                default:
                  Unreachable()
                      << "Unknown unary rounded floating-point function";
                  break;
              }
            }
            break;

            case kind::FLOATINGPOINT_REM:
            {
              fpMap::const_iterator arg1(d_fpMap.find(current[0]));
              fpMap::const_iterator arg2(d_fpMap.find(current[1]));
              bool recurseNeeded =
                  (arg1 == d_fpMap.end()) || (arg2 == d_fpMap.end());

              if (recurseNeeded)
              {
                workStack.push_back(current);
                if (arg1 == d_fpMap.end())
                {
                  workStack.push_back(current[0]);
                }
                if (arg2 == d_fpMap.end())
                {
                  workStack.push_back(current[1]);
                }
                continue;  // i.e. recurse!
              }

              d_fpMap.insert(
                  current,
                  symfpu::remainder<traits>(
                      fpt(current.getType()), (*arg1).second, (*arg2).second));
            }
            break;

            case kind::FLOATINGPOINT_MIN_TOTAL:
            case kind::FLOATINGPOINT_MAX_TOTAL:
            {
              fpMap::const_iterator arg1(d_fpMap.find(current[0]));
              fpMap::const_iterator arg2(d_fpMap.find(current[1]));
              // current[2] is a bit-vector so we do not need to recurse down it

              bool recurseNeeded =
                  (arg1 == d_fpMap.end()) || (arg2 == d_fpMap.end());

              if (recurseNeeded)
              {
                workStack.push_back(current);
                if (arg1 == d_fpMap.end())
                {
                  workStack.push_back(current[0]);
                }
                if (arg2 == d_fpMap.end())
                {
                  workStack.push_back(current[1]);
                }
                continue;  // i.e. recurse!
              }

              switch (current.getKind())
              {
                case kind::FLOATINGPOINT_MAX_TOTAL:
                  d_fpMap.insert(current,
                                 symfpu::max<traits>(fpt(current.getType()),
                                                     (*arg1).second,
                                                     (*arg2).second,
                                                     prop(current[2])));
                  break;

                case kind::FLOATINGPOINT_MIN_TOTAL:
                  d_fpMap.insert(current,
                                 symfpu::min<traits>(fpt(current.getType()),
                                                     (*arg1).second,
                                                     (*arg2).second,
                                                     prop(current[2])));
                  break;

                default:
                  Unreachable()
                      << "Unknown binary floating-point partial function";
                  break;
              }
            }
            break;

            case kind::FLOATINGPOINT_PLUS:
            case kind::FLOATINGPOINT_SUB:
            case kind::FLOATINGPOINT_MULT:
            case kind::FLOATINGPOINT_DIV:
            {
              rmMap::const_iterator mode(d_rmMap.find(current[0]));
              fpMap::const_iterator arg1(d_fpMap.find(current[1]));
              fpMap::const_iterator arg2(d_fpMap.find(current[2]));
              bool recurseNeeded = (mode == d_rmMap.end())
                                   || (arg1 == d_fpMap.end())
                                   || (arg2 == d_fpMap.end());

              if (recurseNeeded)
              {
                workStack.push_back(current);
                if (mode == d_rmMap.end())
                {
                  workStack.push_back(current[0]);
                }
                if (arg1 == d_fpMap.end())
                {
                  workStack.push_back(current[1]);
                }
                if (arg2 == d_fpMap.end())
                {
                  workStack.push_back(current[2]);
                }
                continue;  // i.e. recurse!
              }

              switch (current.getKind())
              {
                case kind::FLOATINGPOINT_PLUS:
                  d_fpMap.insert(current,
                                 symfpu::add<traits>(fpt(current.getType()),
                                                     (*mode).second,
                                                     (*arg1).second,
                                                     (*arg2).second,
                                                     prop(true)));
                  break;

                case kind::FLOATINGPOINT_SUB:
                  // Should have been removed by the rewriter
                  Unreachable()
                      << "Floating-point subtraction should be removed by the "
                         "rewriter.";
                  break;

                case kind::FLOATINGPOINT_MULT:
                  d_fpMap.insert(
                      current,
                      symfpu::multiply<traits>(fpt(current.getType()),
                                               (*mode).second,
                                               (*arg1).second,
                                               (*arg2).second));
                  break;
                case kind::FLOATINGPOINT_DIV:
                  d_fpMap.insert(current,
                                 symfpu::divide<traits>(fpt(current.getType()),
                                                        (*mode).second,
                                                        (*arg1).second,
                                                        (*arg2).second));
                  break;
                case kind::FLOATINGPOINT_REM:
                  /*
                  d_fpMap.insert(current,
                  symfpu::remainder<traits>(fpt(current.getType()),
                                                             (*mode).second,
                                                             (*arg1).second,
                                                             (*arg2).second));
                  */
                  Unimplemented()
                      << "Remainder with rounding mode not yet supported by "
                         "SMT-LIB";
                  break;

                default:
                  Unreachable()
                      << "Unknown binary rounded floating-point function";
                  break;
              }
            }
            break;

            case kind::FLOATINGPOINT_FMA:
            {
              rmMap::const_iterator mode(d_rmMap.find(current[0]));
              fpMap::const_iterator arg1(d_fpMap.find(current[1]));
              fpMap::const_iterator arg2(d_fpMap.find(current[2]));
              fpMap::const_iterator arg3(d_fpMap.find(current[3]));
              bool recurseNeeded =
                  (mode == d_rmMap.end()) || (arg1 == d_fpMap.end())
                  || (arg2 == d_fpMap.end() || (arg3 == d_fpMap.end()));

              if (recurseNeeded)
              {
                workStack.push_back(current);
                if (mode == d_rmMap.end())
                {
                  workStack.push_back(current[0]);
                }
                if (arg1 == d_fpMap.end())
                {
                  workStack.push_back(current[1]);
                }
                if (arg2 == d_fpMap.end())
                {
                  workStack.push_back(current[2]);
                }
                if (arg3 == d_fpMap.end())
                {
                  workStack.push_back(current[3]);
                }
                continue;  // i.e. recurse!
              }

              d_fpMap.insert(current,
                             symfpu::fma<traits>(fpt(current.getType()),
                                                 (*mode).second,
                                                 (*arg1).second,
                                                 (*arg2).second,
                                                 (*arg3).second));
            }
            break;

            /******** Conversions ********/
            case kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT:
            {
              rmMap::const_iterator mode(d_rmMap.find(current[0]));
              fpMap::const_iterator arg1(d_fpMap.find(current[1]));
              bool recurseNeeded =
                  (mode == d_rmMap.end()) || (arg1 == d_fpMap.end());

              if (recurseNeeded)
              {
                workStack.push_back(current);
                if (mode == d_rmMap.end())
                {
                  workStack.push_back(current[0]);
                }
                if (arg1 == d_fpMap.end())
                {
                  workStack.push_back(current[1]);
                }
                continue;  // i.e. recurse!
              }

              d_fpMap.insert(
                  current,
                  symfpu::convertFloatToFloat<traits>(fpt(current[1].getType()),
                                                      fpt(current.getType()),
                                                      (*mode).second,
                                                      (*arg1).second));
            }
            break;

            case kind::FLOATINGPOINT_FP:
            {
              Node IEEEBV(nm->mkNode(
                  kind::BITVECTOR_CONCAT, current[0], current[1], current[2]));
              d_fpMap.insert(
                  current,
                  symfpu::unpack<traits>(fpt(current.getType()), IEEEBV));
            }
            break;

            case kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR:
              d_fpMap.insert(current,
                             symfpu::unpack<traits>(fpt(current.getType()),
                                                    ubv(current[0])));
              break;

            case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR:
            case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR:
            {
              rmMap::const_iterator mode(d_rmMap.find(current[0]));
              bool recurseNeeded = (mode == d_rmMap.end());

              if (recurseNeeded)
              {
                workStack.push_back(current);
                if (mode == d_rmMap.end())
                {
                  workStack.push_back(current[0]);
                }
                continue;  // i.e. recurse!
              }

              switch (current.getKind())
              {
                case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR:
                  d_fpMap.insert(
                      current,
                      symfpu::convertSBVToFloat<traits>(fpt(current.getType()),
                                                        (*mode).second,
                                                        sbv(current[1])));
                  break;

                case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR:
                  d_fpMap.insert(
                      current,
                      symfpu::convertUBVToFloat<traits>(fpt(current.getType()),
                                                        (*mode).second,
                                                        ubv(current[1])));
                  break;

                default:
                  Unreachable() << "Unknown converstion from bit-vector to "
                                   "floating-point";
                  break;
              }
            }
            break;

            case kind::FLOATINGPOINT_TO_FP_REAL:
            {
              d_fpMap.insert(current, buildComponents(current));
              // Rely on the real theory and theory combination
              // to handle the value
            }
            break;

            case kind::FLOATINGPOINT_TO_FP_GENERIC:
              Unreachable() << "Generic to_fp not removed";
              break;

            default:
              Unreachable() << "Unknown kind of type FloatingPoint";
              break;
          }
        }
      }
      // Returns a floating-point type so don't alter the return value
    }
    else if (t.isBoolean())
    {
      boolMap::const_iterator i(d_boolMap.find(current));

      if (i == d_boolMap.end())
      {
        switch (current.getKind())
        {
          /******** Comparisons ********/
          case kind::EQUAL:
          {
            TypeNode childType(current[0].getType());

            if (childType.isFloatingPoint())
            {
              fpMap::const_iterator arg1(d_fpMap.find(current[0]));
              fpMap::const_iterator arg2(d_fpMap.find(current[1]));
              bool recurseNeeded =
                  (arg1 == d_fpMap.end()) || (arg2 == d_fpMap.end());

              if (recurseNeeded)
              {
                workStack.push_back(current);
                if (arg1 == d_fpMap.end())
                {
                  workStack.push_back(current[0]);
                }
                if (arg2 == d_fpMap.end())
                {
                  workStack.push_back(current[1]);
                }
                continue;  // i.e. recurse!
              }

              d_boolMap.insert(
                  current,
                  symfpu::smtlibEqual<traits>(
                      fpt(childType), (*arg1).second, (*arg2).second));
            }
            else if (childType.isRoundingMode())
            {
              rmMap::const_iterator arg1(d_rmMap.find(current[0]));
              rmMap::const_iterator arg2(d_rmMap.find(current[1]));
              bool recurseNeeded =
                  (arg1 == d_rmMap.end()) || (arg2 == d_rmMap.end());

              if (recurseNeeded)
              {
                workStack.push_back(current);
                if (arg1 == d_rmMap.end())
                {
                  workStack.push_back(current[0]);
                }
                if (arg2 == d_rmMap.end())
                {
                  workStack.push_back(current[1]);
                }
                continue;  // i.e. recurse!
              }

              d_boolMap.insert(current, (*arg1).second == (*arg2).second);
            }
            else
            {
              CVC4_FPCONV_PASSTHROUGH;
              return result;
            }
          }
          break;

          case kind::FLOATINGPOINT_LEQ:
          case kind::FLOATINGPOINT_LT:
          {
            TypeNode childType(current[0].getType());

            fpMap::const_iterator arg1(d_fpMap.find(current[0]));
            fpMap::const_iterator arg2(d_fpMap.find(current[1]));
            bool recurseNeeded =
                (arg1 == d_fpMap.end()) || (arg2 == d_fpMap.end());

            if (recurseNeeded)
            {
              workStack.push_back(current);
              if (arg1 == d_fpMap.end())
              {
                workStack.push_back(current[0]);
              }
              if (arg2 == d_fpMap.end())
              {
                workStack.push_back(current[1]);
              }
              continue;  // i.e. recurse!
            }

            switch (current.getKind())
            {
              case kind::FLOATINGPOINT_LEQ:
                d_boolMap.insert(
                    current,
                    symfpu::lessThanOrEqual<traits>(
                        fpt(childType), (*arg1).second, (*arg2).second));
                break;

              case kind::FLOATINGPOINT_LT:
                d_boolMap.insert(
                    current,
                    symfpu::lessThan<traits>(
                        fpt(childType), (*arg1).second, (*arg2).second));
                break;

              default:
                Unreachable() << "Unknown binary floating-point relation";
                break;
            }
          }
          break;

          case kind::FLOATINGPOINT_ISN:
          case kind::FLOATINGPOINT_ISSN:
          case kind::FLOATINGPOINT_ISZ:
          case kind::FLOATINGPOINT_ISINF:
          case kind::FLOATINGPOINT_ISNAN:
          case kind::FLOATINGPOINT_ISNEG:
          case kind::FLOATINGPOINT_ISPOS:
          {
            TypeNode childType(current[0].getType());
            fpMap::const_iterator arg1(d_fpMap.find(current[0]));

            if (arg1 == d_fpMap.end())
            {
              workStack.push_back(current);
              workStack.push_back(current[0]);
              continue;  // i.e. recurse!
            }

            switch (current.getKind())
            {
              case kind::FLOATINGPOINT_ISN:
                d_boolMap.insert(
                    current,
                    symfpu::isNormal<traits>(fpt(childType), (*arg1).second));
                break;

              case kind::FLOATINGPOINT_ISSN:
                d_boolMap.insert(current,
                                 symfpu::isSubnormal<traits>(fpt(childType),
                                                             (*arg1).second));
                break;

              case kind::FLOATINGPOINT_ISZ:
                d_boolMap.insert(
                    current,
                    symfpu::isZero<traits>(fpt(childType), (*arg1).second));
                break;

              case kind::FLOATINGPOINT_ISINF:
                d_boolMap.insert(
                    current,
                    symfpu::isInfinite<traits>(fpt(childType), (*arg1).second));
                break;

              case kind::FLOATINGPOINT_ISNAN:
                d_boolMap.insert(
                    current,
                    symfpu::isNaN<traits>(fpt(childType), (*arg1).second));
                break;

              case kind::FLOATINGPOINT_ISPOS:
                d_boolMap.insert(
                    current,
                    symfpu::isPositive<traits>(fpt(childType), (*arg1).second));
                break;

              case kind::FLOATINGPOINT_ISNEG:
                d_boolMap.insert(
                    current,
                    symfpu::isNegative<traits>(fpt(childType), (*arg1).second));
                break;

              default:
                Unreachable() << "Unknown unary floating-point relation";
                break;
            }
          }
          break;

          case kind::FLOATINGPOINT_EQ:
          case kind::FLOATINGPOINT_GEQ:
          case kind::FLOATINGPOINT_GT:
            Unreachable() << "Kind should have been removed by rewriter.";
            break;

          // Components will be registered as they are owned by
          // the floating-point theory.  No action is required.
          case kind::FLOATINGPOINT_COMPONENT_NAN:
          case kind::FLOATINGPOINT_COMPONENT_INF:
          case kind::FLOATINGPOINT_COMPONENT_ZERO:
          case kind::FLOATINGPOINT_COMPONENT_SIGN:
          /* Fall through... */

          default:
            CVC4_FPCONV_PASSTHROUGH;
            return result;
            break;
        }

        i = d_boolMap.find(current);
      }

      result = (*i).second;
    }
    else if (t.isBitVector())
    {
      switch (current.getKind())
      {
        /******** Conversions ********/
        case kind::FLOATINGPOINT_TO_UBV_TOTAL:
        {
          TypeNode childType(current[1].getType());
          ubvMap::const_iterator i(d_ubvMap.find(current));

          if (i == d_ubvMap.end())
          {
            rmMap::const_iterator mode(d_rmMap.find(current[0]));
            fpMap::const_iterator arg1(d_fpMap.find(current[1]));
            bool recurseNeeded =
                (mode == d_rmMap.end()) || (arg1 == d_fpMap.end());

            if (recurseNeeded)
            {
              workStack.push_back(current);
              if (mode == d_rmMap.end())
              {
                workStack.push_back(current[0]);
              }
              if (arg1 == d_fpMap.end())
              {
                workStack.push_back(current[1]);
              }
              continue;  // i.e. recurse!
            }

            FloatingPointToUBVTotal info =
                current.getOperator().getConst<FloatingPointToUBVTotal>();

            d_ubvMap.insert(current,
                            symfpu::convertFloatToUBV<traits>(fpt(childType),
                                                              (*mode).second,
                                                              (*arg1).second,
                                                              info.bvs,
                                                              ubv(current[2])));
            i = d_ubvMap.find(current);
          }

          result = (*i).second;
        }
        break;

        case kind::FLOATINGPOINT_TO_SBV_TOTAL:
        {
          TypeNode childType(current[1].getType());
          sbvMap::const_iterator i(d_sbvMap.find(current));

          if (i == d_sbvMap.end())
          {
            rmMap::const_iterator mode(d_rmMap.find(current[0]));
            fpMap::const_iterator arg1(d_fpMap.find(current[1]));
            bool recurseNeeded =
                (mode == d_rmMap.end()) || (arg1 == d_fpMap.end());

            if (recurseNeeded)
            {
              workStack.push_back(current);
              if (mode == d_rmMap.end())
              {
                workStack.push_back(current[0]);
              }
              if (arg1 == d_fpMap.end())
              {
                workStack.push_back(current[1]);
              }
              continue;  // i.e. recurse!
            }

            FloatingPointToSBVTotal info =
                current.getOperator().getConst<FloatingPointToSBVTotal>();

            d_sbvMap.insert(current,
                            symfpu::convertFloatToSBV<traits>(fpt(childType),
                                                              (*mode).second,
                                                              (*arg1).second,
                                                              info.bvs,
                                                              sbv(current[2])));

            i = d_sbvMap.find(current);
          }

          result = (*i).second;
        }
        break;

        case kind::FLOATINGPOINT_TO_UBV:
          Unreachable()
              << "Partially defined fp.to_ubv should have been removed by "
                 "expandDefinition";
          break;

        case kind::FLOATINGPOINT_TO_SBV:
          Unreachable()
              << "Partially defined fp.to_sbv should have been removed by "
                 "expandDefinition";
          break;

        // Again, no action is needed
        case kind::FLOATINGPOINT_COMPONENT_EXPONENT:
        case kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND:
        case kind::ROUNDINGMODE_BITBLAST:
        /* Fall through ... */

        default: CVC4_FPCONV_PASSTHROUGH; break;
      }
    }
    else if (t.isReal())
    {
      switch (current.getKind())
      {
        /******** Conversions ********/
        case kind::FLOATINGPOINT_TO_REAL_TOTAL:
        {
          // We need to recurse so that any variables that are only
          // used under this will have components created
          // (via auxiliary constraints)

          TypeNode childType(current[0].getType());
          fpMap::const_iterator arg1(d_fpMap.find(current[0]));

          if (arg1 == d_fpMap.end())
          {
            workStack.push_back(current);
            workStack.push_back(current[0]);
            continue;  // i.e. recurse!
          }

          // However we don't need to do anything explicitly with
          // this as it will be treated as an uninterpreted function
          // by the real theory and we don't need to bit-blast the
          // float expression unless we need to say something about
          // its value.
        }

        break;

        case kind::FLOATINGPOINT_TO_REAL:
          Unreachable()
              << "Partially defined fp.to_real should have been removed by "
                 "expandDefinition";
          break;

        default: CVC4_FPCONV_PASSTHROUGH; break;
      }
    }
    else
    {
      CVC4_FPCONV_PASSTHROUGH;
    }
  }

  return result;
#else
  Unimplemented() << "Conversion is dependent on SymFPU";
#endif
}

#undef CVC4_FPCONV_PASSTHROUGH

Node FpConverter::getValue(Valuation &val, TNode var)
{
  Assert(Theory::isLeafOf(var, THEORY_FP));

#ifdef CVC4_USE_SYMFPU
  TypeNode t(var.getType());

  if (t.isRoundingMode())
  {
    rmMap::const_iterator i(d_rmMap.find(var));

    if (i == d_rmMap.end())
    {
      Unreachable() << "Asking for the value of an unregistered expression";
    }
    else
    {
      Node value = rmToNode((*i).second);
      return value;
    }
  }
  else if (t.isFloatingPoint())
  {
    fpMap::const_iterator i(d_fpMap.find(var));

    if (i == d_fpMap.end())
    {
      Unreachable() << "Asking for the value of an unregistered expression";
    }
    else
    {
      Node value = ufToNode(fpt(t), (*i).second);
      return value;
    }
  }
  else
  {
    Unreachable()
        << "Asking for the value of a type that is not managed by the "
           "floating-point theory";
  }

  Unreachable() << "Unable to find value";

#else
  Unimplemented() << "Conversion is dependent on SymFPU";
#endif
}

}  // namespace fp
}  // namespace theory
}  // namespace CVC4
