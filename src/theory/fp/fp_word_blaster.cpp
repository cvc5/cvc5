/******************************************************************************
 * Top contributors (to current version):
 *   Martin Brain, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Conversion of floating-point operations to bit-vectors using symfpu.
 */

#include "theory/fp/fp_word_blaster.h"

#include <vector>

#include "base/check.h"
#include "expr/node_builder.h"
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
#include "theory/theory.h"  // theory.h Only needed for the leaf test
#include "util/floatingpoint.h"
#include "util/floatingpoint_literal_symfpu.h"

namespace symfpu {
using namespace cvc5::internal::theory::fp::symfpuSymbolic;

#define CVC5_SYM_ITE_DFN(T)                                                  \
  template <>                                                                \
  struct ite<symbolicProposition, T>                                         \
  {                                                                          \
    static const T iteOp(const symbolicProposition& _cond,                   \
                         const T& _l,                                        \
                         const T& _r)                                        \
    {                                                                        \
      cvc5::internal::NodeManager* nm =                                      \
          cvc5::internal::NodeManager::currentNM();                          \
                                                                             \
      cvc5::internal::Node cond = _cond;                                     \
      cvc5::internal::Node l = _l;                                           \
      cvc5::internal::Node r = _r;                                           \
                                                                             \
      /* Handle some common symfpu idioms */                                 \
      if (cond.isConst())                                                    \
      {                                                                      \
        return (cond == nm->mkConst(cvc5::internal::BitVector(1U, 1U))) ? l  \
                                                                        : r; \
      }                                                                      \
      else                                                                   \
      {                                                                      \
        if (l.getKind() == cvc5::internal::kind::BITVECTOR_ITE)              \
        {                                                                    \
          if (l[1] == r)                                                     \
          {                                                                  \
            return nm->mkNode(                                               \
                cvc5::internal::kind::BITVECTOR_ITE,                         \
                nm->mkNode(                                                  \
                    cvc5::internal::kind::BITVECTOR_AND,                     \
                    cond,                                                    \
                    nm->mkNode(cvc5::internal::kind::BITVECTOR_NOT, l[0])),  \
                l[2],                                                        \
                r);                                                          \
          }                                                                  \
          else if (l[2] == r)                                                \
          {                                                                  \
            return nm->mkNode(                                               \
                cvc5::internal::kind::BITVECTOR_ITE,                         \
                nm->mkNode(cvc5::internal::kind::BITVECTOR_AND, cond, l[0]), \
                l[1],                                                        \
                r);                                                          \
          }                                                                  \
        }                                                                    \
        else if (r.getKind() == cvc5::internal::kind::BITVECTOR_ITE)         \
        {                                                                    \
          if (r[1] == l)                                                     \
          {                                                                  \
            return nm->mkNode(                                               \
                cvc5::internal::kind::BITVECTOR_ITE,                         \
                nm->mkNode(                                                  \
                    cvc5::internal::kind::BITVECTOR_AND,                     \
                    nm->mkNode(cvc5::internal::kind::BITVECTOR_NOT, cond),   \
                    nm->mkNode(cvc5::internal::kind::BITVECTOR_NOT, r[0])),  \
                r[2],                                                        \
                l);                                                          \
          }                                                                  \
          else if (r[2] == l)                                                \
          {                                                                  \
            return nm->mkNode(                                               \
                cvc5::internal::kind::BITVECTOR_ITE,                         \
                nm->mkNode(                                                  \
                    cvc5::internal::kind::BITVECTOR_AND,                     \
                    nm->mkNode(cvc5::internal::kind::BITVECTOR_NOT, cond),   \
                    r[0]),                                                   \
                r[1],                                                        \
                l);                                                          \
          }                                                                  \
        }                                                                    \
      }                                                                      \
      return T(nm->mkNode(cvc5::internal::kind::BITVECTOR_ITE, cond, l, r)); \
    }                                                                        \
  }

// Can (unsurprisingly) only ITE things which contain Nodes
CVC5_SYM_ITE_DFN(traits::rm);
CVC5_SYM_ITE_DFN(traits::prop);
CVC5_SYM_ITE_DFN(traits::sbv);
CVC5_SYM_ITE_DFN(traits::ubv);

#undef CVC5_SYM_ITE_DFN

template <>
traits::ubv orderEncode<traits, traits::ubv>(const traits::ubv& b)
{
  return orderEncodeBitwise<traits, traits::ubv>(b);
}

template <>
stickyRightShiftResult<traits> stickyRightShift(const traits::ubv& input,
                                                const traits::ubv& shiftAmount)
{
  return stickyRightShiftBitwise<traits>(input, shiftAmount);
}

template <>
void probabilityAnnotation<traits, traits::prop>(const traits::prop& p,
                                                 const probability& pr)
{
  // For now, do nothing...
  return;
}
};  // namespace symfpu

namespace cvc5::internal {
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
  Assert(b);
  return;
}
void traits::postcondition(const bool b)
{
  Assert(b);
  return;
}
void traits::invariant(const bool b)
{
  Assert(b);
  return;
}

void traits::precondition(const prop& p) { return; }
void traits::postcondition(const prop& p) { return; }
void traits::invariant(const prop& p) { return; }
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
  Assert(checkNodeType(*this));
}  // Only used within this header so could be friend'd
symbolicProposition::symbolicProposition(bool v)
    : nodeWrapper(
        NodeManager::currentNM()->mkConst(BitVector(1U, (v ? 1U : 0U))))
{
  Assert(checkNodeType(*this));
}

symbolicProposition::symbolicProposition(const symbolicProposition& old)
    : nodeWrapper(old)
{
  Assert(checkNodeType(*this));
}

symbolicProposition symbolicProposition::operator!(void) const
{
  return symbolicProposition(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_NOT, *this));
}

symbolicProposition symbolicProposition::operator&&(
    const symbolicProposition& op) const
{
  return symbolicProposition(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_AND, *this, op));
}

symbolicProposition symbolicProposition::operator||(
    const symbolicProposition& op) const
{
  return symbolicProposition(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_OR, *this, op));
}

symbolicProposition symbolicProposition::operator==(
    const symbolicProposition& op) const
{
  return symbolicProposition(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_COMP, *this, op));
}

symbolicProposition symbolicProposition::operator^(
    const symbolicProposition& op) const
{
  return symbolicProposition(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_XOR, *this, op));
}

bool symbolicRoundingMode::checkNodeType(const TNode n)
{
  return n.getType(false).isBitVector(SYMFPU_NUMBER_OF_ROUNDING_MODES);
}

symbolicRoundingMode::symbolicRoundingMode(const Node n) : nodeWrapper(n)
{
  Assert(checkNodeType(*this));
}

symbolicRoundingMode::symbolicRoundingMode(const unsigned v)
    : nodeWrapper(NodeManager::currentNM()->mkConst(
        BitVector(SYMFPU_NUMBER_OF_ROUNDING_MODES, v)))
{
  Assert((v & (v - 1)) == 0 && v != 0);  // Exactly one bit set
  Assert(checkNodeType(*this));
}

symbolicRoundingMode::symbolicRoundingMode(const symbolicRoundingMode& old)
    : nodeWrapper(old)
{
  Assert(checkNodeType(*this));
}

symbolicProposition symbolicRoundingMode::valid(void) const
{
  NodeManager* nm = NodeManager::currentNM();
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
    const symbolicRoundingMode& op) const
{
  return symbolicProposition(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_COMP, *this, op));
}

template <bool isSigned>
Node symbolicBitVector<isSigned>::boolNodeToBV(Node node) const
{
  Assert(node.getType().isBoolean());
  NodeManager* nm = NodeManager::currentNM();
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
  NodeManager* nm = NodeManager::currentNM();
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
  Assert(checkNodeType(*this));
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
  Assert(checkNodeType(*this));
}
template <bool isSigned>
symbolicBitVector<isSigned>::symbolicBitVector(const symbolicProposition& p)
    : nodeWrapper(fromProposition(p))
{
}
template <bool isSigned>
symbolicBitVector<isSigned>::symbolicBitVector(
    const symbolicBitVector<isSigned>& old)
    : nodeWrapper(old)
{
  Assert(checkNodeType(*this));
}
template <bool isSigned>
symbolicBitVector<isSigned>::symbolicBitVector(const BitVector& old)
    : nodeWrapper(NodeManager::currentNM()->mkConst(old))
{
  Assert(checkNodeType(*this));
}

template <bool isSigned>
bwt symbolicBitVector<isSigned>::getWidth(void) const
{
  return this->getType(false).getBitVectorSize();
}

/*** Constant creation and test ***/
template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::one(const bwt& w)
{
  return symbolicBitVector<isSigned>(w, 1);
}
template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::zero(const bwt& w)
{
  return symbolicBitVector<isSigned>(w, 0);
}
template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::allOnes(const bwt& w)
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
symbolicBitVector<true> symbolicBitVector<true>::maxValue(const bwt& w)
{
  symbolicBitVector<true> leadingZero(symbolicBitVector<true>::zero(1));
  symbolicBitVector<true> base(symbolicBitVector<true>::allOnes(w - 1));

  return symbolicBitVector<true>(
      cvc5::internal::NodeManager::currentNM()->mkNode(
          cvc5::internal::kind::BITVECTOR_CONCAT, leadingZero, base));
}

template <>
symbolicBitVector<false> symbolicBitVector<false>::maxValue(const bwt& w)
{
  return symbolicBitVector<false>::allOnes(w);
}

template <>
symbolicBitVector<true> symbolicBitVector<true>::minValue(const bwt& w)
{
  symbolicBitVector<true> leadingOne(symbolicBitVector<true>::one(1));
  symbolicBitVector<true> base(symbolicBitVector<true>::zero(w - 1));

  return symbolicBitVector<true>(
      cvc5::internal::NodeManager::currentNM()->mkNode(
          cvc5::internal::kind::BITVECTOR_CONCAT, leadingOne, base));
}

template <>
symbolicBitVector<false> symbolicBitVector<false>::minValue(const bwt& w)
{
  return symbolicBitVector<false>::zero(w);
}

/*** Operators ***/
template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator<<(
    const symbolicBitVector<isSigned>& op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_SHL, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator>>(
    const symbolicBitVector<isSigned>& op) const
{
  return symbolicBitVector<isSigned>(NodeManager::currentNM()->mkNode(
      (isSigned) ? kind::BITVECTOR_ASHR : kind::BITVECTOR_LSHR, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator|(
    const symbolicBitVector<isSigned>& op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_OR, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator&(
    const symbolicBitVector<isSigned>& op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_AND, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator+(
    const symbolicBitVector<isSigned>& op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_ADD, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator-(
    const symbolicBitVector<isSigned>& op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_SUB, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator*(
    const symbolicBitVector<isSigned>& op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_MULT, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator/(
    const symbolicBitVector<isSigned>& op) const
{
  return symbolicBitVector<isSigned>(NodeManager::currentNM()->mkNode(
      (isSigned) ? kind::BITVECTOR_SDIV : kind::BITVECTOR_UDIV, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator%(
    const symbolicBitVector<isSigned>& op) const
{
  return symbolicBitVector<isSigned>(NodeManager::currentNM()->mkNode(
      (isSigned) ? kind::BITVECTOR_SREM : kind::BITVECTOR_UREM, *this, op));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator-(void) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_NEG, *this));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::operator~(void) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_NOT, *this));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::increment() const
{
  return symbolicBitVector<isSigned>(NodeManager::currentNM()->mkNode(
      kind::BITVECTOR_ADD, *this, one(this->getWidth())));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::decrement() const
{
  return symbolicBitVector<isSigned>(NodeManager::currentNM()->mkNode(
      kind::BITVECTOR_SUB, *this, one(this->getWidth())));
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::signExtendRightShift(
    const symbolicBitVector<isSigned>& op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_ASHR, *this, op));
}

/*** Modular operations ***/
// No overflow checking so these are the same as other operations
template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::modularLeftShift(
    const symbolicBitVector<isSigned>& op) const
{
  return *this << op;
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::modularRightShift(
    const symbolicBitVector<isSigned>& op) const
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
    const symbolicBitVector<isSigned>& op) const
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
    const symbolicBitVector<isSigned>& op) const
{
  return symbolicProposition(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_COMP, *this, op));
}

template <bool isSigned>
symbolicProposition symbolicBitVector<isSigned>::operator<=(
    const symbolicBitVector<isSigned>& op) const
{
  // Consider adding kind::BITVECTOR_SLEBV and BITVECTOR_ULEBV
  return (*this < op) || (*this == op);
}

template <bool isSigned>
symbolicProposition symbolicBitVector<isSigned>::operator>=(
    const symbolicBitVector<isSigned>& op) const
{
  return (*this > op) || (*this == op);
}

template <bool isSigned>
symbolicProposition symbolicBitVector<isSigned>::operator<(
    const symbolicBitVector<isSigned>& op) const
{
  return symbolicProposition(NodeManager::currentNM()->mkNode(
      (isSigned) ? kind::BITVECTOR_SLTBV : kind::BITVECTOR_ULTBV, *this, op));
}

template <bool isSigned>
symbolicProposition symbolicBitVector<isSigned>::operator>(
    const symbolicBitVector<isSigned>& op) const
{
  return symbolicProposition(NodeManager::currentNM()->mkNode(
      (isSigned) ? kind::BITVECTOR_SLTBV : kind::BITVECTOR_ULTBV, op, *this));
}

/*** Type conversion ***/
// cvc5 nodes make no distinction between signed and unsigned, thus ...
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
  NodeBuilder construct(kind::BITVECTOR_SIGN_EXTEND);
  construct << NodeManager::currentNM()->mkConst<BitVectorSignExtend>(
      BitVectorSignExtend(extension))
            << *this;

  return symbolicBitVector<true>(construct);
}

template <>
symbolicBitVector<false> symbolicBitVector<false>::extend(bwt extension) const
{
  NodeBuilder construct(kind::BITVECTOR_ZERO_EXTEND);
  construct << NodeManager::currentNM()->mkConst<BitVectorZeroExtend>(
      BitVectorZeroExtend(extension))
            << *this;

  return symbolicBitVector<false>(construct);
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::contract(
    bwt reduction) const
{
  Assert(this->getWidth() > reduction);

  NodeBuilder construct(kind::BITVECTOR_EXTRACT);
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
    const symbolicBitVector<isSigned>& op) const
{
  Assert(this->getWidth() <= op.getWidth());
  return this->extend(op.getWidth() - this->getWidth());
}

template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::append(
    const symbolicBitVector<isSigned>& op) const
{
  return symbolicBitVector<isSigned>(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_CONCAT, *this, op));
}

// Inclusive of end points, thus if the same, extracts just one bit
template <bool isSigned>
symbolicBitVector<isSigned> symbolicBitVector<isSigned>::extract(
    bwt upper, bwt lower) const
{
  Assert(upper >= lower);

  NodeBuilder construct(kind::BITVECTOR_EXTRACT);
  construct << NodeManager::currentNM()->mkConst<BitVectorExtract>(
      BitVectorExtract(upper, lower))
            << *this;

  return symbolicBitVector<isSigned>(construct);
}

floatingPointTypeInfo::floatingPointTypeInfo(const TypeNode type)
    : FloatingPointSize(type.getConst<FloatingPointSize>())
{
  Assert(type.isFloatingPoint());
}
floatingPointTypeInfo::floatingPointTypeInfo(unsigned exp, unsigned sig)
    : FloatingPointSize(exp, sig)
{
}
floatingPointTypeInfo::floatingPointTypeInfo(const floatingPointTypeInfo& old)
    : FloatingPointSize(old)
{
}

TypeNode floatingPointTypeInfo::getTypeNode(void) const
{
  return NodeManager::currentNM()->mkFloatingPointType(*this);
}
}  // namespace symfpuSymbolic

FpWordBlaster::FpWordBlaster(context::UserContext* user)
    : d_additionalAssertions(user),
      d_fpMap(user),
      d_rmMap(user),
      d_boolMap(user),
      d_ubvMap(user),
      d_sbvMap(user)
{
}

FpWordBlaster::~FpWordBlaster() {}

Node FpWordBlaster::ufToNode(const fpt& format, const uf& u) const
{
  NodeManager* nm = NodeManager::currentNM();

  FloatingPointSize fps(format.getTypeNode().getConst<FloatingPointSize>());

  // This is not entirely obvious but it builds a float from components
  // Particularly, if the components can be constant folded, it should
  // build a Node containing a constant FloatingPoint number

  ubv packed(symfpu::pack<traits>(format, u));
  Node value =
      nm->mkNode(nm->mkConst(FloatingPointToFPIEEEBitVector(fps)), packed);
  return value;
}

Node FpWordBlaster::rmToNode(const rm& r) const
{
  NodeManager* nm = NodeManager::currentNM();

  Node transVar = r;

  Node RNE = traits::RNE();
  Node RNA = traits::RNA();
  Node RTP = traits::RTP();
  Node RTN = traits::RTN();
  Node RTZ = traits::RTZ();

  Node value = nm->mkNode(
      kind::ITE,
      nm->mkNode(kind::EQUAL, transVar, RNE),
      nm->mkConst(RoundingMode::ROUND_NEAREST_TIES_TO_EVEN),
      nm->mkNode(
          kind::ITE,
          nm->mkNode(kind::EQUAL, transVar, RNA),
          nm->mkConst(RoundingMode::ROUND_NEAREST_TIES_TO_AWAY),
          nm->mkNode(
              kind::ITE,
              nm->mkNode(kind::EQUAL, transVar, RTP),
              nm->mkConst(RoundingMode::ROUND_TOWARD_POSITIVE),
              nm->mkNode(kind::ITE,
                         nm->mkNode(kind::EQUAL, transVar, RTN),
                         nm->mkConst(RoundingMode::ROUND_TOWARD_NEGATIVE),
                         nm->mkConst(RoundingMode::ROUND_TOWARD_ZERO)))));
  return value;
}

Node FpWordBlaster::propToNode(const prop& p) const
{
  NodeManager* nm = NodeManager::currentNM();
  Node value = nm->mkNode(
      kind::EQUAL, p, nm->mkConst(cvc5::internal::BitVector(1U, 1U)));
  return value;
}
Node FpWordBlaster::ubvToNode(const ubv& u) const { return u; }
Node FpWordBlaster::sbvToNode(const sbv& s) const { return s; }
// Creates the components constraint
FpWordBlaster::uf FpWordBlaster::buildComponents(TNode current)
{
  Assert(Theory::isLeafOf(current, THEORY_FP)
         || current.getKind() == kind::FLOATINGPOINT_TO_FP_FROM_REAL);

  NodeManager* nm = NodeManager::currentNM();
  uf tmp(nm->mkNode(kind::FLOATINGPOINT_COMPONENT_NAN, current),
         nm->mkNode(kind::FLOATINGPOINT_COMPONENT_INF, current),
         nm->mkNode(kind::FLOATINGPOINT_COMPONENT_ZERO, current),
         nm->mkNode(kind::FLOATINGPOINT_COMPONENT_SIGN, current),
         nm->mkNode(kind::FLOATINGPOINT_COMPONENT_EXPONENT, current),
         nm->mkNode(kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND, current));

  d_additionalAssertions.push_back(tmp.valid(fpt(current.getType())));

  return tmp;
}

Node FpWordBlaster::wordBlast(TNode node)
{
  std::vector<TNode> visit;
  std::unordered_map<TNode, bool> visited;
  NodeManager* nm = NodeManager::currentNM();

  visit.push_back(node);

  while (!visit.empty())
  {
    TNode cur = visit.back();
    visit.pop_back();
    TypeNode t(cur.getType());

    /* Already word-blasted, skip. */
    if ((t.isBoolean() && d_boolMap.find(cur) != d_boolMap.end())
        || (t.isRoundingMode() && d_rmMap.find(cur) != d_rmMap.end())
        || (t.isBitVector()
            && (d_sbvMap.find(cur) != d_sbvMap.end()
                || d_ubvMap.find(cur) != d_ubvMap.end()))
        || (t.isFloatingPoint() && d_fpMap.find(cur) != d_fpMap.end()))
    {
      continue;
    }

    Kind kind = cur.getKind();

    if (t.isReal() && kind != kind::FLOATINGPOINT_TO_REAL_TOTAL)
    {
      // The only nodes with Real sort in Theory FP are of kind
      // kind::FLOATINGPOINT_TO_REAL_TOTAL (kind::FLOATINGPOINT_TO_REAL is
      // rewritten to kind::FLOATINGPOINT_TO_REAL_TOTAL).
      // We don't need to do anything explicitly with them since they will be
      // treated as an uninterpreted function by the Real theory and we don't
      // need to bit-blast the float expression unless we need to say something
      // about its value.
      //
      // We still have to word blast it's arguments, though.
      //
      // All other Real expressions can be skipped.
      continue;
    }

    if (cur.isClosure())
    {
      // We ignore closures. For closures (e.g., set comprehension), we rely on
      // the reduction of the closures to handle the body.
      continue;
    }

    auto it = visited.find(cur);
    if (it == visited.end())
    {
      visited.emplace(cur, 0);
      visit.push_back(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second == false)
    {
      it->second = true;

      if (t.isRoundingMode())
      {
        /* ---- RoundingMode constants and variables -------------- */
        Assert(Theory::isLeafOf(cur, THEORY_FP));
        if (kind == kind::CONST_ROUNDINGMODE)
        {
          switch (cur.getConst<RoundingMode>())
          {
            case RoundingMode::ROUND_NEAREST_TIES_TO_EVEN:
              d_rmMap.insert(cur, traits::RNE());
              break;
            case RoundingMode::ROUND_NEAREST_TIES_TO_AWAY:
              d_rmMap.insert(cur, traits::RNA());
              break;
            case RoundingMode::ROUND_TOWARD_POSITIVE:
              d_rmMap.insert(cur, traits::RTP());
              break;
            case RoundingMode::ROUND_TOWARD_NEGATIVE:
              d_rmMap.insert(cur, traits::RTN());
              break;
            case RoundingMode::ROUND_TOWARD_ZERO:
              d_rmMap.insert(cur, traits::RTZ());
              break;
            default: Unreachable() << "Unknown rounding mode"; break;
          }
        }
        else
        {
          rm tmp(nm->mkNode(kind::ROUNDINGMODE_BITBLAST, cur));
          d_rmMap.insert(cur, tmp);
          d_additionalAssertions.push_back(tmp.valid());
        }
      }
      else if (t.isFloatingPoint())
      {
        /* ---- FloatingPoint constants and variables ------------- */
        if (Theory::isLeafOf(cur, THEORY_FP))
        {
          if (kind == kind::CONST_FLOATINGPOINT)
          {
            d_fpMap.insert(
                cur,
                symfpu::unpackedFloat<traits>(
                    cur.getConst<FloatingPoint>().getLiteral()->getSymUF()));
          }
          else
          {
            d_fpMap.insert(cur, buildComponents(cur));
          }
        }
        else
        {
          /* ---- FloatingPoint operators --------------------------- */
          Assert(kind != kind::CONST_FLOATINGPOINT);
          Assert(kind != kind::VARIABLE);
          Assert(kind != kind::BOUND_VARIABLE && kind != kind::SKOLEM);

          switch (kind)
          {
            /* ---- Arithmetic operators ---- */
            case kind::FLOATINGPOINT_ABS:
              Assert(d_fpMap.find(cur[0]) != d_fpMap.end());
              d_fpMap.insert(cur,
                             symfpu::absolute<traits>(
                                 fpt(t), (*d_fpMap.find(cur[0])).second));
              break;

            case kind::FLOATINGPOINT_NEG:
              Assert(d_fpMap.find(cur[0]) != d_fpMap.end());
              d_fpMap.insert(cur,
                             symfpu::negate<traits>(
                                 fpt(t), (*d_fpMap.find(cur[0])).second));
              break;

            case kind::FLOATINGPOINT_SQRT:
              Assert(d_rmMap.find(cur[0]) != d_rmMap.end());
              Assert(d_fpMap.find(cur[1]) != d_fpMap.end());
              d_fpMap.insert(
                  cur,
                  symfpu::sqrt<traits>(fpt(t),
                                       (*d_rmMap.find(cur[0])).second,
                                       (*d_fpMap.find(cur[1])).second));
              break;

            case kind::FLOATINGPOINT_RTI:
              Assert(d_rmMap.find(cur[0]) != d_rmMap.end());
              Assert(d_fpMap.find(cur[1]) != d_fpMap.end());
              d_fpMap.insert(cur,
                             symfpu::roundToIntegral<traits>(
                                 fpt(t),
                                 (*d_rmMap.find(cur[0])).second,
                                 (*d_fpMap.find(cur[1])).second));
              break;

            case kind::FLOATINGPOINT_REM:
              Assert(d_fpMap.find(cur[0]) != d_fpMap.end());
              Assert(d_fpMap.find(cur[1]) != d_fpMap.end());
              d_fpMap.insert(
                  cur,
                  symfpu::remainder<traits>(fpt(t),
                                            (*d_fpMap.find(cur[0])).second,
                                            (*d_fpMap.find(cur[1])).second));
              break;

            case kind::FLOATINGPOINT_MAX_TOTAL:
              Assert(d_fpMap.find(cur[0]) != d_fpMap.end());
              Assert(d_fpMap.find(cur[1]) != d_fpMap.end());
              Assert(cur[2].getType().isBitVector());
              d_fpMap.insert(cur,
                             symfpu::max<traits>(fpt(t),
                                                 (*d_fpMap.find(cur[0])).second,
                                                 (*d_fpMap.find(cur[1])).second,
                                                 prop(cur[2])));
              break;

            case kind::FLOATINGPOINT_MIN_TOTAL:
              Assert(d_fpMap.find(cur[0]) != d_fpMap.end());
              Assert(d_fpMap.find(cur[1]) != d_fpMap.end());
              Assert(cur[2].getType().isBitVector());
              d_fpMap.insert(cur,
                             symfpu::min<traits>(fpt(t),
                                                 (*d_fpMap.find(cur[0])).second,
                                                 (*d_fpMap.find(cur[1])).second,
                                                 prop(cur[2])));
              break;

            case kind::FLOATINGPOINT_ADD:
              Assert(d_rmMap.find(cur[0]) != d_rmMap.end());
              Assert(d_fpMap.find(cur[1]) != d_fpMap.end());
              Assert(d_fpMap.find(cur[2]) != d_fpMap.end());
              d_fpMap.insert(cur,
                             symfpu::add<traits>(fpt(t),
                                                 (*d_rmMap.find(cur[0])).second,
                                                 (*d_fpMap.find(cur[1])).second,
                                                 (*d_fpMap.find(cur[2])).second,
                                                 prop(true)));
              break;

            case kind::FLOATINGPOINT_MULT:
              Assert(d_rmMap.find(cur[0]) != d_rmMap.end());
              Assert(d_fpMap.find(cur[1]) != d_fpMap.end());
              Assert(d_fpMap.find(cur[2]) != d_fpMap.end());
              d_fpMap.insert(
                  cur,
                  symfpu::multiply<traits>(fpt(t),
                                           (*d_rmMap.find(cur[0])).second,
                                           (*d_fpMap.find(cur[1])).second,
                                           (*d_fpMap.find(cur[2])).second));
              break;

            case kind::FLOATINGPOINT_DIV:
              Assert(d_rmMap.find(cur[0]) != d_rmMap.end());
              Assert(d_fpMap.find(cur[1]) != d_fpMap.end());
              Assert(d_fpMap.find(cur[2]) != d_fpMap.end());
              d_fpMap.insert(
                  cur,
                  symfpu::divide<traits>(fpt(t),
                                         (*d_rmMap.find(cur[0])).second,
                                         (*d_fpMap.find(cur[1])).second,
                                         (*d_fpMap.find(cur[2])).second));
              break;

            case kind::FLOATINGPOINT_FMA:
              Assert(d_rmMap.find(cur[0]) != d_rmMap.end());
              Assert(d_fpMap.find(cur[1]) != d_fpMap.end());
              Assert(d_fpMap.find(cur[2]) != d_fpMap.end());
              Assert(d_fpMap.find(cur[3]) != d_fpMap.end());

              d_fpMap.insert(
                  cur,
                  symfpu::fma<traits>(fpt(t),
                                      (*d_rmMap.find(cur[0])).second,
                                      (*d_fpMap.find(cur[1])).second,
                                      (*d_fpMap.find(cur[2])).second,
                                      (*d_fpMap.find(cur[3])).second));
              break;

            /* ---- Conversions ---- */
            case kind::FLOATINGPOINT_TO_FP_FROM_FP:
              Assert(d_rmMap.find(cur[0]) != d_rmMap.end());
              Assert(d_fpMap.find(cur[1]) != d_fpMap.end());
              d_fpMap.insert(cur,
                             symfpu::convertFloatToFloat<traits>(
                                 fpt(cur[1].getType()),
                                 fpt(t),
                                 (*d_rmMap.find(cur[0])).second,
                                 (*d_fpMap.find(cur[1])).second));
              break;

            case kind::FLOATINGPOINT_FP:
            {
              Assert(cur[0].getType().isBitVector());
              Assert(cur[1].getType().isBitVector());
              Assert(cur[2].getType().isBitVector());

              Node IEEEBV(
                  nm->mkNode(kind::BITVECTOR_CONCAT, cur[0], cur[1], cur[2]));
              d_fpMap.insert(cur, symfpu::unpack<traits>(fpt(t), IEEEBV));
            }
            break;

            case kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV:
              Assert(cur[0].getType().isBitVector());
              d_fpMap.insert(cur, symfpu::unpack<traits>(fpt(t), ubv(cur[0])));
              break;

            case kind::FLOATINGPOINT_TO_FP_FROM_SBV:
              Assert(d_rmMap.find(cur[0]) != d_rmMap.end());
              d_fpMap.insert(
                  cur,
                  symfpu::convertSBVToFloat<traits>(
                      fpt(t), (*d_rmMap.find(cur[0])).second, sbv(cur[1])));
              break;

            case kind::FLOATINGPOINT_TO_FP_FROM_UBV:
              Assert(d_rmMap.find(cur[0]) != d_rmMap.end());
              d_fpMap.insert(
                  cur,
                  symfpu::convertUBVToFloat<traits>(
                      fpt(t), (*d_rmMap.find(cur[0])).second, ubv(cur[1])));
              break;

            case kind::FLOATINGPOINT_TO_FP_FROM_REAL:
              d_fpMap.insert(cur, buildComponents(cur));
              // Rely on the real theory and theory combination
              // to handle the value
              break;

            default: Unreachable() << "Unhandled kind " << kind; break;
          }
        }
      }
      else if (t.isBoolean())
      {
        switch (kind)
        {
          /* ---- Comparisons --------------------------------------- */
          case kind::EQUAL:
          {
            TypeNode childType(cur[0].getType());

            if (childType.isFloatingPoint())
            {
              Assert(d_fpMap.find(cur[0]) != d_fpMap.end());
              Assert(d_fpMap.find(cur[1]) != d_fpMap.end());
              d_boolMap.insert(
                  cur,
                  symfpu::smtlibEqual<traits>(fpt(childType),
                                              (*d_fpMap.find(cur[0])).second,
                                              (*d_fpMap.find(cur[1])).second));
            }
            else if (childType.isRoundingMode())
            {
              Assert(d_rmMap.find(cur[0]) != d_rmMap.end());
              Assert(d_rmMap.find(cur[1]) != d_rmMap.end());
              d_boolMap.insert(cur,
                               (*d_rmMap.find(cur[0])).second
                                   == (*d_rmMap.find(cur[1])).second);
            }
            // else do nothing
          }
          break;

          case kind::FLOATINGPOINT_LEQ:
            Assert(d_fpMap.find(cur[0]) != d_fpMap.end());
            Assert(d_fpMap.find(cur[1]) != d_fpMap.end());
            d_boolMap.insert(cur,
                             symfpu::lessThanOrEqual<traits>(
                                 fpt(cur[0].getType()),
                                 (*d_fpMap.find(cur[0])).second,
                                 (*d_fpMap.find(cur[1])).second));
            break;

          case kind::FLOATINGPOINT_LT:
            Assert(d_fpMap.find(cur[0]) != d_fpMap.end());
            Assert(d_fpMap.find(cur[1]) != d_fpMap.end());
            d_boolMap.insert(
                cur,
                symfpu::lessThan<traits>(fpt(cur[0].getType()),
                                         (*d_fpMap.find(cur[0])).second,
                                         (*d_fpMap.find(cur[1])).second));
            break;

          /* ---- Tester -------------------------------------------- */
          case kind::FLOATINGPOINT_IS_NORMAL:
            Assert(d_fpMap.find(cur[0]) != d_fpMap.end());
            d_boolMap.insert(
                cur,
                symfpu::isNormal<traits>(fpt(cur[0].getType()),
                                         (*d_fpMap.find(cur[0])).second));
            break;

          case kind::FLOATINGPOINT_IS_SUBNORMAL:
            Assert(d_fpMap.find(cur[0]) != d_fpMap.end());
            d_boolMap.insert(
                cur,
                symfpu::isSubnormal<traits>(fpt(cur[0].getType()),
                                            (*d_fpMap.find(cur[0])).second));
            break;

          case kind::FLOATINGPOINT_IS_ZERO:
            Assert(d_fpMap.find(cur[0]) != d_fpMap.end());
            d_boolMap.insert(
                cur,
                symfpu::isZero<traits>(fpt(cur[0].getType()),
                                       (*d_fpMap.find(cur[0])).second));
            break;

          case kind::FLOATINGPOINT_IS_INF:
            Assert(d_fpMap.find(cur[0]) != d_fpMap.end());
            d_boolMap.insert(
                cur,
                symfpu::isInfinite<traits>(fpt(cur[0].getType()),
                                           (*d_fpMap.find(cur[0])).second));
            break;

          case kind::FLOATINGPOINT_IS_NAN:
            Assert(d_fpMap.find(cur[0]) != d_fpMap.end());
            d_boolMap.insert(
                cur,
                symfpu::isNaN<traits>(fpt(cur[0].getType()),
                                      (*d_fpMap.find(cur[0])).second));
            break;

          case kind::FLOATINGPOINT_IS_NEG:
            Assert(d_fpMap.find(cur[0]) != d_fpMap.end());
            d_boolMap.insert(
                cur,
                symfpu::isNegative<traits>(fpt(cur[0].getType()),
                                           (*d_fpMap.find(cur[0])).second));
            break;

          case kind::FLOATINGPOINT_IS_POS:
            Assert(d_fpMap.find(cur[0]) != d_fpMap.end());
            d_boolMap.insert(
                cur,
                symfpu::isPositive<traits>(fpt(cur[0].getType()),
                                           (*d_fpMap.find(cur[0])).second));
            break;

          default:;  // do nothing
        }
      }
      else if (t.isBitVector())
      {
        /* ---- Conversions --------------------------------------- */
        if (kind == kind::FLOATINGPOINT_TO_UBV_TOTAL)
        {
          Assert(d_rmMap.find(cur[0]) != d_rmMap.end());
          Assert(d_fpMap.find(cur[1]) != d_fpMap.end());
          FloatingPointToUBVTotal info =
              cur.getOperator().getConst<FloatingPointToUBVTotal>();
          d_ubvMap.insert(
              cur,
              symfpu::convertFloatToUBV<traits>(fpt(cur[1].getType()),
                                                (*d_rmMap.find(cur[0])).second,
                                                (*d_fpMap.find(cur[1])).second,
                                                info.d_bv_size,
                                                ubv(cur[2])));
        }
        else if (kind == kind::FLOATINGPOINT_TO_SBV_TOTAL)
        {
          Assert(d_rmMap.find(cur[0]) != d_rmMap.end());
          Assert(d_fpMap.find(cur[1]) != d_fpMap.end());
          FloatingPointToSBVTotal info =
              cur.getOperator().getConst<FloatingPointToSBVTotal>();

          d_sbvMap.insert(
              cur,
              symfpu::convertFloatToSBV<traits>(fpt(cur[1].getType()),
                                                (*d_rmMap.find(cur[0])).second,
                                                (*d_fpMap.find(cur[1])).second,
                                                info.d_bv_size,
                                                sbv(cur[2])));
        }
        // else do nothing
      }
    }
    else
    {
      Assert(visited.at(cur) == 1);
      continue;
    }
  }

  if (d_boolMap.find(node) != d_boolMap.end())
  {
    Assert(node.getType().isBoolean());
    return (*d_boolMap.find(node)).second;
  }
  if (d_sbvMap.find(node) != d_sbvMap.end())
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_SBV_TOTAL);
    return (*d_sbvMap.find(node)).second;
  }
  if (d_ubvMap.find(node) != d_ubvMap.end())
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_UBV_TOTAL);
    return (*d_ubvMap.find(node)).second;
  }
  return node;
}

Node FpWordBlaster::getValue(Valuation& val, TNode var)
{
  Assert(var.getKind() == kind::FLOATINGPOINT_TO_FP_FROM_SBV
         || var.getKind() == kind::FLOATINGPOINT_TO_FP_FROM_UBV
         || var.getKind() == kind::FLOATINGPOINT_TO_FP_FROM_REAL
         || var.getKind() == kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV
         || Theory::isLeafOf(var, THEORY_FP));

  TypeNode t(var.getType());

  Assert(t.isRoundingMode() || t.isFloatingPoint())
      << "Asking for the value of a type that is not managed by the "
         "floating-point theory";

  if (t.isRoundingMode())
  {
    rmMap::const_iterator i(d_rmMap.find(var));
    if (i == d_rmMap.end())
    {
      return Node::null();
    }
    return rmToNode((*i).second);
  }

  fpMap::const_iterator i(d_fpMap.find(var));
  if (i == d_fpMap.end())
  {
    return Node::null();
  }
  return ufToNode(fpt(t), (*i).second);
}

}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal
