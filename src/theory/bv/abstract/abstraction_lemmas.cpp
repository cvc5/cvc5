/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Refinement lemma schemes for the bit-vector arithmetic abstraction.
 *
 * Direct port of Bitwuzla's `src/solver/abstract/abstraction_lemmas.cpp`
 * (Table 2 of "Scalable Bit-Blasting with Abstractions", CAV 2024).
 * Every lemma `l[x,s,t]` for an abstracted term `t = x <op> s` satisfies
 * `(x <op> s = t) => l` and is therefore sound to assert as a refinement.
 *
 * Ported from Bitwuzla's implementation of the abstraction lemmas, see
 * https://github.com/bitwuzla/bitwuzla/blob/main/src/solver/abstract/abstraction_lemmas.cpp
 * (Copyright (C) 2022 by the Bitwuzla authors, MIT license).
 */

#include "theory/bv/abstract/abstraction_lemmas.h"

#include "base/check.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"

namespace cvc5::internal {
namespace theory {
namespace bv::abstract {

/* --- LemmaKind ------------------------------------------------------------ */

std::ostream& operator<<(std::ostream& os, LemmaKind kind)
{
  os << std::to_string(kind);
  return os;
}

/* --- Lemma ---------------------------------------------------------------- */

// Lemma<K> provides both instances as null-node defaults; each scheme below
// specializes exactly one of them. A purely symbolic lemma thus returns a null
// Node for the value instance, and vice versa.

#define LEMMA(kind) \
  template <>       \
  Node Lemma<LemmaKind::kind>::instance(TNode x, TNode s, TNode t) const

#define LEMMA_VAL(kind)                  \
  template <>                            \
  Node Lemma<LemmaKind::kind>::instance( \
      TNode x, TNode s, TNode t, TNode xval, TNode sval) const

// Multiplication lemmas

LEMMA_VAL(MUL1_POW2);
LEMMA_VAL(MUL2_NEG_POW2);
LEMMA(MUL3_IC);
LEMMA(MUL4_ODD);
LEMMA(MUL5);
LEMMA(MUL6);
LEMMA(MUL7);
LEMMA(MUL8);
LEMMA(MUL9);
LEMMA(MUL10);
LEMMA(MUL13);
LEMMA(MUL15);
LEMMA(MUL19);
LEMMA(MUL16);
LEMMA(MUL18);
LEMMA(MUL17);
LEMMA(MUL11);
LEMMA(MUL12);
LEMMA(MUL14);

// Unsigned division lemmas

LEMMA_VAL(UDIV1_POW2);
LEMMA(UDIV2);
LEMMA(UDIV3);
LEMMA(UDIV4);
LEMMA(UDIV5);
LEMMA(UDIV6);
LEMMA(UDIV7);
LEMMA(UDIV8);
LEMMA(UDIV9);
LEMMA(UDIV10);
LEMMA(UDIV11);
LEMMA(UDIV12);
LEMMA(UDIV13);
LEMMA(UDIV14);
LEMMA(UDIV15);
LEMMA(UDIV16);
LEMMA(UDIV17);
LEMMA(UDIV18);
LEMMA(UDIV19);
LEMMA(UDIV20);
LEMMA(UDIV21);
LEMMA(UDIV22);
LEMMA(UDIV23);
LEMMA(UDIV24);
LEMMA(UDIV25);
LEMMA(UDIV26);
LEMMA(UDIV27);
LEMMA(UDIV28);
LEMMA(UDIV29);
LEMMA(UDIV30);
LEMMA(UDIV31);
LEMMA(UDIV32);
LEMMA(UDIV33);
LEMMA(UDIV34);
LEMMA(UDIV35);
LEMMA(UDIV36);
LEMMA(UDIV37);

// Unsigned remainder lemmas

LEMMA_VAL(UREM1_POW2);
LEMMA(UREM2);
LEMMA(UREM3);
LEMMA(UREM4);
LEMMA(UREM5);
LEMMA(UREM6);
LEMMA(UREM7);
LEMMA(UREM8);
LEMMA(UREM9);
LEMMA(UREM10);
LEMMA(UREM11);
LEMMA(UREM12);
LEMMA(UREM13);
LEMMA(UREM14);
LEMMA(UREM15);

#undef LEMMA
#undef LEMMA_VAL

/* --- node construction helpers ------------------------------------------- */

namespace {

// Bit-vector operators.
Node bvnot(NodeManager* nm, TNode a)
{
  return nm->mkNode(Kind::BITVECTOR_NOT, a);
}
Node bvneg(NodeManager* nm, TNode a)
{
  return nm->mkNode(Kind::BITVECTOR_NEG, a);
}
Node bvand(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::BITVECTOR_AND, a, b);
}
Node bvor(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::BITVECTOR_OR, a, b);
}
Node bvxor(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::BITVECTOR_XOR, a, b);
}
Node bvadd(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::BITVECTOR_ADD, a, b);
}
Node bvsub(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::BITVECTOR_SUB, a, b);
}
Node bvshl(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::BITVECTOR_SHL, a, b);
}
Node bvlshr(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::BITVECTOR_LSHR, a, b);
}
Node bvult(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::BITVECTOR_ULT, a, b);
}
Node bvule(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::BITVECTOR_ULE, a, b);
}
Node bvuge(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::BITVECTOR_UGE, a, b);
}

// Boolean connectives / (dis)equality.
Node eq(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::EQUAL, a, b);
}
Node distinct(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::NOT, nm->mkNode(Kind::EQUAL, a, b));
}
Node impl(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::IMPLIES, a, b);
}
Node andn(NodeManager* nm, TNode a, TNode b)
{
  return nm->mkNode(Kind::AND, a, b);
}

// Bit-vector constants.
Node one(NodeManager* nm, TNode x)
{
  return utils::mkOne(nm, utils::getSize(x));
}
Node zero(NodeManager* nm, TNode x)
{
  return utils::mkZero(nm, utils::getSize(x));
}
Node ones(NodeManager* nm, TNode x)
{
  return utils::mkOnes(nm, utils::getSize(x));
}
}  // namespace

/* --- Multiplication lemmas ----------------------------------------------- */

// 1*: (=> (= x 2^i) (= t (bvshl s i)))
template <>
Node Lemma<LemmaKind::MUL1_POW2>::instance(
    TNode x, TNode s, TNode t, TNode xval, CVC5_UNUSED TNode sval) const
{
  Assert(xval.getKind() == Kind::CONST_BITVECTOR);
  const BitVector& bv = xval.getConst<BitVector>();
  unsigned p = bv.isPow2();
  if (p == 0) return Node();
  Node shiftBy = utils::mkConst(d_nm, bv.getSize(), p - 1);
  return impl(d_nm, eq(d_nm, x, xval), eq(d_nm, t, bvshl(d_nm, s, shiftBy)));
}

// 2*: (=> (= x -2^i) (= t (bvshl (bvneg s) i)))
template <>
Node Lemma<LemmaKind::MUL2_NEG_POW2>::instance(
    TNode x, TNode s, TNode t, TNode xval, CVC5_UNUSED TNode sval) const
{
  Assert(xval.getKind() == Kind::CONST_BITVECTOR);
  const BitVector& bv = xval.getConst<BitVector>();
  unsigned w = bv.getSize();
  // bvneg of the minimum signed value is itself (a power of two), but the
  // lemma is for the "-2^i" case with i < w-1; skip it (matches Bitwuzla).
  if (bv == BitVector::mkMinSigned(w)) return Node();
  BitVector neg = -bv;
  unsigned p = neg.isPow2();
  if (p == 0) return Node();
  Node shiftBy = utils::mkConst(d_nm, w, p - 1);
  return impl(d_nm,
              eq(d_nm, x, xval),
              eq(d_nm, t, bvshl(d_nm, bvneg(d_nm, s), shiftBy)));
}

// 3*: (= (bvand (bvor (bvneg s) s) t) t)
template <>
Node Lemma<LemmaKind::MUL3_IC>::instance(CVC5_UNUSED TNode x,
                                         TNode s,
                                         TNode t) const
{
  return eq(d_nm, bvand(d_nm, bvor(d_nm, bvneg(d_nm, s), s), t), t);
}

// 4*: (= ((_ extract 0 0) t) (bvand x[0] s[0]))
template <>
Node Lemma<LemmaKind::MUL4_ODD>::instance(TNode x, TNode s, TNode t) const
{
  return eq(d_nm,
            utils::mkExtract(t, 0, 0),
            bvand(d_nm, utils::mkExtract(x, 0, 0), utils::mkExtract(s, 0, 0)));
}

// 5: (not (= s (bvnot (bvor t (bvand 1 (bvor x s))))))
template <>
Node Lemma<LemmaKind::MUL5>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "MUL5 is not valid for bit-width 1";
  return distinct(
      d_nm,
      s,
      bvnot(d_nm, bvor(d_nm, t, bvand(d_nm, one(d_nm, x), bvor(d_nm, x, s)))));
}

// 6: (not (= (bvand x t) (bvor s (bvnot t))))
template <>
Node Lemma<LemmaKind::MUL6>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "MUL6 is not valid for bit-width 1";
  return distinct(d_nm, bvand(d_nm, x, t), bvor(d_nm, s, bvnot(d_nm, t)));
}

// 7: (not (= t (bvshl (bvor s 1) (bvshl t x))))
template <>
Node Lemma<LemmaKind::MUL7>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "MUL7 is not valid for bit-width 1";
  return distinct(
      d_nm, t, bvshl(d_nm, bvor(d_nm, s, one(d_nm, x)), bvshl(d_nm, t, x)));
}

// 8: (= s (bvshl s (bvand x (bvlshr 1 t))))
template <>
Node Lemma<LemmaKind::MUL8>::instance(TNode x, TNode s, TNode t) const
{
  return eq(
      d_nm, s, bvshl(d_nm, s, bvand(d_nm, x, bvlshr(d_nm, one(d_nm, x), t))));
}

// 9: (bvuge t (bvand 1 (bvlshr (bvand x s) 1)))
template <>
Node Lemma<LemmaKind::MUL9>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) != 2) << "MUL9 is not valid for bit-width 2";
  Node o = one(d_nm, x);
  return bvuge(d_nm, t, bvand(d_nm, o, bvlshr(d_nm, bvand(d_nm, x, s), o)));
}

// 10: (not (= x (bvxor 1 (bvshl x (bvxor s t)))))
template <>
Node Lemma<LemmaKind::MUL10>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, x, bvxor(d_nm, one(d_nm, x), bvshl(d_nm, x, bvxor(d_nm, s, t))));
}

// 11: (not (= t (bvor 1 (bvnot (bvxor x s)))))
template <>
Node Lemma<LemmaKind::MUL11>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "MUL11 is not valid for bit-width 1";
  return distinct(
      d_nm, t, bvor(d_nm, one(d_nm, x), bvnot(d_nm, bvxor(d_nm, x, s))));
}

// 12: (not (= t (bvor (bvnot 1) (bvxor x s))))
template <>
Node Lemma<LemmaKind::MUL12>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "MUL12 is not valid for bit-width 1";
  return distinct(
      d_nm, t, bvor(d_nm, bvnot(d_nm, one(d_nm, x)), bvxor(d_nm, x, s)));
}

// 13: (not (= x (bvsub (bvshl x (bvadd s t)) 1)))
template <>
Node Lemma<LemmaKind::MUL13>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, x, bvsub(d_nm, bvshl(d_nm, x, bvadd(d_nm, s, t)), one(d_nm, x)));
}

// 14: (not (= x (bvsub 1 (bvshl x (bvsub s t)))))
template <>
Node Lemma<LemmaKind::MUL14>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, x, bvsub(d_nm, one(d_nm, x), bvshl(d_nm, x, bvsub(d_nm, s, t))));
}

// 15: (not (= s (bvadd 1 (bvshl s (bvsub t x)))))
template <>
Node Lemma<LemmaKind::MUL15>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, s, bvadd(d_nm, one(d_nm, x), bvshl(d_nm, s, bvsub(d_nm, t, x))));
}

// 16: (not (= s (bvsub 1 (bvshl s (bvsub t x)))))
template <>
Node Lemma<LemmaKind::MUL16>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, s, bvsub(d_nm, one(d_nm, x), bvshl(d_nm, s, bvsub(d_nm, t, x))));
}

// 17: (not (= s (bvadd 1 (bvshl s (bvsub x t)))))
template <>
Node Lemma<LemmaKind::MUL17>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, s, bvadd(d_nm, one(d_nm, x), bvshl(d_nm, s, bvsub(d_nm, x, t))));
}

// 18: (not (= t (bvor 1 (bvadd x s))))
template <>
Node Lemma<LemmaKind::MUL18>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "MUL18 is not valid for bit-width 1";
  return distinct(d_nm, t, bvor(d_nm, one(d_nm, x), bvadd(d_nm, x, s)));
}

// 19: (not (= x (bvnot (bvshl x (bvadd s t)))))
template <>
Node Lemma<LemmaKind::MUL19>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(d_nm, x, bvnot(d_nm, bvshl(d_nm, x, bvadd(d_nm, s, t))));
}

/* --- unsigned division lemmas -------------------------------------------- */

// 1*: (=> (= s 2^i) (= t (bvlshr x i)))
template <>
Node Lemma<LemmaKind::UDIV1_POW2>::instance(
    TNode x, TNode s, TNode t, CVC5_UNUSED TNode xval, TNode sval) const
{
  Assert(sval.getKind() == Kind::CONST_BITVECTOR);
  const BitVector& bv = sval.getConst<BitVector>();
  unsigned p = bv.isPow2();
  if (p == 0) return Node();
  Node shiftBy = utils::mkConst(d_nm, bv.getSize(), p - 1);
  return impl(d_nm, eq(d_nm, s, sval), eq(d_nm, t, bvlshr(d_nm, x, shiftBy)));
}

// 2*: (=> (and (= s x) (distinct s 0)) (= t 1))
template <>
Node Lemma<LemmaKind::UDIV2>::instance(TNode x, TNode s, TNode t) const
{
  return impl(d_nm,
              andn(d_nm, eq(d_nm, s, x), distinct(d_nm, s, zero(d_nm, x))),
              eq(d_nm, t, one(d_nm, x)));
}

// 3*: (=> (= s 0) (= t (bvnot 0)))
template <>
Node Lemma<LemmaKind::UDIV3>::instance(TNode x, TNode s, TNode t) const
{
  return impl(d_nm, eq(d_nm, s, zero(d_nm, x)), eq(d_nm, t, ones(d_nm, x)));
}

// 4*: (=> (and (= x 0) (distinct s 0)) (= t 0))
template <>
Node Lemma<LemmaKind::UDIV4>::instance(TNode x, TNode s, TNode t) const
{
  return impl(
      d_nm,
      andn(d_nm, eq(d_nm, x, zero(d_nm, x)), distinct(d_nm, s, zero(d_nm, x))),
      eq(d_nm, t, zero(d_nm, x)));
}

// 5*: (=> (distinct s 0) (bvule t x))
template <>
Node Lemma<LemmaKind::UDIV5>::instance(TNode x, TNode s, TNode t) const
{
  return impl(d_nm, distinct(d_nm, s, zero(d_nm, x)), bvule(d_nm, t, x));
}

// 6*: (=> (and (= s ~0) (distinct x ~0)) (= t 0))
template <>
Node Lemma<LemmaKind::UDIV6>::instance(TNode x, TNode s, TNode t) const
{
  return impl(
      d_nm,
      andn(d_nm, eq(d_nm, s, ones(d_nm, x)), distinct(d_nm, x, ones(d_nm, x))),
      eq(d_nm, t, zero(d_nm, x)));
}

// 7: (not (bvult x (bvneg (bvand (bvneg s) (bvneg t)))))
template <>
Node Lemma<LemmaKind::UDIV7>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, x, bvneg(d_nm, bvand(d_nm, bvneg(d_nm, s), bvneg(d_nm, t))));
}

// 8: (not (bvult (bvneg (bvor s 1)) t))
template <>
Node Lemma<LemmaKind::UDIV8>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, bvneg(d_nm, bvor(d_nm, s, one(d_nm, x))), t);
}

// 9: (not (= t (bvneg (bvand s (bvnot x)))))
template <>
Node Lemma<LemmaKind::UDIV9>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(d_nm, t, bvneg(d_nm, bvand(d_nm, s, bvnot(d_nm, x))));
}

// 10: (not (= (bvor s t) (bvand x (bvnot 1))))
template <>
Node Lemma<LemmaKind::UDIV10>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, bvor(d_nm, s, t), bvand(d_nm, x, bvnot(d_nm, one(d_nm, x))));
}

// 11: (not (= (bvor s 1) (bvand x (bvnot t))))
template <>
Node Lemma<LemmaKind::UDIV11>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, bvor(d_nm, s, one(d_nm, x)), bvand(d_nm, x, bvnot(d_nm, t)));
}

// 12: (not (bvult (bvand x (bvneg t)) (bvand s t)))
template <>
Node Lemma<LemmaKind::UDIV12>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, bvand(d_nm, x, bvneg(d_nm, t)), bvand(d_nm, s, t));
}

// 13: (not (bvult s (bvlshr x t)))
template <>
Node Lemma<LemmaKind::UDIV13>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, s, bvlshr(d_nm, x, t));
}

// 14: (not (bvult x (bvshl (bvlshr s (bvshl s t)) 1)))
template <>
Node Lemma<LemmaKind::UDIV14>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, x, bvshl(d_nm, bvlshr(d_nm, s, bvshl(d_nm, s, t)), one(d_nm, x)));
}

// 15: (not (bvult x (bvlshr (bvshl t 1) (bvshl t s))))
template <>
Node Lemma<LemmaKind::UDIV15>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, x, bvlshr(d_nm, bvshl(d_nm, t, one(d_nm, x)), bvshl(d_nm, t, s)));
}

// 16: (not (bvult t (bvshl (bvlshr x s) 1)))
template <>
Node Lemma<LemmaKind::UDIV16>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, t, bvshl(d_nm, bvlshr(d_nm, x, s), one(d_nm, x)));
}

// 17: (not (bvult x (bvand (bvor x t) (bvshl s 1))))
template <>
Node Lemma<LemmaKind::UDIV17>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, x, bvand(d_nm, bvor(d_nm, x, t), bvshl(d_nm, s, one(d_nm, x))));
}

// 18: (not (bvult x (bvand (bvor x s) (bvshl t 1))))
template <>
Node Lemma<LemmaKind::UDIV18>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, x, bvand(d_nm, bvor(d_nm, x, s), bvshl(d_nm, t, one(d_nm, x))));
}

// 19: (not (= (bvlshr x t) (bvor s t)))
template <>
Node Lemma<LemmaKind::UDIV19>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(d_nm, bvlshr(d_nm, x, t), bvor(d_nm, s, t));
}

// 20: (not (= s (bvnot (bvlshr s (bvlshr t 1)))))
template <>
Node Lemma<LemmaKind::UDIV20>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, s, bvnot(d_nm, bvlshr(d_nm, s, bvlshr(d_nm, t, one(d_nm, x)))));
}

// 21: (not (= x (bvnot (bvand x (bvshl t 1)))))
template <>
Node Lemma<LemmaKind::UDIV21>::instance(TNode x,
                                        CVC5_UNUSED TNode s,
                                        TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "UDIV21 is not valid for bit-width 1";
  return distinct(
      d_nm, x, bvnot(d_nm, bvand(d_nm, x, bvshl(d_nm, t, one(d_nm, x)))));
}

// 22: (not (bvult t (bvlshr (bvshl x 1) s)))
template <>
Node Lemma<LemmaKind::UDIV22>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, t, bvlshr(d_nm, bvshl(d_nm, x, one(d_nm, x)), s));
}

// 23: (not (bvult x (bvshl s (bvnot (bvor x t)))))
template <>
Node Lemma<LemmaKind::UDIV23>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, x, bvshl(d_nm, s, bvnot(d_nm, bvor(d_nm, x, t))));
}

// 24: (not (bvult x (bvshl t (bvnot (bvor x s)))))
template <>
Node Lemma<LemmaKind::UDIV24>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, x, bvshl(d_nm, t, bvnot(d_nm, bvor(d_nm, x, s))));
}

// 25: (not (bvult x (bvxor t (bvlshr t (bvlshr s 1)))))
template <>
Node Lemma<LemmaKind::UDIV25>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, x, bvxor(d_nm, t, bvlshr(d_nm, t, bvlshr(d_nm, s, one(d_nm, x)))));
}

// 26: (not (bvult x (bvxor s (bvlshr s (bvlshr t 1)))))
template <>
Node Lemma<LemmaKind::UDIV26>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, x, bvxor(d_nm, s, bvlshr(d_nm, s, bvlshr(d_nm, t, one(d_nm, x)))));
}

// 27: (not (bvult x (bvshl s (bvnot (bvxor x t)))))
template <>
Node Lemma<LemmaKind::UDIV27>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, x, bvshl(d_nm, s, bvnot(d_nm, bvxor(d_nm, x, t))));
}

// 28: (not (bvult x (bvshl t (bvnot (bvxor x s)))))
template <>
Node Lemma<LemmaKind::UDIV28>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, x, bvshl(d_nm, t, bvnot(d_nm, bvxor(d_nm, x, s))));
}

// 29: (not (= x (bvadd t (bvor s (bvadd x s)))))
template <>
Node Lemma<LemmaKind::UDIV29>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(d_nm, x, bvadd(d_nm, t, bvor(d_nm, s, bvadd(d_nm, x, s))));
}

// 30: (not (= x (bvadd t (bvadd 1 (bvshl 1 x)))))
template <>
Node Lemma<LemmaKind::UDIV30>::instance(TNode x,
                                        CVC5_UNUSED TNode s,
                                        TNode t) const
{
  Assert(utils::getSize(x) >= 3) << "UDIV30 is not valid for bit-width < 3";
  Node o = one(d_nm, x);
  return distinct(d_nm, x, bvadd(d_nm, t, bvadd(d_nm, o, bvshl(d_nm, o, x))));
}

// 31: (not (bvult s (bvlshr (bvadd x t) t)))
template <>
Node Lemma<LemmaKind::UDIV31>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, s, bvlshr(d_nm, bvadd(d_nm, x, t), t));
}

// 32: (not (= x (bvadd t (bvadd t (bvor x s)))))
template <>
Node Lemma<LemmaKind::UDIV32>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "UDIV32 is not valid for bit-width 1";
  return distinct(d_nm, x, bvadd(d_nm, t, bvadd(d_nm, t, bvor(d_nm, x, s))));
}

// 33: (not (bvult (bvxor s (bvor x t)) (bvxor t 1)))
template <>
Node Lemma<LemmaKind::UDIV33>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, bvxor(d_nm, s, bvor(d_nm, x, t)), bvxor(d_nm, t, one(d_nm, x)));
}

// 34: (not (bvult t (bvlshr x (bvsub s 1))))
template <>
Node Lemma<LemmaKind::UDIV34>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, t, bvlshr(d_nm, x, bvsub(d_nm, s, one(d_nm, x))));
}

// 35: (not (bvult (bvsub s 1) (bvlshr x t)))
template <>
Node Lemma<LemmaKind::UDIV35>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, bvsub(d_nm, s, one(d_nm, x)), bvlshr(d_nm, x, t));
}

// 36: (not (= x (bvsub 1 (bvshl x (bvsub x t)))))
template <>
Node Lemma<LemmaKind::UDIV36>::instance(TNode x,
                                        CVC5_UNUSED TNode s,
                                        TNode t) const
{
  Assert(utils::getSize(x) != 2) << "UDIV36 is not valid for bit-width 2";
  return distinct(
      d_nm, x, bvsub(d_nm, one(d_nm, x), bvshl(d_nm, x, bvsub(d_nm, x, t))));
}

// (=> (= s 1) (= t x))
template <>
Node Lemma<LemmaKind::UDIV37>::instance(TNode x, TNode s, TNode t) const
{
  return impl(d_nm, eq(d_nm, s, one(d_nm, x)), eq(d_nm, t, x));
}

/* --- unsigned remainder lemmas ------------------------------------------- */

// 1*: (=> (= s 2^i) (= t (concat 0[w-i] x[i-1:0])))
template <>
Node Lemma<LemmaKind::UREM1_POW2>::instance(
    TNode x, TNode s, TNode t, CVC5_UNUSED TNode xval, TNode sval) const
{
  Assert(sval.getKind() == Kind::CONST_BITVECTOR);
  const BitVector& bv = sval.getConst<BitVector>();
  unsigned p = bv.isPow2();
  if (p == 0) return Node();
  unsigned ctz = p - 1;
  unsigned w = bv.getSize();
  Node rem;
  if (ctz == 0)
  {
    rem = utils::mkZero(d_nm, w);
  }
  else
  {
    // zero_extend by (w - ctz) of the low ctz bits of x.
    rem = utils::mkConcat(utils::mkZero(d_nm, w - ctz),
                          utils::mkExtract(x, ctz - 1, 0));
  }
  return impl(d_nm, eq(d_nm, s, sval), eq(d_nm, t, rem));
}

// 2*: (=> (distinct s 0) (bvult t s))
template <>
Node Lemma<LemmaKind::UREM2>::instance(TNode x, TNode s, TNode t) const
{
  return impl(d_nm, distinct(d_nm, s, zero(d_nm, x)), bvult(d_nm, t, s));
}

// 3*: (=> (= x 0) (= t 0))
template <>
Node Lemma<LemmaKind::UREM3>::instance(TNode x,
                                       CVC5_UNUSED TNode s,
                                       TNode t) const
{
  return impl(d_nm, eq(d_nm, x, zero(d_nm, x)), eq(d_nm, t, zero(d_nm, x)));
}

// 4*: (=> (= s 0) (= t x))
template <>
Node Lemma<LemmaKind::UREM4>::instance(TNode x, TNode s, TNode t) const
{
  return impl(d_nm, eq(d_nm, s, zero(d_nm, x)), eq(d_nm, t, x));
}

// 5*: (=> (= s x) (= t 0))
template <>
Node Lemma<LemmaKind::UREM5>::instance(TNode x, TNode s, TNode t) const
{
  return impl(d_nm, eq(d_nm, s, x), eq(d_nm, t, zero(d_nm, x)));
}

// 6*: (=> (bvult x s) (= t x))
template <>
Node Lemma<LemmaKind::UREM6>::instance(TNode x, TNode s, TNode t) const
{
  return impl(d_nm, bvult(d_nm, x, s), eq(d_nm, t, x));
}

// 7*: (bvuge (bvnot (bvneg s)) t)
template <>
Node Lemma<LemmaKind::UREM7>::instance(CVC5_UNUSED TNode x,
                                       TNode s,
                                       TNode t) const
{
  return bvuge(d_nm, bvnot(d_nm, bvneg(d_nm, s)), t);
}

// 8: (= x (bvand x (bvor s (bvor t (bvneg s)))))
template <>
Node Lemma<LemmaKind::UREM8>::instance(TNode x, TNode s, TNode t) const
{
  return eq(
      d_nm, x, bvand(d_nm, x, bvor(d_nm, s, bvor(d_nm, t, bvneg(d_nm, s)))));
}

// 9: (not (bvult x (bvor t (bvand x s))))
template <>
Node Lemma<LemmaKind::UREM9>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, x, bvor(d_nm, t, bvand(d_nm, x, s)));
}

// 10: (not (= 1 (bvand t (bvnot (bvor x s)))))
template <>
Node Lemma<LemmaKind::UREM10>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, one(d_nm, x), bvand(d_nm, t, bvnot(d_nm, bvor(d_nm, x, s))));
}

// 11: (not (= t (bvor (bvnot x) (bvneg s))))
template <>
Node Lemma<LemmaKind::UREM11>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(d_nm, t, bvor(d_nm, bvnot(d_nm, x), bvneg(d_nm, s)));
}

// 12: (not (bvult (bvand t (bvor x s)) (bvand t 1)))
template <>
Node Lemma<LemmaKind::UREM12>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, bvand(d_nm, t, bvor(d_nm, x, s)), bvand(d_nm, t, one(d_nm, x)));
}

// 13: (not (= x (bvor (bvneg x) (bvneg (bvnot t)))))
template <>
Node Lemma<LemmaKind::UREM13>::instance(TNode x,
                                        CVC5_UNUSED TNode s,
                                        TNode t) const
{
  Assert(utils::getSize(x) >= 3) << "UREM13 is not valid for bit-width < 3";
  return distinct(
      d_nm, x, bvor(d_nm, bvneg(d_nm, x), bvneg(d_nm, bvnot(d_nm, t))));
}

// 14: (not (bvult (bvadd x (bvneg s)) t))
template <>
Node Lemma<LemmaKind::UREM14>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, bvadd(d_nm, x, bvneg(d_nm, s)), t);
}

// 15: (not (bvult (bvxor (bvneg s) (bvor x s)) t))
template <>
Node Lemma<LemmaKind::UREM15>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, bvxor(d_nm, bvneg(d_nm, s), bvor(d_nm, x, s)), t);
}

/* --- LemmaRegistry -------------------------------------------------------- */

LemmaRegistry::LemmaRegistry(NodeManager* nm)
{
  initMul(nm);
  initUdiv(nm);
  initUrem(nm);
}

const std::vector<std::unique_ptr<AbstractionLemma>>& LemmaRegistry::lemmas(
    Kind kind) const
{
  static const std::vector<std::unique_ptr<AbstractionLemma>> empty;
  switch (kind)
  {
    case Kind::BITVECTOR_MULT: return d_mul;
    case Kind::BITVECTOR_UDIV: return d_udiv;
    case Kind::BITVECTOR_UREM: return d_urem;
    default: return empty;
  }
}

void LemmaRegistry::initMul(NodeManager* nm)
{
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL1_POW2>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL2_NEG_POW2>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL3_IC>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL4_ODD>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL5>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL6>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL7>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL8>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL9>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL10>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL11>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL12>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL13>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL14>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL15>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL16>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL17>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL18>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL19>>(nm));
}

void LemmaRegistry::initUdiv(NodeManager* nm)
{
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV1_POW2>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV37>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV2>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV3>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV4>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV5>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV6>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV7>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV8>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV9>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV10>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV11>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV12>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV13>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV14>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV15>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV16>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV17>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV18>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV19>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV20>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV21>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV22>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV23>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV24>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV25>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV26>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV27>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV28>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV29>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV30>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV31>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV32>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV33>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV34>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV35>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV36>>(nm));
}

void LemmaRegistry::initUrem(NodeManager* nm)
{
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM1_POW2>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM2>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM3>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM4>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM5>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM6>>(nm));
  // UREM7 is implied by UREM2 and thus not registered (same as in Bitwuzla).
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM8>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM9>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM10>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM11>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM12>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM13>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM14>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM15>>(nm));
}

}  // namespace bv::abstract
}  // namespace theory
}  // namespace cvc5::internal

/* -------------------------------------------------------------------------- */

namespace std {
std::string to_string(cvc5::internal::theory::bv::abstract::LemmaKind kind)
{
  using namespace cvc5::internal::theory::bv::abstract;
  switch (kind)
  {
    case LemmaKind::MUL1_POW2: return "MUL1_POW2";
    case LemmaKind::MUL2_NEG_POW2: return "MUL2_NEG_POW2";
    case LemmaKind::MUL3_IC: return "MUL3_IC";
    case LemmaKind::MUL4_ODD: return "MUL4_ODD";
    case LemmaKind::MUL5: return "MUL5";
    case LemmaKind::MUL6: return "MUL6";
    case LemmaKind::MUL7: return "MUL7";
    case LemmaKind::MUL8: return "MUL8";
    case LemmaKind::MUL9: return "MUL9";
    case LemmaKind::MUL10: return "MUL10";
    case LemmaKind::MUL11: return "MUL11";
    case LemmaKind::MUL12: return "MUL12";
    case LemmaKind::MUL13: return "MUL13";
    case LemmaKind::MUL14: return "MUL14";
    case LemmaKind::MUL15: return "MUL15";
    case LemmaKind::MUL16: return "MUL16";
    case LemmaKind::MUL17: return "MUL17";
    case LemmaKind::MUL18: return "MUL18";
    case LemmaKind::MUL19: return "MUL19";

    case LemmaKind::UDIV1_POW2: return "UDIV1_POW2";
    case LemmaKind::UDIV2: return "UDIV2";
    case LemmaKind::UDIV3: return "UDIV3";
    case LemmaKind::UDIV4: return "UDIV4";
    case LemmaKind::UDIV5: return "UDIV5";
    case LemmaKind::UDIV6: return "UDIV6";
    case LemmaKind::UDIV7: return "UDIV7";
    case LemmaKind::UDIV8: return "UDIV8";
    case LemmaKind::UDIV9: return "UDIV9";
    case LemmaKind::UDIV10: return "UDIV10";
    case LemmaKind::UDIV11: return "UDIV11";
    case LemmaKind::UDIV12: return "UDIV12";
    case LemmaKind::UDIV13: return "UDIV13";
    case LemmaKind::UDIV14: return "UDIV14";
    case LemmaKind::UDIV15: return "UDIV15";
    case LemmaKind::UDIV16: return "UDIV16";
    case LemmaKind::UDIV17: return "UDIV17";
    case LemmaKind::UDIV18: return "UDIV18";
    case LemmaKind::UDIV19: return "UDIV19";
    case LemmaKind::UDIV20: return "UDIV20";
    case LemmaKind::UDIV21: return "UDIV21";
    case LemmaKind::UDIV22: return "UDIV22";
    case LemmaKind::UDIV23: return "UDIV23";
    case LemmaKind::UDIV24: return "UDIV24";
    case LemmaKind::UDIV25: return "UDIV25";
    case LemmaKind::UDIV26: return "UDIV26";
    case LemmaKind::UDIV27: return "UDIV27";
    case LemmaKind::UDIV28: return "UDIV28";
    case LemmaKind::UDIV29: return "UDIV29";
    case LemmaKind::UDIV30: return "UDIV30";
    case LemmaKind::UDIV31: return "UDIV31";
    case LemmaKind::UDIV32: return "UDIV32";
    case LemmaKind::UDIV33: return "UDIV33";
    case LemmaKind::UDIV34: return "UDIV34";
    case LemmaKind::UDIV35: return "UDIV35";
    case LemmaKind::UDIV36: return "UDIV36";
    case LemmaKind::UDIV37: return "UDIV37";

    case LemmaKind::UREM1_POW2: return "UREM1_POW2";
    case LemmaKind::UREM2: return "UREM2";
    case LemmaKind::UREM3: return "UREM3";
    case LemmaKind::UREM4: return "UREM4";
    case LemmaKind::UREM5: return "UREM5";
    case LemmaKind::UREM6: return "UREM6";
    case LemmaKind::UREM7: return "UREM7";
    case LemmaKind::UREM8: return "UREM8";
    case LemmaKind::UREM9: return "UREM9";
    case LemmaKind::UREM10: return "UREM10";
    case LemmaKind::UREM11: return "UREM11";
    case LemmaKind::UREM12: return "UREM12";
    case LemmaKind::UREM13: return "UREM13";
    case LemmaKind::UREM14: return "UREM14";
    case LemmaKind::UREM15: return "UREM15";
  }
  return "?";
}
}  // namespace std
