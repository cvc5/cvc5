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
#include "cvc5_public.h"
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

/* --- AbstractionLemma ----------------------------------------------------- */

// Default instances; specialized per LemmaKind below. A purely symbolic lemma
// returns a null Node for the value instance, and vice versa.
Node AbstractionLemma::instance(CVC5_UNUSED TNode x,
                                CVC5_UNUSED TNode s,
                                CVC5_UNUSED TNode t) const
{
  return Node();
}

Node AbstractionLemma::instance(CVC5_UNUSED TNode x,
                                CVC5_UNUSED TNode s,
                                CVC5_UNUSED TNode t,
                                CVC5_UNUSED TNode xval,
                                CVC5_UNUSED TNode sval,
                                CVC5_UNUSED TNode tval) const
{
  return Node();
}

/* --- Lemma ---------------------------------------------------------------- */

#define LEMMA(kind) \
  template <>       \
  Node Lemma<LemmaKind::kind>::instance(TNode x, TNode s, TNode t) const

#define LEMMA_VAL(kind)                  \
  template <>                            \
  Node Lemma<LemmaKind::kind>::instance( \
      TNode x, TNode s, TNode t, TNode xval, TNode sval, TNode tval) const

// Multiplication lemmas

LEMMA(MUL_IC);
LEMMA(MUL_ODD);
LEMMA_VAL(MUL_POW2);
LEMMA_VAL(MUL_NEG_POW2);
LEMMA(MUL_REF1);
LEMMA(MUL_REF3);
LEMMA(MUL_REFN3);
LEMMA(MUL_REFN4);
LEMMA(MUL_REFN5);
LEMMA(MUL_REFN6);
LEMMA(MUL_REFN9);
LEMMA(MUL_REFN11);
LEMMA(MUL_REF12);
LEMMA(MUL_REFN12);
LEMMA(MUL_REF13);
LEMMA(MUL_REFN13);
LEMMA(MUL_REF14);
LEMMA(MUL_REF15);
LEMMA(MUL_REF18);

// Unsigned division lemmas

LEMMA_VAL(UDIV_POW2);
LEMMA(UDIV_REF1);
LEMMA(UDIV_REF2);
LEMMA(UDIV_REF3);
LEMMA(UDIV_REF4);
LEMMA(UDIV_REF5);
LEMMA(UDIV_REF6);
LEMMA(UDIV_REF7);
LEMMA(UDIV_REF8);
LEMMA(UDIV_REF9);
LEMMA(UDIV_REF10);
LEMMA(UDIV_REF11);
LEMMA(UDIV_REF12);
LEMMA(UDIV_REF13);
LEMMA(UDIV_REF14);
LEMMA(UDIV_REF15);
LEMMA(UDIV_REF16);
LEMMA(UDIV_REF17);
LEMMA(UDIV_REF18);
LEMMA(UDIV_REF19);
LEMMA(UDIV_REF20);
LEMMA(UDIV_REF21);
LEMMA(UDIV_REF23);
LEMMA(UDIV_REF24);
LEMMA(UDIV_REF25);
LEMMA(UDIV_REF26);
LEMMA(UDIV_REF27);
LEMMA(UDIV_REF28);
LEMMA(UDIV_REF29);
LEMMA(UDIV_REF30);
LEMMA(UDIV_REF31);
LEMMA(UDIV_REF32);
LEMMA(UDIV_REF33);
LEMMA(UDIV_REF34);
LEMMA(UDIV_REF36);
LEMMA(UDIV_REF37);
LEMMA(UDIV_REF38);

// Unsigned remainder lemmas

LEMMA_VAL(UREM_POW2);
LEMMA(UREM_REF1);
LEMMA(UREM_REF2);
LEMMA(UREM_REF3);
LEMMA(UREM_REF4);
LEMMA(UREM_REF5);
LEMMA(UREM_REF6);
LEMMA(UREM_REF7);
LEMMA(UREM_REF8);
LEMMA(UREM_REF9);
LEMMA(UREM_REF10);
LEMMA(UREM_REF11);
LEMMA(UREM_REF12);
LEMMA(UREM_REF13);
LEMMA(UREM_REF14);

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
Node Lemma<LemmaKind::MUL_POW2>::instance(TNode x,
                                          TNode s,
                                          TNode t,
                                          TNode xval,
                                          CVC5_UNUSED TNode sval,
                                          CVC5_UNUSED TNode tval) const
{
  Assert(xval.isConst());
  const BitVector& bv = xval.getConst<BitVector>();
  unsigned p = bv.isPow2();
  if (p == 0) return Node();
  Node shiftBy = utils::mkConst(d_nm, bv.getSize(), p - 1);
  return impl(d_nm, eq(d_nm, x, xval), eq(d_nm, t, bvshl(d_nm, s, shiftBy)));
}

// 2*: (=> (= x -2^i) (= t (bvshl (bvneg s) i)))
template <>
Node Lemma<LemmaKind::MUL_NEG_POW2>::instance(TNode x,
                                              TNode s,
                                              TNode t,
                                              TNode xval,
                                              CVC5_UNUSED TNode sval,
                                              CVC5_UNUSED TNode tval) const
{
  Assert(xval.isConst());
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
Node Lemma<LemmaKind::MUL_IC>::instance(CVC5_UNUSED TNode x,
                                        TNode s,
                                        TNode t) const
{
  return eq(d_nm, bvand(d_nm, bvor(d_nm, bvneg(d_nm, s), s), t), t);
}

// 4*: (= ((_ extract 0 0) t) (bvand x[0] s[0]))
template <>
Node Lemma<LemmaKind::MUL_ODD>::instance(TNode x, TNode s, TNode t) const
{
  return eq(d_nm,
            utils::mkExtract(t, 0, 0),
            bvand(d_nm, utils::mkExtract(x, 0, 0), utils::mkExtract(s, 0, 0)));
}

// 5: (not (= s (bvnot (bvor t (bvand 1 (bvor x s))))))
template <>
Node Lemma<LemmaKind::MUL_REF1>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "MUL_REF1 is not valid for bit-width 1";
  return distinct(
      d_nm,
      s,
      bvnot(d_nm, bvor(d_nm, t, bvand(d_nm, one(d_nm, x), bvor(d_nm, x, s)))));
}

// 6: (not (= (bvand x t) (bvor s (bvnot t))))
template <>
Node Lemma<LemmaKind::MUL_REF3>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "MUL_REF3 is not valid for bit-width 1";
  return distinct(d_nm, bvand(d_nm, x, t), bvor(d_nm, s, bvnot(d_nm, t)));
}

// 7: (not (= t (bvshl (bvor s 1) (bvshl t x))))
template <>
Node Lemma<LemmaKind::MUL_REFN3>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "MUL_REFN3 is not valid for bit-width 1";
  return distinct(
      d_nm, t, bvshl(d_nm, bvor(d_nm, s, one(d_nm, x)), bvshl(d_nm, t, x)));
}

// 8: (= s (bvshl s (bvand x (bvlshr 1 t))))
template <>
Node Lemma<LemmaKind::MUL_REFN4>::instance(TNode x, TNode s, TNode t) const
{
  return eq(
      d_nm, s, bvshl(d_nm, s, bvand(d_nm, x, bvlshr(d_nm, one(d_nm, x), t))));
}

// 9: (bvuge t (bvand 1 (bvlshr (bvand x s) 1)))
template <>
Node Lemma<LemmaKind::MUL_REFN5>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) != 2) << "MUL_REFN5 is not valid for bit-width 2";
  Node o = one(d_nm, x);
  return bvuge(d_nm, t, bvand(d_nm, o, bvlshr(d_nm, bvand(d_nm, x, s), o)));
}

// 10: (not (= x (bvxor 1 (bvshl x (bvxor s t)))))
template <>
Node Lemma<LemmaKind::MUL_REFN6>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, x, bvxor(d_nm, one(d_nm, x), bvshl(d_nm, x, bvxor(d_nm, s, t))));
}

// 11: (not (= t (bvor 1 (bvnot (bvxor x s)))))
template <>
Node Lemma<LemmaKind::MUL_REF14>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "MUL_REF14 is not valid for bit-width 1";
  return distinct(
      d_nm, t, bvor(d_nm, one(d_nm, x), bvnot(d_nm, bvxor(d_nm, x, s))));
}

// 12: (not (= t (bvor (bvnot 1) (bvxor x s))))
template <>
Node Lemma<LemmaKind::MUL_REF15>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "MUL_REF15 is not valid for bit-width 1";
  return distinct(
      d_nm, t, bvor(d_nm, bvnot(d_nm, one(d_nm, x)), bvxor(d_nm, x, s)));
}

// 13: (not (= x (bvsub (bvshl x (bvadd s t)) 1)))
template <>
Node Lemma<LemmaKind::MUL_REFN9>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, x, bvsub(d_nm, bvshl(d_nm, x, bvadd(d_nm, s, t)), one(d_nm, x)));
}

// 14: (not (= x (bvsub 1 (bvshl x (bvsub s t)))))
template <>
Node Lemma<LemmaKind::MUL_REF18>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, x, bvsub(d_nm, one(d_nm, x), bvshl(d_nm, x, bvsub(d_nm, s, t))));
}

// 15: (not (= s (bvadd 1 (bvshl s (bvsub t x)))))
template <>
Node Lemma<LemmaKind::MUL_REFN11>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, s, bvadd(d_nm, one(d_nm, x), bvshl(d_nm, s, bvsub(d_nm, t, x))));
}

// 16: (not (= s (bvsub 1 (bvshl s (bvsub t x)))))
template <>
Node Lemma<LemmaKind::MUL_REFN12>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, s, bvsub(d_nm, one(d_nm, x), bvshl(d_nm, s, bvsub(d_nm, t, x))));
}

// 17: (not (= s (bvadd 1 (bvshl s (bvsub x t)))))
template <>
Node Lemma<LemmaKind::MUL_REFN13>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, s, bvadd(d_nm, one(d_nm, x), bvshl(d_nm, s, bvsub(d_nm, x, t))));
}

// 18: (not (= t (bvor 1 (bvadd x s))))
template <>
Node Lemma<LemmaKind::MUL_REF13>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "MUL_REF13 is not valid for bit-width 1";
  return distinct(d_nm, t, bvor(d_nm, one(d_nm, x), bvadd(d_nm, x, s)));
}

// 19: (not (= x (bvnot (bvshl x (bvadd s t)))))
template <>
Node Lemma<LemmaKind::MUL_REF12>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(d_nm, x, bvnot(d_nm, bvshl(d_nm, x, bvadd(d_nm, s, t))));
}

/* --- unsigned division lemmas -------------------------------------------- */

// 1*: (=> (= s 2^i) (= t (bvlshr x i)))
template <>
Node Lemma<LemmaKind::UDIV_POW2>::instance(TNode x,
                                           TNode s,
                                           TNode t,
                                           CVC5_UNUSED TNode xval,
                                           TNode sval,
                                           CVC5_UNUSED TNode tval) const
{
  Assert(sval.isConst());
  const BitVector& bv = sval.getConst<BitVector>();
  unsigned p = bv.isPow2();
  if (p == 0) return Node();
  Node shiftBy = utils::mkConst(d_nm, bv.getSize(), p - 1);
  return impl(d_nm, eq(d_nm, s, sval), eq(d_nm, t, bvlshr(d_nm, x, shiftBy)));
}

// (=> (= s 1) (= t x))
template <>
Node Lemma<LemmaKind::UDIV_REF1>::instance(TNode x, TNode s, TNode t) const
{
  return impl(d_nm, eq(d_nm, s, one(d_nm, x)), eq(d_nm, t, x));
}

// 2*: (=> (and (= s x) (distinct s 0)) (= t 1))
template <>
Node Lemma<LemmaKind::UDIV_REF2>::instance(TNode x, TNode s, TNode t) const
{
  return impl(d_nm,
              andn(d_nm, eq(d_nm, s, x), distinct(d_nm, s, zero(d_nm, x))),
              eq(d_nm, t, one(d_nm, x)));
}

// 3*: (=> (= s 0) (= t (bvnot 0)))
template <>
Node Lemma<LemmaKind::UDIV_REF3>::instance(TNode x, TNode s, TNode t) const
{
  return impl(d_nm, eq(d_nm, s, zero(d_nm, x)), eq(d_nm, t, ones(d_nm, x)));
}

// 4*: (=> (and (= x 0) (distinct s 0)) (= t 0))
template <>
Node Lemma<LemmaKind::UDIV_REF4>::instance(TNode x, TNode s, TNode t) const
{
  return impl(
      d_nm,
      andn(d_nm, eq(d_nm, x, zero(d_nm, x)), distinct(d_nm, s, zero(d_nm, x))),
      eq(d_nm, t, zero(d_nm, x)));
}

// 5*: (=> (distinct s 0) (bvule t x))
template <>
Node Lemma<LemmaKind::UDIV_REF5>::instance(TNode x, TNode s, TNode t) const
{
  return impl(d_nm, distinct(d_nm, s, zero(d_nm, x)), bvule(d_nm, t, x));
}

// 6*: (=> (and (= s ~0) (distinct x ~0)) (= t 0))
template <>
Node Lemma<LemmaKind::UDIV_REF6>::instance(TNode x, TNode s, TNode t) const
{
  return impl(
      d_nm,
      andn(d_nm, eq(d_nm, s, ones(d_nm, x)), distinct(d_nm, x, ones(d_nm, x))),
      eq(d_nm, t, zero(d_nm, x)));
}

// 7: (not (bvult x (bvneg (bvand (bvneg s) (bvneg t)))))
template <>
Node Lemma<LemmaKind::UDIV_REF7>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, x, bvneg(d_nm, bvand(d_nm, bvneg(d_nm, s), bvneg(d_nm, t))));
}

// 8: (not (bvult (bvneg (bvor s 1)) t))
template <>
Node Lemma<LemmaKind::UDIV_REF8>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, bvneg(d_nm, bvor(d_nm, s, one(d_nm, x))), t);
}

// 9: (not (= t (bvneg (bvand s (bvnot x)))))
template <>
Node Lemma<LemmaKind::UDIV_REF9>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(d_nm, t, bvneg(d_nm, bvand(d_nm, s, bvnot(d_nm, x))));
}

// 10: (not (= (bvor s t) (bvand x (bvnot 1))))
template <>
Node Lemma<LemmaKind::UDIV_REF10>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, bvor(d_nm, s, t), bvand(d_nm, x, bvnot(d_nm, one(d_nm, x))));
}

// 11: (not (= (bvor s 1) (bvand x (bvnot t))))
template <>
Node Lemma<LemmaKind::UDIV_REF11>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, bvor(d_nm, s, one(d_nm, x)), bvand(d_nm, x, bvnot(d_nm, t)));
}

// 12: (not (bvult (bvand x (bvneg t)) (bvand s t)))
template <>
Node Lemma<LemmaKind::UDIV_REF12>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, bvand(d_nm, x, bvneg(d_nm, t)), bvand(d_nm, s, t));
}

// 13: (not (bvult s (bvlshr x t)))
template <>
Node Lemma<LemmaKind::UDIV_REF13>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, s, bvlshr(d_nm, x, t));
}

// 14: (not (bvult x (bvshl (bvlshr s (bvshl s t)) 1)))
template <>
Node Lemma<LemmaKind::UDIV_REF14>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, x, bvshl(d_nm, bvlshr(d_nm, s, bvshl(d_nm, s, t)), one(d_nm, x)));
}

// 15: (not (bvult x (bvlshr (bvshl t 1) (bvshl t s))))
template <>
Node Lemma<LemmaKind::UDIV_REF15>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, x, bvlshr(d_nm, bvshl(d_nm, t, one(d_nm, x)), bvshl(d_nm, t, s)));
}

// 16: (not (bvult t (bvshl (bvlshr x s) 1)))
template <>
Node Lemma<LemmaKind::UDIV_REF16>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, t, bvshl(d_nm, bvlshr(d_nm, x, s), one(d_nm, x)));
}

// 17: (not (bvult x (bvand (bvor x t) (bvshl s 1))))
template <>
Node Lemma<LemmaKind::UDIV_REF17>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, x, bvand(d_nm, bvor(d_nm, x, t), bvshl(d_nm, s, one(d_nm, x))));
}

// 18: (not (bvult x (bvand (bvor x s) (bvshl t 1))))
template <>
Node Lemma<LemmaKind::UDIV_REF18>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, x, bvand(d_nm, bvor(d_nm, x, s), bvshl(d_nm, t, one(d_nm, x))));
}

// 19: (not (= (bvlshr x t) (bvor s t)))
template <>
Node Lemma<LemmaKind::UDIV_REF19>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(d_nm, bvlshr(d_nm, x, t), bvor(d_nm, s, t));
}

// 20: (not (= s (bvnot (bvlshr s (bvlshr t 1)))))
template <>
Node Lemma<LemmaKind::UDIV_REF20>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(
      d_nm, s, bvnot(d_nm, bvlshr(d_nm, s, bvlshr(d_nm, t, one(d_nm, x)))));
}

// 21: (not (= x (bvnot (bvand x (bvshl t 1)))))
template <>
Node Lemma<LemmaKind::UDIV_REF21>::instance(TNode x,
                                            CVC5_UNUSED TNode s,
                                            TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "UDIV_REF21 is not valid for bit-width 1";
  return distinct(
      d_nm, x, bvnot(d_nm, bvand(d_nm, x, bvshl(d_nm, t, one(d_nm, x)))));
}

// 22: (not (bvult t (bvlshr (bvshl x 1) s)))
template <>
Node Lemma<LemmaKind::UDIV_REF23>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, t, bvlshr(d_nm, bvshl(d_nm, x, one(d_nm, x)), s));
}

// 23: (not (bvult x (bvshl s (bvnot (bvor x t)))))
template <>
Node Lemma<LemmaKind::UDIV_REF24>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, x, bvshl(d_nm, s, bvnot(d_nm, bvor(d_nm, x, t))));
}

// 24: (not (bvult x (bvshl t (bvnot (bvor x s)))))
template <>
Node Lemma<LemmaKind::UDIV_REF25>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, x, bvshl(d_nm, t, bvnot(d_nm, bvor(d_nm, x, s))));
}

// 25: (not (bvult x (bvxor t (bvlshr t (bvlshr s 1)))))
template <>
Node Lemma<LemmaKind::UDIV_REF26>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, x, bvxor(d_nm, t, bvlshr(d_nm, t, bvlshr(d_nm, s, one(d_nm, x)))));
}

// 26: (not (bvult x (bvxor s (bvlshr s (bvlshr t 1)))))
template <>
Node Lemma<LemmaKind::UDIV_REF27>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, x, bvxor(d_nm, s, bvlshr(d_nm, s, bvlshr(d_nm, t, one(d_nm, x)))));
}

// 27: (not (bvult x (bvshl s (bvnot (bvxor x t)))))
template <>
Node Lemma<LemmaKind::UDIV_REF28>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, x, bvshl(d_nm, s, bvnot(d_nm, bvxor(d_nm, x, t))));
}

// 28: (not (bvult x (bvshl t (bvnot (bvxor x s)))))
template <>
Node Lemma<LemmaKind::UDIV_REF29>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, x, bvshl(d_nm, t, bvnot(d_nm, bvxor(d_nm, x, s))));
}

// 29: (not (= x (bvadd t (bvor s (bvadd x s)))))
template <>
Node Lemma<LemmaKind::UDIV_REF30>::instance(TNode x, TNode s, TNode t) const
{
  return distinct(d_nm, x, bvadd(d_nm, t, bvor(d_nm, s, bvadd(d_nm, x, s))));
}

// 30: (not (= x (bvadd t (bvadd 1 (bvshl 1 x)))))
template <>
Node Lemma<LemmaKind::UDIV_REF31>::instance(TNode x,
                                            CVC5_UNUSED TNode s,
                                            TNode t) const
{
  Assert(utils::getSize(x) >= 3) << "UDIV_REF31 is not valid for bit-width < 3";
  Node o = one(d_nm, x);
  return distinct(d_nm, x, bvadd(d_nm, t, bvadd(d_nm, o, bvshl(d_nm, o, x))));
}

// 31: (not (bvult s (bvlshr (bvadd x t) t)))
template <>
Node Lemma<LemmaKind::UDIV_REF32>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, s, bvlshr(d_nm, bvadd(d_nm, x, t), t));
}

// 32: (not (= x (bvadd t (bvadd t (bvor x s)))))
template <>
Node Lemma<LemmaKind::UDIV_REF33>::instance(TNode x, TNode s, TNode t) const
{
  Assert(utils::getSize(x) >= 2) << "UDIV_REF33 is not valid for bit-width 1";
  return distinct(d_nm, x, bvadd(d_nm, t, bvadd(d_nm, t, bvor(d_nm, x, s))));
}

// 33: (not (bvult (bvxor s (bvor x t)) (bvxor t 1)))
template <>
Node Lemma<LemmaKind::UDIV_REF34>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(
      d_nm, bvxor(d_nm, s, bvor(d_nm, x, t)), bvxor(d_nm, t, one(d_nm, x)));
}

// 34: (not (bvult t (bvlshr x (bvsub s 1))))
template <>
Node Lemma<LemmaKind::UDIV_REF36>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, t, bvlshr(d_nm, x, bvsub(d_nm, s, one(d_nm, x))));
}

// 35: (not (bvult (bvsub s 1) (bvlshr x t)))
template <>
Node Lemma<LemmaKind::UDIV_REF37>::instance(TNode x, TNode s, TNode t) const
{
  return bvuge(d_nm, bvsub(d_nm, s, one(d_nm, x)), bvlshr(d_nm, x, t));
}

// 36: (not (= x (bvsub 1 (bvshl x (bvsub x t)))))
template <>
Node Lemma<LemmaKind::UDIV_REF38>::instance(TNode x,
                                            CVC5_UNUSED TNode s,
                                            TNode t) const
{
  Assert(utils::getSize(x) != 2) << "UDIV_REF38 is not valid for bit-width 2";
  return distinct(
      d_nm, x, bvsub(d_nm, one(d_nm, x), bvshl(d_nm, x, bvsub(d_nm, x, t))));
}

/* --- unsigned remainder lemmas ------------------------------------------- */

// 1*: (=> (= s 2^i) (= t (concat 0[w-i] x[i-1:0])))
template <>
Node Lemma<LemmaKind::UREM_POW2>::instance(TNode x,
                                           TNode s,
                                           TNode t,
                                           CVC5_UNUSED TNode xval,
                                           TNode sval,
                                           CVC5_UNUSED TNode tval) const
{
  Assert(sval.isConst());
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
Node Lemma<LemmaKind::UREM_REF1>::instance(TNode x,
                                           CVC5_UNUSED TNode s,
                                           TNode t) const
{
  return impl(d_nm, distinct(d_nm, s, zero(d_nm, x)), bvult(d_nm, t, s));
}

// 3*: (=> (= x 0) (= t 0))
template <>
Node Lemma<LemmaKind::UREM_REF2>::instance(TNode x,
                                           CVC5_UNUSED TNode s,
                                           TNode t) const
{
  return impl(d_nm, eq(d_nm, x, zero(d_nm, x)), eq(d_nm, t, zero(d_nm, x)));
}

// 4*: (=> (= s 0) (= t x))
template <>
Node Lemma<LemmaKind::UREM_REF3>::instance(TNode x,
                                           CVC5_UNUSED TNode s,
                                           TNode t) const
{
  return impl(d_nm, eq(d_nm, s, zero(d_nm, x)), eq(d_nm, t, x));
}

// 5*: (=> (= s x) (= t 0))
template <>
Node Lemma<LemmaKind::UREM_REF4>::instance(TNode x,
                                           CVC5_UNUSED TNode s,
                                           TNode t) const
{
  return impl(d_nm, eq(d_nm, s, x), eq(d_nm, t, zero(d_nm, x)));
}

// 6*: (=> (bvult x s) (= t x))
template <>
Node Lemma<LemmaKind::UREM_REF5>::instance(TNode x,
                                           CVC5_UNUSED TNode s,
                                           TNode t) const
{
  return impl(d_nm, bvult(d_nm, x, s), eq(d_nm, t, x));
}

// 7*: (bvuge (bvnot (bvneg s)) t)
template <>
Node Lemma<LemmaKind::UREM_REF6>::instance(CVC5_UNUSED TNode x,
                                           TNode s,
                                           TNode t) const
{
  return bvuge(d_nm, bvnot(d_nm, bvneg(d_nm, s)), t);
}

// 8: (= x (bvand x (bvor s (bvor t (bvneg s)))))
template <>
Node Lemma<LemmaKind::UREM_REF7>::instance(TNode x,
                                           CVC5_UNUSED TNode s,
                                           TNode t) const
{
  return eq(
      d_nm, x, bvand(d_nm, x, bvor(d_nm, s, bvor(d_nm, t, bvneg(d_nm, s)))));
}

// 9: (not (bvult x (bvor t (bvand x s))))
template <>
Node Lemma<LemmaKind::UREM_REF8>::instance(TNode x,
                                           CVC5_UNUSED TNode s,
                                           TNode t) const
{
  return bvuge(d_nm, x, bvor(d_nm, t, bvand(d_nm, x, s)));
}

// 10: (not (= 1 (bvand t (bvnot (bvor x s)))))
template <>
Node Lemma<LemmaKind::UREM_REF9>::instance(TNode x,
                                           CVC5_UNUSED TNode s,
                                           TNode t) const
{
  return distinct(
      d_nm, one(d_nm, x), bvand(d_nm, t, bvnot(d_nm, bvor(d_nm, x, s))));
}

// 11: (not (= t (bvor (bvnot x) (bvneg s))))
template <>
Node Lemma<LemmaKind::UREM_REF10>::instance(TNode x,
                                            CVC5_UNUSED TNode s,
                                            TNode t) const
{
  return distinct(d_nm, t, bvor(d_nm, bvnot(d_nm, x), bvneg(d_nm, s)));
}

// 12: (not (bvult (bvand t (bvor x s)) (bvand t 1)))
template <>
Node Lemma<LemmaKind::UREM_REF11>::instance(TNode x,
                                            CVC5_UNUSED TNode s,
                                            TNode t) const
{
  return bvuge(
      d_nm, bvand(d_nm, t, bvor(d_nm, x, s)), bvand(d_nm, t, one(d_nm, x)));
}

// 13: (not (= x (bvor (bvneg x) (bvneg (bvnot t)))))
template <>
Node Lemma<LemmaKind::UREM_REF12>::instance(TNode x,
                                            CVC5_UNUSED TNode s,
                                            TNode t) const
{
  Assert(utils::getSize(x) >= 3) << "UREM_REF12 is not valid for bit-width < 3";
  return distinct(
      d_nm, x, bvor(d_nm, bvneg(d_nm, x), bvneg(d_nm, bvnot(d_nm, t))));
}

// 14: (not (bvult (bvadd x (bvneg s)) t))
template <>
Node Lemma<LemmaKind::UREM_REF13>::instance(TNode x,
                                            CVC5_UNUSED TNode s,
                                            TNode t) const
{
  return bvuge(d_nm, bvadd(d_nm, x, bvneg(d_nm, s)), t);
}

// 15: (not (bvult (bvxor (bvneg s) (bvor x s)) t))
template <>
Node Lemma<LemmaKind::UREM_REF14>::instance(TNode x,
                                            CVC5_UNUSED TNode s,
                                            TNode t) const
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
  switch (kind)
  {
    case Kind::BITVECTOR_MULT: return d_mul;
    case Kind::BITVECTOR_UDIV: return d_udiv;
    case Kind::BITVECTOR_UREM: return d_urem;
    default: return d_empty;
  }
}

void LemmaRegistry::initMul(NodeManager* nm)
{
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_POW2>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_NEG_POW2>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_IC>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_ODD>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_REF1>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_REF3>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_REFN3>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_REFN4>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_REFN5>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_REFN6>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_REF14>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_REF15>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_REFN9>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_REF18>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_REFN11>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_REFN12>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_REFN13>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_REF13>>(nm));
  d_mul.push_back(std::make_unique<Lemma<LemmaKind::MUL_REF12>>(nm));
}

void LemmaRegistry::initUdiv(NodeManager* nm)
{
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_POW2>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF1>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF2>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF3>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF4>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF5>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF6>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF7>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF8>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF9>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF10>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF11>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF12>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF13>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF14>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF15>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF16>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF17>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF18>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF19>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF20>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF21>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF23>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF24>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF25>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF26>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF27>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF28>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF29>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF30>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF31>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF32>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF33>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF34>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF36>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF37>>(nm));
  d_udiv.push_back(std::make_unique<Lemma<LemmaKind::UDIV_REF38>>(nm));
}

void LemmaRegistry::initUrem(NodeManager* nm)
{
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM_POW2>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM_REF1>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM_REF2>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM_REF3>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM_REF4>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM_REF5>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM_REF6>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM_REF7>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM_REF8>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM_REF9>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM_REF10>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM_REF11>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM_REF12>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM_REF13>>(nm));
  d_urem.push_back(std::make_unique<Lemma<LemmaKind::UREM_REF14>>(nm));
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
    case LemmaKind::MUL_POW2: return "MUL_POW2";
    case LemmaKind::MUL_NEG_POW2: return "MUL_NEG_POW2";
    case LemmaKind::MUL_IC: return "MUL_IC";
    case LemmaKind::MUL_ODD: return "MUL_ODD";
    case LemmaKind::MUL_REF1: return "MUL_REF1";
    case LemmaKind::MUL_REF3: return "MUL_REF3";
    case LemmaKind::MUL_REFN3: return "MUL_REFN3";
    case LemmaKind::MUL_REFN4: return "MUL_REFN4";
    case LemmaKind::MUL_REFN5: return "MUL_REFN5";
    case LemmaKind::MUL_REFN6: return "MUL_REFN6";
    case LemmaKind::MUL_REF14: return "MUL_REF14";
    case LemmaKind::MUL_REF15: return "MUL_REF15";
    case LemmaKind::MUL_REFN9: return "MUL_REFN9";
    case LemmaKind::MUL_REF18: return "MUL_REF18";
    case LemmaKind::MUL_REFN11: return "MUL_REFN11";
    case LemmaKind::MUL_REFN12: return "MUL_REFN12";
    case LemmaKind::MUL_REFN13: return "MUL_REFN13";
    case LemmaKind::MUL_REF13: return "MUL_REF13";
    case LemmaKind::MUL_REF12: return "MUL_REF12";

    case LemmaKind::UDIV_POW2: return "UDIV_POW2";
    case LemmaKind::UDIV_REF1: return "UDIV_REF1";
    case LemmaKind::UDIV_REF2: return "UDIV_REF2";
    case LemmaKind::UDIV_REF3: return "UDIV_REF3";
    case LemmaKind::UDIV_REF4: return "UDIV_REF4";
    case LemmaKind::UDIV_REF5: return "UDIV_REF5";
    case LemmaKind::UDIV_REF6: return "UDIV_REF6";
    case LemmaKind::UDIV_REF7: return "UDIV_REF7";
    case LemmaKind::UDIV_REF8: return "UDIV_REF8";
    case LemmaKind::UDIV_REF9: return "UDIV_REF9";
    case LemmaKind::UDIV_REF10: return "UDIV_REF10";
    case LemmaKind::UDIV_REF11: return "UDIV_REF11";
    case LemmaKind::UDIV_REF12: return "UDIV_REF12";
    case LemmaKind::UDIV_REF13: return "UDIV_REF13";
    case LemmaKind::UDIV_REF14: return "UDIV_REF14";
    case LemmaKind::UDIV_REF15: return "UDIV_REF15";
    case LemmaKind::UDIV_REF16: return "UDIV_REF16";
    case LemmaKind::UDIV_REF17: return "UDIV_REF17";
    case LemmaKind::UDIV_REF18: return "UDIV_REF18";
    case LemmaKind::UDIV_REF19: return "UDIV_REF19";
    case LemmaKind::UDIV_REF20: return "UDIV_REF20";
    case LemmaKind::UDIV_REF21: return "UDIV_REF21";
    case LemmaKind::UDIV_REF23: return "UDIV_REF23";
    case LemmaKind::UDIV_REF24: return "UDIV_REF24";
    case LemmaKind::UDIV_REF25: return "UDIV_REF25";
    case LemmaKind::UDIV_REF26: return "UDIV_REF26";
    case LemmaKind::UDIV_REF27: return "UDIV_REF27";
    case LemmaKind::UDIV_REF28: return "UDIV_REF28";
    case LemmaKind::UDIV_REF29: return "UDIV_REF29";
    case LemmaKind::UDIV_REF30: return "UDIV_REF30";
    case LemmaKind::UDIV_REF31: return "UDIV_REF31";
    case LemmaKind::UDIV_REF32: return "UDIV_REF32";
    case LemmaKind::UDIV_REF33: return "UDIV_REF33";
    case LemmaKind::UDIV_REF34: return "UDIV_REF34";
    case LemmaKind::UDIV_REF36: return "UDIV_REF36";
    case LemmaKind::UDIV_REF37: return "UDIV_REF37";
    case LemmaKind::UDIV_REF38: return "UDIV_REF38";

    case LemmaKind::UREM_POW2: return "UREM_POW2";
    case LemmaKind::UREM_REF1: return "UREM_REF1";
    case LemmaKind::UREM_REF2: return "UREM_REF2";
    case LemmaKind::UREM_REF3: return "UREM_REF3";
    case LemmaKind::UREM_REF4: return "UREM_REF4";
    case LemmaKind::UREM_REF5: return "UREM_REF5";
    case LemmaKind::UREM_REF6: return "UREM_REF6";
    case LemmaKind::UREM_REF7: return "UREM_REF7";
    case LemmaKind::UREM_REF8: return "UREM_REF8";
    case LemmaKind::UREM_REF9: return "UREM_REF9";
    case LemmaKind::UREM_REF10: return "UREM_REF10";
    case LemmaKind::UREM_REF11: return "UREM_REF11";
    case LemmaKind::UREM_REF12: return "UREM_REF12";
    case LemmaKind::UREM_REF13: return "UREM_REF13";
    case LemmaKind::UREM_REF14: return "UREM_REF14";
  }
  return "?";
}
}  // namespace std
