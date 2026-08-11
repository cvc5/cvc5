/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Refinement lemma schemes for the bit-vector arithmetic abstraction
 * (CEGAR) strategy.
 *
 * These are a direct port of the lemma schemes used by Bitwuzla's abstraction
 * module, as described in "Scalable Bit-Blasting with Abstractions" (Niemetz,
 * Preiner, Zohar, CAV 2024), Table 2.
 *
 * For an abstracted arithmetic term `t = x <op> s` (<op> in {bvmul, bvudiv,
 * bvurem}), each lemma `l[x,s,t]` is a sound over-approximation of the
 * operator, i.e. `(x <op> s = t) => l` is T_BV-valid. Hence every lemma may be
 * asserted permanently to constrain the fresh abstraction constant `t` without
 * removing real models.
 *
 * Ported from Bitwuzla's implementation of the abstraction lemmas, see
 * https://github.com/bitwuzla/bitwuzla/blob/main/src/solver/abstract/abstraction_lemmas.h
 * (Copyright (C) 2022 by the Bitwuzla authors, MIT license).
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__ABSTRACT__ABSTRACTION_LEMMAS_H
#define CVC5__THEORY__BV__ABSTRACT__ABSTRACTION_LEMMAS_H

#include <cstdint>
#include <memory>
#include <ostream>
#include <vector>

#include "expr/kind.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace bv::abstract {

/* -------------------------------------------------------------------------- */

/** The kind of the bit-vector arithmetic refinement lemma. */
enum class LemmaKind : uint32_t
{
  // Multiplication (x * s = t)
  MUL1_POW2,      // 1*: (=> (= x 2^i) (= t (bvshl s i)))
  MUL2_NEG_POW2,  // 2*: (=> (= x -2^i) (= t (bvshl (bvneg s) i)))
  MUL3_IC,        // 3*: (= (bvand (bvor (bvneg s) s) t) t)
  MUL4_ODD,       // 4*: (= ((_ extract 0 0) t) (bvand x[0] s[0]))
  MUL5,           //  5: (not (= s (bvnot (bvor t (bvand 1 (bvor x s))))))
  MUL6,           //  6: (not (= (bvand x t) (bvor s (bvnot t))))
  MUL7,           //  7: (not (= t (bvshl (bvor s 1) (bvshl t x))))
  MUL8,           //  8: (= s (bvshl s (bvand x (bvlshr 1 t))))
  MUL9,           //  9: (bvuge t (bvand 1 (bvlshr (bvand x s) 1)))
  MUL10,          // 10: (not (= x (bvxor 1 (bvshl x (bvxor s t)))))
  MUL11,          // 11: (not (= t (bvor 1 (bvnot (bvxor x s)))))
  MUL12,          // 12: (not (= t (bvor (bvnot 1) (bvxor x s))))
  MUL13,          // 13: (not (= x (bvsub (bvshl x (bvadd s t)) 1)))
  MUL14,          // 14: (not (= x (bvsub 1 (bvshl x (bvsub s t)))))
  MUL15,          // 15: (not (= s (bvadd 1 (bvshl s (bvsub t x)))))
  MUL16,          // 16: (not (= s (bvsub 1 (bvshl s (bvsub t x)))))
  MUL17,          // 17: (not (= s (bvadd 1 (bvshl s (bvsub x t)))))
  MUL18,          // 18: (not (= t (bvor 1 (bvadd x s))))
  MUL19,          // 19: (not (= x (bvnot (bvshl x (bvadd s t)))))

  // Unsigned division (x udiv s = t)
  UDIV1_POW2,  // 1*: (=> (= s 2^i) (= t (bvlshr x i)))
  UDIV37,      //  -: (=> (= s 1) (= t x))
  UDIV2,       // 2*: (=> (and (= s x) (distinct s 0)) (= t 1))
  UDIV3,       // 3*: (=> (= s 0) (= t (bvnot 0)))
  UDIV4,       // 4*: (=> (and (= x 0) (distinct s 0)) (= t 0))
  UDIV5,       // 5*: (=> (distinct s 0) (bvule t x))
  UDIV6,       // 6*: (=> (and (= s ~0) (distinct x ~0)) (= t 0))
  UDIV7,       //  7: (not (bvult x (bvneg (bvand (bvneg s) (bvneg t)))))
  UDIV8,       //  8: (not (bvult (bvneg (bvor s 1)) t))
  UDIV9,       //  9: (not (= t (bvneg (bvand s (bvnot x)))))
  UDIV10,      // 10: (not (= (bvor s t) (bvand x (bvnot 1))))
  UDIV11,      // 11: (not (= (bvor s 1) (bvand x (bvnot t))))
  UDIV12,      // 12: (not (bvult (bvand x (bvneg t)) (bvand s t)))
  UDIV13,      // 13: (not (bvult s (bvlshr x t)))
  UDIV14,      // 14: (not (bvult x (bvshl (bvlshr s (bvshl s t)) 1)))
  UDIV15,      // 15: (not (bvult x (bvlshr (bvshl t 1) (bvshl t s))))
  UDIV16,      // 16: (not (bvult t (bvshl (bvlshr x s) 1)))
  UDIV17,      // 17: (not (bvult x (bvand (bvor x t) (bvshl s 1))))
  UDIV18,      // 18: (not (bvult x (bvand (bvor x s) (bvshl t 1))))
  UDIV19,      // 19: (not (= (bvlshr x t) (bvor s t)))
  UDIV20,      // 20: (not (= s (bvnot (bvlshr s (bvlshr t 1)))))
  UDIV21,      // 21: (not (= x (bvnot (bvand x (bvshl t 1)))))
  UDIV22,      // 22: (not (bvult t (bvlshr (bvshl x 1) s)))
  UDIV23,      // 23: (not (bvult x (bvshl s (bvnot (bvor x t)))))
  UDIV24,      // 24: (not (bvult x (bvshl t (bvnot (bvor x s)))))
  UDIV25,      // 25: (not (bvult x (bvxor t (bvlshr t (bvlshr s 1)))))
  UDIV26,      // 26: (not (bvult x (bvxor s (bvlshr s (bvlshr t 1)))))
  UDIV27,      // 27: (not (bvult x (bvshl s (bvnot (bvxor x t)))))
  UDIV28,      // 28: (not (bvult x (bvshl t (bvnot (bvxor x s)))))
  UDIV29,      // 29: (not (= x (bvadd t (bvor s (bvadd x s)))))
  UDIV30,      // 30: (not (= x (bvadd t (bvadd 1 (bvshl 1 x)))))
  UDIV31,      // 31: (not (bvult s (bvlshr (bvadd x t) t)))
  UDIV32,      // 32: (not (= x (bvadd t (bvadd t (bvor x s)))))
  UDIV33,      // 33: (not (bvult (bvxor s (bvor x t)) (bvxor t 1)))
  UDIV34,      // 34: (not (bvult t (bvlshr x (bvsub s 1))))
  UDIV35,      // 35: (not (bvult (bvsub s 1) (bvlshr x t)))
  UDIV36,      // 36: (not (= x (bvsub 1 (bvshl x (bvsub x t)))))

  // Unsigned remainder (x urem s = t)
  UREM1_POW2,  // 1*: (=> (= s 2^i) (= t (concat 0[w-i] x[i-1:0])))
  UREM2,       // 2*: (=> (distinct s 0) (bvult t s))
  UREM3,       // 3*: (=> (= x 0) (= t 0))
  UREM4,       // 4*: (=> (= s 0) (= t x))
  UREM5,       // 5*: (=> (= s x) (= t 0))
  UREM6,       // 6*: (=> (bvult x s) (= t x))
  UREM7,       // 7*: (bvuge (bvnot (bvneg s)) t)
  UREM8,       //  8: (= x (bvand x (bvor s (bvor t (bvneg s)))))
  UREM9,       //  9: (not (bvult x (bvor t (bvand x s))))
  UREM10,      // 10: (not (= 1 (bvand t (bvnot (bvor x s)))))
  UREM11,      // 11: (not (= t (bvor (bvnot x) (bvneg s))))
  UREM12,      // 12: (not (bvult (bvand t (bvor x s)) (bvand t 1)))
  UREM13,      // 13: (not (= x (bvor (bvneg x) (bvneg (bvnot t)))))
  UREM14,      // 14: (not (bvult (bvadd x (bvneg s)) t))
  UREM15,      // 15: (not (bvult (bvxor (bvneg s) (bvor x s)) t))
};

std::ostream& operator<<(std::ostream& os, LemmaKind kind);

/* -------------------------------------------------------------------------- */

/** Base class for bit-vector abstraction lemmas. */
class AbstractionLemma
{
 public:
  /** Constructor. */
  AbstractionLemma(NodeManager* nm, LemmaKind kind) : d_nm(nm), d_kind(kind) {}
  /** Destructor. */
  virtual ~AbstractionLemma() {}

  /** @return The kind of this lemma. */
  LemmaKind getKind() const { return d_kind; }

  /**
   * For a bit-vector arithmetic term (op x s) that is abstracted with t,
   * determine the instantiation of a purely symbolic lemma.
   *
   * @param x     The x operand.
   * @param s     The s operand.
   * @param t     The t operand.
   * @return The instantiation of the lemma, or the null node if this scheme
   *         depends on model values (see the overload below).
   */
  virtual Node instance(TNode x, TNode s, TNode t) const = 0;

  /**
   * For a bit-vector arithmetic term (op x s) that is abstracted with t,
   * determine the instantiation of a lemma that depends on the model
   * values of x and/or s.
   *
   * @param x    The x operand.
   * @param s    The s operand.
   * @param t    The t operand.
   * @param xval The model value of x, must be a bit-vector value.
   * @param sval The model value of s, must be a bit-vector value.
   * @return The instantiation of the lemma, or the null node if this scheme is
   *         purely symbolic (see the overload above), or if the model values
   *         do not match the pattern of this scheme (e.g., xval is not a power
   *         of two for MUL1_POW2).
   */
  virtual Node instance(
      TNode x, TNode s, TNode t, TNode xval, TNode sval) const = 0;

 protected:
  /** The associated node manager. */
  NodeManager* d_nm;
  /** The lemma kind. */
  LemmaKind d_kind;
};

template <enum LemmaKind K>
class Lemma : public AbstractionLemma
{
 public:
  Lemma(NodeManager* nm) : AbstractionLemma(nm, K) {}
  ~Lemma() {}
  Node instance(CVC5_UNUSED TNode x,
                CVC5_UNUSED TNode s,
                CVC5_UNUSED TNode t) const override
  {
    return Node();
  }
  Node instance(CVC5_UNUSED TNode x,
                CVC5_UNUSED TNode s,
                CVC5_UNUSED TNode t,
                CVC5_UNUSED TNode xval,
                CVC5_UNUSED TNode sval) const override
  {
    return Node();
  }
};

/**
 * Registry of all refinement lemma schemes, grouped per abstracted operator and
 * ordered by refinement tier (the order in which they should be checked).
 */
class LemmaRegistry
{
 public:
  explicit LemmaRegistry(NodeManager* nm);

  /**
   * @return The lemma scheme as an ordered list of lemmas for the given kind
   *         (BITVECTOR_MULT, BITVECTOR_UDIV or BITVECTOR_UREM). Returns an
   *          empty list for any other kind.
   */
  const std::vector<std::unique_ptr<AbstractionLemma>>& lemmas(Kind kind) const;

 private:
  void initMul(NodeManager* nm);
  void initUdiv(NodeManager* nm);
  void initUrem(NodeManager* nm);

  std::vector<std::unique_ptr<AbstractionLemma>> d_mul;
  std::vector<std::unique_ptr<AbstractionLemma>> d_udiv;
  std::vector<std::unique_ptr<AbstractionLemma>> d_urem;
};

}  // namespace bv::abstract
}  // namespace theory
}  // namespace cvc5::internal

/* -------------------------------------------------------------------------- */

namespace std {
std::string to_string(cvc5::internal::theory::bv::abstract::LemmaKind kind);
}  // namespace std

/* -------------------------------------------------------------------------- */
#endif
