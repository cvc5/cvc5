/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Trust identifier enumeration
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__TRUST_ID_H
#define CVC5__PROOF__TRUST_ID_H

#include "expr/node.h"

namespace cvc5::internal {

/**
 * Identifiers for trusted steps in proofs.
 */
enum class TrustId : uint32_t
{
  NONE,
  /** Assertions of the preprocessed input clauses */
  PREPROCESSED_INPUT,
  /** A lemma sent by a theory without a proof */
  THEORY_LEMMA,
  /**
   * A step proving false, used as a trust step when the prop engine is not SAT
   * proof producing (--proof-mode=pp-only).
   */
  SMT_REFUTATION,
  /**
   * An internal inference made by a theory without a proof. These are split
   * per theory, and introduced as needed.
   */
  THEORY_INFERENCE_ARITH,
  THEORY_INFERENCE_ARRAYS,
  THEORY_INFERENCE_DATATYPES,
  THEORY_INFERENCE_SEP,
  THEORY_INFERENCE_SETS,
  THEORY_INFERENCE_STRINGS,
  /** A ppStaticRewrite step */
  PP_STATIC_REWRITE,
  /** A rewrite of the input formula made by a theory during preprocessing
     without a proof */
  THEORY_PREPROCESS,
  /** A lemma added during theory-preprocessing without a proof */
  THEORY_PREPROCESS_LEMMA,
  /** A expanding of definitions of the input formula made without a proof */
  THEORY_EXPAND_DEF,
  /** Specific preprocessing passes */
  /** BvGauss */
  PREPROCESS_BV_GUASS,
  PREPROCESS_BV_GUASS_LEMMA,
  /** BvToBool preprocessing pass */
  PREPROCESS_BV_TO_BOOL,
  /** BvToInt preprocessing pass */
  PREPROCESS_BV_TO_INT,
  PREPROCESS_BV_TO_INT_LEMMA,
  /** BoolToBv preprocessing pass */
  PREPROCESS_BOOL_TO_BV,
  /** Ackermann preprocessing pass */
  PREPROCESS_ACKERMANN,
  PREPROCESS_ACKERMANN_LEMMA,
  /** StaticLearning preprocessing pass */
  PREPROCESS_STATIC_LEARNING_LEMMA,
  /** HoElim preprocessing pass */
  PREPROCESS_HO_ELIM,
  PREPROCESS_HO_ELIM_LEMMA,
  /** BitvectorEagerAtoms preprocessing pass */
  PREPROCESS_BITVECTOR_EAGER_ATOMS,
  /** FfBitsum preprocessing pass */
  PREPROCESS_FF_BITSUM,
  /** FfDisjunctiveBit preprocessing pass */
  PREPROCESS_FF_DISJUNCTIVE_BIT,
  /** FunDefFmf preprocessing pass */
  PREPROCESS_FUN_DEF_FMF,
  /** ITESimp preprocessing pass */
  PREPROCESS_ITE_SIMP,
  /** LearnedRewrite preprocessing pass */
  PREPROCESS_LEARNED_REWRITE,
  PREPROCESS_LEARNED_REWRITE_LEMMA,
  /** MipLibTrick preprocessing pass */
  PREPROCESS_MIPLIB_TRICK,
  PREPROCESS_MIPLIB_TRICK_LEMMA,
  /** NlExtPurify preprocessing pass */
  PREPROCESS_NL_EXT_PURIFY,
  PREPROCESS_NL_EXT_PURIFY_LEMMA,
  /** BvIntroPow2 preprocessing pass */
  PREPROCESS_BV_INTRO_POW2,
  /** ForeignTheoryRewrite preprocessing pass */
  PREPROCESS_FOREIGN_THEORY_REWRITE,
  /** UnconstrainedSimp preprocessing pass */
  PREPROCESS_UNCONSTRAINED_SIMP,
  /** QuantifiersPreprocess preprocessing pass */
  PREPROCESS_QUANTIFIERS_PP,
  /** RealToInt preprocessing pass */
  PREPROCESS_REAL_TO_INT,
  /** SortInferencePass preprocessing pass */
  PREPROCESS_SORT_INFER,
  PREPROCESS_SORT_INFER_LEMMA,
  /** StringsEagerPp preprocessing pass */
  PREPROCESS_STRINGS_EAGER_PP,
  /**
   * We use :math:`\texttt{IRP}_k(poly)` for an IndexedRootPredicate that is
   * defined as the :math:`k`'th root of the polynomial :math:`poly`. Note that
   * :math:`poly` may not be univariate; in this case, the value of
   * :math:`\texttt{IRP}_k(poly)` can only be calculated with respect to a
   * (partial) model for all but one variable of :math:`poly`.
   *
   * A formula :math:`\texttt{Interval}(x_i)` describes that a variable
   * :math:`x_i` is within a particular interval whose bounds are given as IRPs.
   * It is either an open interval or a point interval:
   *
   * .. math::
   *   \texttt{IRP}_k(poly) < x_i < \texttt{IRP}_k(poly)
   *
   *   x_i = \texttt{IRP}_k(poly)
   *
   * A formula :math:`\texttt{Cell}(x_1 \dots x_i)` describes a portion
   * of the real space in the following form:
   *
   * .. math::
   *   \texttt{Interval}(x_1) \land \dots \land \texttt{Interval}(x_i)
   *
   * A cell can also be empty (for :math:`i = 0`).
   *
   * A formula :math:`\texttt{Covering}(x_i)` is a set of intervals, implying
   * that :math:`x_i` can be in neither of these intervals. To be a covering (of
   * the real line), the union of these intervals should be the real numbers.
   *
   * .. math::
   *   \inferrule{\texttt{Cell}, A \mid -}{\bot}
   *
   * A direct interval is generated from an assumption :math:`A` (in variables
   * :math:`x_1 \dots x_i`) over a :math:`\texttt{Cell}(x_1 \dots x_i)`. It
   * derives that :math:`A` evaluates to false over the cell. In the actual
   * algorithm, it means that :math:`x_i` can not be in the topmost interval of
   * the cell.
   */
  ARITH_NL_COVERING_DIRECT,
  /**
   * See ARITH_NL_COVERING_DIRECT for the necessary definitions.
   *
   * .. math::
   *   \inferrule{\texttt{Cell}, \texttt{Covering} \mid -}{\bot}
   *
   * A recursive interval is generated from :math:`\texttt{Covering}(x_i)` over
   * :math:`\texttt{Cell}(x_1 \dots x_{i-1})`. It generates the conclusion that
   * no :math:`x_i` exists that extends the cell and satisfies all assumptions.
   */
  ARITH_NL_COVERING_RECURSIVE,
  /**
   * A conversion between a literal used in the inference id lemma
   * InferenceId::ARITH_NL_COMPARISON and a relation between absolute
   * values as used by ProofRule::ARITH_MULT_ABS_COMPARISON.
   */
  ARITH_NL_COMPARE_LIT_TRANSFORM,
  /** A lemma from the DIO solver */
  ARITH_DIO_LEMMA,
  /** A lemma from the ArithStaticLearner utility */
  ARITH_STATIC_LEARN,
  /** A nonlinear comparison lemma that failed proof reconstruction */
  ARITH_NL_COMPARE_LEMMA,
  /** A conflict coming from the bitblast solver */
  BV_BITBLAST_CONFLICT,
  /** A step from BvPpAssert utility */
  BV_PP_ASSERT,
  /** Diamonds preprocessing in TheoryUf::ppStaticLearn */
  DIAMONDS,
  /** An extended theory rewrite */
  EXT_THEORY_REWRITE,
  /** A rewrite whose proof could not be elaborated */
  REWRITE_NO_ELABORATE,
  /** A flattening rewrite in an equality engine proof */
  FLATTENING_REWRITE,
  /** A proof of an applied substitution that could not be no elaborate */
  SUBS_NO_ELABORATE,
  /** A proof of an applied substitution that could not be reconstructed during
     solving */
  SUBS_MAP,
  /** A proof of a substitution x=t that could not be shown by rewrite */
  SUBS_EQ,
  /** A step of the form (~ s t) = (~ (to_real s) (to_real t)) */
  ARITH_PRED_CAST_TYPE,
  /**
   * Strings -- Regular expression elimination
   *
   * Proves :math:`F = F'` where :math:`F'` is the result of eliminating regular
   * expressions from :math:`F` using the routine
   * :math:`\texttt{strings::RegExpElimination::eliminate}(F, b)` for some
   * :math:`b`.
   *
   * Here, :math:`b` is a Boolean indicating whether we are using aggressive
   * eliminations.
   */
  RE_ELIM,
  /** A quantifiers preprocessing step that was given without a proof */
  QUANTIFIERS_PREPROCESS,
  /** A quantifiers rewriting step for instantiations, e.g. virtual term
     substitution */
  QUANTIFIERS_INST_REWRITE,
  /** A quantifiers from the --sub-cbqi module */
  QUANTIFIERS_SUB_CBQI_LEMMA,
  /** A quantifiers from the nested quantifier elimination module */
  QUANTIFIERS_NESTED_QE_LEMMA,
  /** A rewrite performed at TheoryStrings::ppStaticRewrite */
  STRINGS_PP_STATIC_REWRITE,
  /**
   * An existential corresponding to a witness term introduced e.g. in
   * quantifier instantiation
   */
  VALID_WITNESS,
  /** A subtype elimination step that could not be processed */
  SUBTYPE_ELIMINATION,
  /** A rewrite required for showing a macro theory rewrite */
  MACRO_THEORY_REWRITE_RCONS,
  /**
   * A rewrite required for showing a macro theory rewrite that should not
   * require the use of theory rewrites to prove.
   */
  MACRO_THEORY_REWRITE_RCONS_SIMPLE,
  /** An unproven step from the int-blaster */
  INT_BLASTER,
  /** Untracked sources of trust, which are discouraged */
  /** A rewrite of the input formula by a preprocessing pass without a proof */
  UNKNOWN_PREPROCESS,
  /** A lemma added during preprocessing without a proof */
  UNKNOWN_PREPROCESS_LEMMA,
};
/** Converts a trust id to a string. */
const char* toString(TrustId id);
/** Write a trust id to out */
std::ostream& operator<<(std::ostream& out, TrustId id);
/** Make a trust id node */
Node mkTrustId(NodeManager* nm, TrustId id);
/** get a trust identifier from a node, return false if we fail */
bool getTrustId(TNode n, TrustId& i);

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__METHOD_ID_H */
