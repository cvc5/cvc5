/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Mudathir Mohamed, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common cvc5 types. These types are used internally as well as externally and
 * the language bindings are generated automatically.
 */

#include <cvc5/cvc5_export.h>

#ifndef CVC5__API__CVC5_TYPES_H
#define CVC5__API__CVC5_TYPES_H

#include <iosfwd>

namespace cvc5 {

/**
 * The different reasons for returning an "unknown" result.
 */
enum UnknownExplanation
{
  /**
   * Full satisfiability check required (e.g., if only preprocessing was
   * performed).
   */
  REQUIRES_FULL_CHECK,
  /** Incomplete theory solver. */
  INCOMPLETE,
  /** Time limit reached. */
  TIMEOUT,
  /** Resource limit reached. */
  RESOURCEOUT,
  /** Memory limit reached. */
  MEMOUT,
  /** Solver was interrupted. */
  INTERRUPTED,
  /** Unsupported feature encountered. */
  UNSUPPORTED,
  /** Other reason. */
  OTHER,
  /** Requires another satisfiability check */
  REQUIRES_CHECK_AGAIN,
  /** No specific reason given. */
  UNKNOWN_REASON
};

/**
 * Serialize an UnknownExplanation to given stream.
 * @param out the output stream
 * @param e the explanation to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, UnknownExplanation e) CVC5_EXPORT;

/**
 * Rounding modes for floating-point numbers.
 *
 * For many floating-point operations, infinitely precise results may not be
 * representable with the number of available bits. Thus, the results are
 * rounded in a certain way to one of the representable floating-point numbers.
 *
 * \verbatim embed:rst:leading-asterisk
 * These rounding modes directly follow the SMT-LIB theory for floating-point
 * arithmetic, which in turn is based on IEEE Standard 754 :cite:`IEEE754`.
 * The rounding modes are specified in Sections 4.3.1 and 4.3.2 of the IEEE
 * Standard 754.
 * \endverbatim
 */
enum RoundingMode
{
  /**
   * Round to the nearest even number.
   *
   * If the two nearest floating-point numbers bracketing an unrepresentable
   * infinitely precise result are equally near, the one with an even least
   * significant digit will be delivered.
   */
  ROUND_NEAREST_TIES_TO_EVEN,
  /**
   * Round towards positive infinity (SMT-LIB: ``+oo``).
   *
   * The result shall be the format's floating-point number (possibly ``+oo``)
   * closest to and no less than the infinitely precise result.
   */
  ROUND_TOWARD_POSITIVE,
  /**
   * Round towards negative infinity (``-oo``).
   *
   * The result shall be the format's floating-point number (possibly ``-oo``)
   * closest to and no less than the infinitely precise result.
   */
  ROUND_TOWARD_NEGATIVE,
  /**
   * Round towards zero.
   *
   * The result shall be the format's floating-point number closest to and no
   * greater in magnitude than the infinitely precise result.
   */
  ROUND_TOWARD_ZERO,
  /**
   * Round to the nearest number away from zero.
   *
   * If the two nearest floating-point numbers bracketing an unrepresentable
   * infinitely precise result are equally near, the one with larger magnitude
   * will be selected.
   */
  ROUND_NEAREST_TIES_TO_AWAY,
};

}  // namespace cvc5

namespace cvc5::modes {

/**
 * Mode for blocking models.
 *
 * Specifies how models are blocked in Solver::blockModel and
 * Solver::blockModelValues.
 */
enum BlockModelsMode
{
  /** Block models based on the SAT skeleton. */
  LITERALS,
  /** Block models based on the concrete model values for the free variables. */
  VALUES
};
/** Writes a block models mode to a stream. */
std::ostream& operator<<(std::ostream& out, BlockModelsMode bmode) CVC5_EXPORT;

/**
 * Types of learned literals.
 *
 * Specifies categories of literals learned for the method
 * Solver::getLearnedLiterals.
 *
 * Note that a literal may conceptually belong to multiple categories. We
 * classify literals based on the first criteria in this list that they meet.
 */
enum LearnedLitType
{
  /**
   * An equality that was turned into a substitution during preprocessing.
   *
   * In particular, literals in this category are of the form (= x t) where
   * x does not occur in t.
   */
  LEARNED_LIT_PREPROCESS_SOLVED,
  /**
   * A top-level literal (unit clause) from the preprocessed set of input
   * formulas.
   */
  LEARNED_LIT_PREPROCESS,
  /**
   * A literal from the preprocessed set of input formulas that does not
   * occur at top-level after preprocessing.
   *
   * Typically, this is the most interesting category of literals to learn.
   */
  LEARNED_LIT_INPUT,
  /**
   * An internal literal that is solvable for an input variable.
   *
   * In particular, literals in this category are of the form (= x t) where
   * x does not occur in t, the preprocessed set of input formulas contains the
   * term x, but not the literal (= x t).
   *
   * Note that solvable literals can be turned into substitutions during
   * preprocessing.
   */
  LEARNED_LIT_SOLVABLE,
  /**
   * An internal literal that can be made into a constant propagation for an
   * input term.
   *
   * In particular, literals in this category are of the form (= t c) where
   * c is a constant, the preprocessed set of input formulas contains the
   * term t, but not the literal (= t c).
   */
  LEARNED_LIT_CONSTANT_PROP,
  /** Any internal literal that does not fall into the above categories. */
  LEARNED_LIT_INTERNAL,
  /** Special case for when produce-learned-literals is not set.  */
  LEARNED_LIT_UNKNOWN
};
/** Writes a learned literal type to a stream. */
std::ostream& operator<<(std::ostream& out, LearnedLitType ltype) CVC5_EXPORT;

/**
 * Components to include in a proof.
 */
enum ProofComponent
{
  /**
   * Proofs of G1 ... Gn whose free assumptions are a subset of
   * F1, ... Fm, where:
   * - G1, ... Gn are the preprocessed input formulas,
   * - F1, ... Fm are the input formulas.
   *
   * Note that G1 ... Gn may be arbitrary formulas, not necessarily clauses.
   */
  PROOF_COMPONENT_RAW_PREPROCESS,
  /**
   * Proofs of Gu1 ... Gun whose free assumptions are Fu1, ... Fum,
   * where:
   * - Gu1, ... Gun are clauses corresponding to input formulas used in the SAT
   * proof,
   * - Fu1, ... Fum is the subset of the input formulas that are used in the SAT
   * proof (i.e. the unsat core).
   *
   * Note that Gu1 ... Gun are clauses that are added to the SAT solver before
   * its main search.
   *
   * Only valid immediately after an unsat response.
   */
  PROOF_COMPONENT_PREPROCESS,
  /**
   * A proof of false whose free assumptions are Gu1, ... Gun, L1 ... Lk,
   * where:
   * - Gu1, ... Gun, is a set of clauses corresponding to input formulas,
   * - L1, ..., Lk is a set of clauses corresponding to theory lemmas.
   *
   * Only valid immediately after an unsat response.
   */
  PROOF_COMPONENT_SAT,
  /**
   * Proofs of L1 ... Lk where:
   *- L1, ..., Lk are clauses corresponding to theory lemmas used in the SAT
   * proof.
   *
   * In contrast to proofs given for preprocess, L1 ... Lk are clauses that are
   * added to the SAT solver after its main search.
   *
   * Only valid immediately after an unsat response.
   */
  PROOF_COMPONENT_THEORY_LEMMAS,
  /**
   * A proof of false whose free assumptions are a subset of the input formulas
   * F1, ... Fm.
   *
   * Only valid immediately after an unsat response.
   */
  PROOF_COMPONENT_FULL,
};
/** Writes a proof component identifier to a stream. */
std::ostream& operator<<(std::ostream& out, ProofComponent pc) CVC5_EXPORT;

/**
 * Find synthesis targets, used as an argument to Solver::findSynth. These
 * specify various kinds of terms that can be found by this method.
 */
enum FindSynthTarget
{
  /**
   * Find the next term in the enumeration of the target grammar.
   */
  FIND_SYNTH_TARGET_ENUM,
  /**
   * Find a pair of terms (t,s) in the target grammar which are equivalent
   * but do not rewrite to the same term in the given rewriter
   * (--sygus-rewrite=MODE). If so, the equality (= t s) is returned by
   * findSynth.
   *
   * This can be used to synthesize rewrite rules. Note if the rewriter is set
   * to none (--sygus-rewrite=none), this indicates a possible rewrite when
   * implementing a rewriter from scratch.
   */
  FIND_SYNTH_TARGET_REWRITE,
  /**
   * Find a term t in the target grammar which rewrites to a term s that is
   * not equivalent to it. If so, the equality (= t s) is returned by
   * findSynth.
   *
   * This can be used to test the correctness of the given rewriter. Any
   * returned rewrite indicates an unsoundness in the given rewriter.
   */
  FIND_SYNTH_TARGET_REWRITE_UNSOUND,
  /**
   * Find a rewrite between pairs of terms (t,s) that are matchable with terms
   * in the input assertions where t and s are equivalent but do not rewrite
   * to the same term in the given rewriter (--sygus-rewrite=MODE).
   *
   * This can be used to synthesize rewrite rules that apply to the current
   * problem.
   */
  FIND_SYNTH_TARGET_REWRITE_INPUT,
  /**
   * Find a query over the given grammar. If the given grammar generates terms
   * that are not Boolean, we consider equalities over terms from the given
   * grammar.
   *
   * The algorithm for determining which queries to generate is configured by
   * --sygus-query-gen=MODE.
   */
  FIND_SYNTH_TARGET_QUERY
};
/** Writes a synthesis find target identifier to a stream. */
std::ostream& operator<<(std::ostream& out, FindSynthTarget fst) CVC5_EXPORT;

}  // namespace cvc5::modes

#endif
