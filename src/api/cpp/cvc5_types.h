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

#include "cvc5_export.h"

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
  PREPROCESS_SOLVED,
  /**
   * A top-level literal (unit clause) from the preprocessed set of input
   * formulas.
   */
  PREPROCESS,
  /**
   * A literal from the preprocessed set of input formulas that does not
   * occur at top-level after preprocessing.
   *
   * Typically, this is the most interesting category of literals to learn.
   */
  INPUT,
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
  SOLVABLE,
  /**
   * An internal literal that can be made into a constant propagation for an
   * input term.
   *
   * In particular, literals in this category are of the form (= t c) where
   * c is a constant, the preprocessed set of input formulas contains the
   * term t, but not the literal (= t c).
   */
  CONSTANT_PROP,
  /** Any internal literal that does not fall into the above categories. */
  INTERNAL,
  /** Special case for when produce-learned-literals is not set.  */
  UNKNOWN
};
/** Writes a learned literal type to a stream. */
std::ostream& operator<<(std::ostream& out, LearnedLitType ltype);
}

#endif
