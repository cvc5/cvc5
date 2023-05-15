/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Term context utilities.
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__TERM_CONTEXT_H
#define CVC5__EXPR__TERM_CONTEXT_H

#include "expr/node.h"
#include "theory/theory_id.h"

namespace cvc5::internal {

/**
 * This is an abstract class for computing "term context identifiers". A term
 * context identifier is a hash value that identifies some property of the
 * context in which a term occurs. Common examples of the implementation of
 * such a mapping are implemented in the subclasses below.
 *
 * A term context identifier is intended to be information that can be locally
 * computed from the parent's hash, and hence does not rely on maintaining
 * paths.
 *
 * In the below documentation, we write t @ [p] to a term at a given position,
 * where p is a list of indices. For example, the atomic subterms of:
 *   (and P (not Q))
 * are P @ [0] and Q @ [1,0].
 */
class TermContext
{
 public:
  TermContext() {}
  virtual ~TermContext() {}
  /** The default initial value of root terms. */
  virtual uint32_t initialValue() const = 0;
  /**
   * Returns the term context identifier of the index^th child of t, where tval
   * is the term context identifier of t.
   */
  virtual uint32_t computeValue(TNode t, uint32_t tval, size_t index) const = 0;
  /**
   * Returns the term context identifier of the operator of t, where tval
   * is the term context identifier of t.
   */
  virtual uint32_t computeValueOp(TNode t, uint32_t tval) const;
};

/**
 * Remove term formulas (rtf) term context.
 *
 * Computes whether we are inside a term (as opposed to being part of Boolean
 * skeleton) and whether we are inside a quantifier. For example, for:
 *   (and (= a b) (forall ((x Int)) (P x)))
 * we have the following mappings (term -> inTerm,inQuant)
 *   (= a b) @ [0] -> false, false
 *   a @ [0,1] -> true, false
 *   (P x) @ [1,1] -> false, true
 *    x @ [1,1,0] -> true, true
 * Notice that the hash of a child can be computed from the parent's hash only,
 * and hence this can be implemented as an instance of the abstract class.
 */
class RtfTermContext : public TermContext
{
 public:
  RtfTermContext() {}
  /** The initial value: not in a term context or beneath a quantifier. */
  uint32_t initialValue() const override;
  /** Compute the value of the index^th child of t whose hash is tval */
  uint32_t computeValue(TNode t, uint32_t tval, size_t index) const override;
  /** get hash value from the flags */
  static uint32_t getValue(bool inQuant, bool inTerm);
  /** get flags from the hash value */
  static void getFlags(uint32_t val, bool& inQuant, bool& inTerm);

 private:
  /**
   * Returns true if the children of t should be considered in a "term" context,
   * which is any context beneath a symbol that does not belong to the Boolean
   * theory as well as other exceptions like equality, separation logic
   * connectives and bit-vector eager atoms.
   */
  static bool hasNestedTermChildren(TNode t);
};

/**
 * Simpler version of above that only computes whether we are inside a
 * quantifier.
 */
class InQuantTermContext : public TermContext
{
 public:
  InQuantTermContext() {}
  /** The initial value: not beneath a quantifier. */
  uint32_t initialValue() const override;
  /** Compute the value of the index^th child of t whose hash is tval */
  uint32_t computeValue(TNode t, uint32_t tval, size_t index) const override;
  /** get hash value from the flags */
  static uint32_t getValue(bool inQuant);
  /** get flags from the hash value */
  static bool inQuant(uint32_t val, bool& inQuant);
};

/**
 * Polarity term context.
 *
 * This class computes the polarity of a term-context-sensitive term, which is
 * one of {true, false, none}. This corresponds to the value that can be
 * assigned to that term while preservering satisfiability of the overall
 * formula, or none if such a value does not exist. If not "none", this
 * typically corresponds to whether the number of NOT the formula is beneath is
 * even, although special cases exist (e.g. the first child of IMPLIES).
 *
 * For example, given the formula:
 *   (and P (not (= (f x) 0)))
 * assuming the root of this formula has true polarity, we have that:
 *   P @ [0] -> true
 *   (not (= (f x) 0)) @ [1] -> true
 *   (= (f x) 0) @ [1,0] -> false
 *   (f x) @ [1,0,0]), x @ [1,0,0,0]), 0 @ [1,0,1] -> none
 *
 * Notice that a term-context-sensitive Node is not one-to-one with Node.
 * In particular, given the formula:
 *   (and P (not P))
 * We have that the P at path [0] has polarity true and the P at path [1,0] has
 * polarity false.
 *
 * Finally, notice that polarity does not correspond to a value that the
 * formula entails. Thus, for the formula:
 *   (or P Q)
 * we have that
 *   P @ [0] -> true
 *   Q @ [1] -> true
 * although neither is entailed.
 *
 * Notice that the hash of a child can be computed from the parent's hash only.
 */
class PolarityTermContext : public TermContext
{
 public:
  PolarityTermContext() {}
  /** The initial value: true polarity. */
  uint32_t initialValue() const override;
  /** Compute the value of the index^th child of t whose hash is tval */
  uint32_t computeValue(TNode t, uint32_t tval, size_t index) const override;
  /**
   * Get hash value from the flags, where hasPol false means no polarity.
   */
  static uint32_t getValue(bool hasPol, bool pol);
  /**
   * get flags from the hash value. If we have no polarity, both hasPol and pol
   * are set to false.
   */
  static void getFlags(uint32_t val, bool& hasPol, bool& pol);
};

/**
 * Similar to InQuantTermContext, but computes whether we are below a theory
 * leaf of given theory id.
 */
class TheoryLeafTermContext : public TermContext
{
 public:
  TheoryLeafTermContext(theory::TheoryId id) : d_theoryId(id) {}
  /** The initial value: not beneath a theory leaf. */
  uint32_t initialValue() const override;
  /** Compute the value of the index^th child of t whose hash is tval */
  uint32_t computeValue(TNode t, uint32_t tval, size_t index) const override;

 private:
  theory::TheoryId d_theoryId;
};

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__TERM_CONVERSION_PROOF_GENERATOR_H */
