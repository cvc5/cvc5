/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Skolem manager utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__INTERNAL_SKOLEM_ID_H
#define CVC5__EXPR__INTERNAL_SKOLEM_ID_H

#include <string>

#include "expr/internal_skolem_id.h"

namespace cvc5::internal {

/**
 * Internal skolem function identifier, used for identifying internal skolems
 * that are not exported as part of the API.
 *
 * This is a subclassification of skolems whose SkolemId is INTERNAL. It is
 * used to generate canonical skolems but without exporting to the API. Skolems
 * can be created using mkInternalSkolemFunction below.
 */
enum class InternalSkolemId
{
  NONE,
  /** Sequence model construction, element for base */
  SEQ_MODEL_BASE_ELEMENT,
  /** the "none" term, for instantiation evaluation */
  IEVAL_NONE,
  /** the "some" term, for instantiation evaluation */
  IEVAL_SOME,
  /** sygus "any constant" placeholder */
  SYGUS_ANY_CONSTANT,
  /**
   * Quantifiers synth fun embedding, for function-to-synthesize, this the
   * first order datatype variable for f.
   */
  QUANTIFIERS_SYNTH_FUN_EMBED,
  /** Higher-order type match predicate, see HoTermDb */
  HO_TYPE_MATCH_PRED,
  /** Input variables for MBQI */
  MBQI_INPUT,
  /** abstract value for a term t */
  ABSTRACT_VALUE,
  /** Input variables for quantifier elimination of closed formulas */
  QE_CLOSED_INPUT,
  /** Skolem used for marking a quantified attribute */
  QUANTIFIERS_ATTRIBUTE_INTERNAL
};
/** Converts an internal skolem function name to a string. */
const char* toString(InternalSkolemId id);
/** Writes an internal skolem function name to a stream. */
std::ostream& operator<<(std::ostream& out, InternalSkolemId id);

/**
 * Optional flags used to control behavior of skolem creation.
 * They should be composed with bitwise operators.
 */
enum class SkolemFlags : uint8_t
{
  /** default behavior */
  SKOLEM_DEFAULT = 0,
  /** do not make the name unique by adding the id */
  SKOLEM_EXACT_NAME = 1,
};

/*
 * Performs a bitwise OR operation between two SkolemFlags values.
 */
inline SkolemFlags operator|(SkolemFlags lhs, SkolemFlags rhs)
{
  return static_cast<SkolemFlags>(
      static_cast<std::underlying_type_t<SkolemFlags>>(lhs)
      | static_cast<std::underlying_type_t<SkolemFlags>>(rhs));
}

/*
 * Performs a bitwise AND operation between two SkolemFlags values.
 */
inline SkolemFlags operator&(SkolemFlags lhs, SkolemFlags rhs)
{
  return static_cast<SkolemFlags>(
      static_cast<std::underlying_type_t<SkolemFlags>>(lhs)
      & static_cast<std::underlying_type_t<SkolemFlags>>(rhs));
}

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__INTERNAL_SKOLEM_ID_H */
