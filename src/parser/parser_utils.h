/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A collection of state for use by parser implementations.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__PARSER_UTILS_H
#define CVC5__PARSER__PARSER_UTILS_H

#include <string>

namespace cvc5 {
namespace parser {

/** Types of checks for the symbols */
enum DeclarationCheck
{
  /** Enforce that the symbol has been declared */
  CHECK_DECLARED,
  /** Enforce that the symbol has not been declared */
  CHECK_UNDECLARED,
  /** Don't check anything */
  CHECK_NONE
}; /* enum DeclarationCheck */

/**
 * Returns a string representation of the given object (for
 * debugging).
 */
std::ostream& operator<<(std::ostream& out, DeclarationCheck check);

/**
 * Types of symbols. Used to define namespaces.
 */
enum SymbolType
{
  /** Variables */
  SYM_VARIABLE,
  /** Sorts */
  SYM_SORT,
  /** Symbols that should be preserved verbatim */
  SYM_VERBATIM
}; /* enum SymbolType */

/**
 * Returns a string representation of the given object (for
 * debugging).
 */
std::ostream& operator<<(std::ostream& out, SymbolType type);

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__PARSER_UTILS_H */
