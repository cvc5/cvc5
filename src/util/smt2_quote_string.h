/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Abdalrhman Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Quotes a string if necessary for smt2.
 */

#include "cvc5_private.h"

#ifndef CVC5__UTIL__SMT2_QUOTE_STRING_H
#define CVC5__UTIL__SMT2_QUOTE_STRING_H

#include <string>

#include "cvc5_export.h"

namespace cvc5::internal {

/**
 * SMT-LIB 2 quoting for symbols
 */
std::string quoteSymbol(const std::string& s);

/**
 * SMT-LIB 2 quoting for strings
 */
std::string quoteString(const std::string& s) CVC5_EXPORT;

}  // namespace cvc5::internal

#endif /* CVC5__UTIL__SMT2_QUOTE_STRING_H */
