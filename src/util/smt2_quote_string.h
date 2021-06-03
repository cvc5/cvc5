/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

namespace cvc5 {

/**
 * SMT-LIB 2 quoting for symbols
 */
std::string quoteSymbol(const std::string& s);

}  // namespace cvc5

#endif /* CVC5__UTIL__SMT2_QUOTE_STRING_H */
