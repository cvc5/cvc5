/*********************                                                        */
/*! \file smt2_quote_string.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Quotes a string if necessary for smt2.
 **
 ** Quotes a string if necessary for smt2.
 **/

#include "cvc4_private.h"

#ifndef CVC4__UTIL__SMT2_QUOTE_STRING_H
#define CVC4__UTIL__SMT2_QUOTE_STRING_H

#include <string>

namespace CVC4 {

/**
 * SMT-LIB 2 quoting for symbols
 */
std::string quoteSymbol(const std::string& s);

}/* CVC4 namespace */

#endif /* CVC4__UTIL__SMT2_QUOTE_STRING_H */
