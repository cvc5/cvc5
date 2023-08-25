/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * ParserState state implementation.
 */

#include "parser/parser_utils.h"

#include <iostream>

namespace cvc5 {
namespace parser {

std::ostream& operator<<(std::ostream& out, DeclarationCheck check)
{
  switch (check)
  {
    case CHECK_NONE: return out << "CHECK_NONE";
    case CHECK_DECLARED: return out << "CHECK_DECLARED";
    case CHECK_UNDECLARED: return out << "CHECK_UNDECLARED";
    default: return out << "DeclarationCheck!UNKNOWN";
  }
}

std::ostream& operator<<(std::ostream& out, SymbolType type)
{
  switch (type)
  {
    case SYM_VARIABLE: return out << "SYM_VARIABLE";
    case SYM_SORT: return out << "SYM_SORT";
    case SYM_VERBATIM: return out << "SYM_VERBATIM";
    default: return out << "SymbolType!UNKNOWN";
  }
}

}  // namespace parser
}  // namespace cvc5
