/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Temp
 */

#include "parser/temp_lexer.h"

namespace cvc5 {
namespace parser {

TempLexer::TempLexer(FlexLexer& p) : d_parent(p) {}
void TempLexer::initialize(std::istream& input)
{
}
const char* TempLexer::tokenStr()
{
  return "";
}
Token TempLexer::nextToken()
{
  return Token::NONE;
}

}  // namespace parser
}  // namespace cvc5

