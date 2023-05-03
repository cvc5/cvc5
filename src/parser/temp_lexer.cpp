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

#include "parser/flex_lexer.h"

namespace cvc5 {
namespace parser {

TempLexer::TempLexer(FlexLexer& p) : d_parent(p), d_input(nullptr) {}

void TempLexer::initialize(std::istream* input) { d_input = input;}

const char* TempLexer::tokenStr() { return d_token.data(); }

Token TempLexer::nextToken() 
{ 
  return Token::NONE; 
}

int32_t TempLexer::nextChar()
{
  int32_t res = d_input->get();
  if (res == '\n')
  {
    d_parent.addLines(1);
  }
  else
  {
    d_parent.addColumns(1);
  }
  return res;
}
  
}  // namespace parser
}  // namespace cvc5
