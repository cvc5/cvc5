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

#include "cvc5parser_private.h"

#ifndef CVC5__PARSER__TEMP_LEXER_H
#define CVC5__PARSER__TEMP_LEXER_H

#include <cstdlib>
#include <istream>
#include <vector>

#include "parser/tokens.h"

namespace cvc5 {
namespace parser {

class FlexLexer;

class TempLexer
{
 public:
  TempLexer(FlexLexer& p);
  void initialize(std::istream* input);
  const char* tokenStr();
  Token nextToken();

 private:
  FlexLexer& d_parent;
  std::istream* d_input;
  std::vector<char> d_token;
  int32_t nextChar();
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__TEMP_LEXER_H */
