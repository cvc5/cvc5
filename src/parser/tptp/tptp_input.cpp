/******************************************************************************
 * Top contributors (to current version):
 *   Francois Bobot, Morgan Deters, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add file-specific comments here ]]
 */

#include "parser/tptp/tptp_input.h"

#include <antlr3.h>

#include "base/check.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "parser/parser_exception.h"
#include "parser/tptp/TptpLexer.h"
#include "parser/tptp/TptpParser.h"
#include "parser/tptp/tptp.h"

namespace cvc5 {
namespace parser {

/* Use lookahead=2 */
TptpInput::TptpInput(AntlrInputStream& inputStream) :
  AntlrInput(inputStream, 2) {
  pANTLR3_INPUT_STREAM input = inputStream.getAntlr3InputStream();
  Assert(input != NULL);

  d_pTptpLexer = TptpLexerNew(input);
  if( d_pTptpLexer == NULL ) {
    throw ParserException("Failed to create TPTP lexer.");
  }

  setAntlr3Lexer( d_pTptpLexer->pLexer );

  pANTLR3_COMMON_TOKEN_STREAM tokenStream = getTokenStream();
  Assert(tokenStream != NULL);

  d_pTptpParser = TptpParserNew(tokenStream);
  if( d_pTptpParser == NULL ) {
    throw ParserException("Failed to create TPTP parser.");
  }

  setAntlr3Parser(d_pTptpParser->pParser);
}


TptpInput::~TptpInput() {
  d_pTptpLexer->free(d_pTptpLexer);
  d_pTptpParser->free(d_pTptpParser);
}

Command* TptpInput::parseCommand() {
  return d_pTptpParser->parseCommand(d_pTptpParser);
}

api::Term TptpInput::parseExpr()
{
  return d_pTptpParser->parseExpr(d_pTptpParser);
}

}  // namespace parser
}  // namespace cvc5
