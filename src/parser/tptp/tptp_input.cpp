/*********************                                                        */
/*! \file tptp_input.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Francois Bobot, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add file-specific comments here ]].
 **
 ** [[ Add file-specific comments here ]]
 **/


#include "parser/tptp/tptp_input.h"

#include <antlr3.h>

#include "expr/expr_manager.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "parser/parser_exception.h"
#include "parser/tptp/tptp.h"
#include "parser/tptp/TptpLexer.h"
#include "parser/tptp/TptpParser.h"

namespace CVC4 {
namespace parser {

/* Use lookahead=2 */
TptpInput::TptpInput(AntlrInputStream& inputStream) :
  AntlrInput(inputStream, 2) {
  pANTLR3_INPUT_STREAM input = inputStream.getAntlr3InputStream();
  assert( input != NULL );

  d_pTptpLexer = TptpLexerNew(input);
  if( d_pTptpLexer == NULL ) {
    throw ParserException("Failed to create TPTP lexer.");
  }

  setAntlr3Lexer( d_pTptpLexer->pLexer );

  pANTLR3_COMMON_TOKEN_STREAM tokenStream = getTokenStream();
  assert( tokenStream != NULL );

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

}/* CVC4::parser namespace */
}/* CVC4 namespace */
