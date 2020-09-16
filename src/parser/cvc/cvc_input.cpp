/*********************                                                        */
/*! \file cvc_input.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add file-specific comments here ]].
 **
 ** [[ Add file-specific comments here ]]
 **/

#include "parser/cvc/cvc_input.h"

#include <antlr3.h>

#include "expr/expr_manager.h"
#include "parser/antlr_input.h"
#include "parser/parser_exception.h"
#include "parser/cvc/CvcLexer.h"
#include "parser/cvc/CvcParser.h"

namespace CVC4 {
namespace parser {

/* Use lookahead=3 */
CvcInput::CvcInput(AntlrInputStream& inputStream) :
  AntlrInput(inputStream,6) {
  pANTLR3_INPUT_STREAM input = inputStream.getAntlr3InputStream();
  assert( input != NULL );

  d_pCvcLexer = CvcLexerNew(input);
  if( d_pCvcLexer == NULL ) {
    throw ParserException("Failed to create CVC lexer.");
  }

  setAntlr3Lexer( d_pCvcLexer->pLexer );

  pANTLR3_COMMON_TOKEN_STREAM tokenStream = getTokenStream();
  assert( tokenStream != NULL );

  d_pCvcParser = CvcParserNew(tokenStream);
  if( d_pCvcParser == NULL ) {
    throw ParserException("Failed to create CVC parser.");
  }

  setAntlr3Parser(d_pCvcParser->pParser);
}


CvcInput::~CvcInput() {
  d_pCvcLexer->free(d_pCvcLexer);
  d_pCvcParser->free(d_pCvcParser);
}

Command* CvcInput::parseCommand() {
  return d_pCvcParser->parseCommand(d_pCvcParser);
}

api::Term CvcInput::parseExpr()
{
  return d_pCvcParser->parseExpr(d_pCvcParser);
}

/*
pANTLR3_LEXER CvcInput::getLexer() {
  return d_pCvcLexer->pLexer;
}
*/

}/* CVC4::parser namespace */
}/* CVC4 namespace */
