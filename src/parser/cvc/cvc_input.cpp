/*
 * cvc_parser.cpp
 *
 *  Created on: Mar 5, 2010
 *      Author: chris
 */

#include <antlr3.h>

#include "expr/expr_manager.h"
#include "parser/parser_exception.h"
#include "parser/cvc/cvc_input.h"
#include "parser/cvc/generated/CvcLexer.h"
#include "parser/cvc/generated/CvcParser.h"

namespace CVC4 {
namespace parser {

/* Use lookahead=2 */
CvcInput::CvcInput(ExprManager* exprManager, const std::string& filename, bool useMmap) :
  AntlrInput(exprManager,filename,2,useMmap) {
  init();
}

CvcInput::CvcInput(ExprManager* exprManager, const std::string& input, const std::string& name) :
  AntlrInput(exprManager,input,name,2) {
  init();
}

void CvcInput::init() {
  pANTLR3_INPUT_STREAM input = getInputStream();
  AlwaysAssert( input != NULL );

  d_pCvcLexer = CvcLexerNew(input);
  if( d_pCvcLexer == NULL ) {
    throw ParserException("Failed to create CVC lexer.");
  }

  setLexer( d_pCvcLexer->pLexer );

  pANTLR3_COMMON_TOKEN_STREAM tokenStream = getTokenStream();
  AlwaysAssert( tokenStream != NULL );

  d_pCvcParser = CvcParserNew(tokenStream);
  if( d_pCvcParser == NULL ) {
    throw ParserException("Failed to create CVC parser.");
  }

  setParser(d_pCvcParser->pParser);
  SetCvcInput(this);
}


CvcInput::~CvcInput() {
  d_pCvcLexer->free(d_pCvcLexer);
  d_pCvcParser->free(d_pCvcParser);
}

Command* CvcInput::doParseCommand() throw (ParserException) {
  return d_pCvcParser->parseCommand(d_pCvcParser);
}

Expr CvcInput::doParseExpr() throw (ParserException) {
  return d_pCvcParser->parseExpr(d_pCvcParser);
}

pANTLR3_LEXER CvcInput::getLexer() {
  return d_pCvcLexer->pLexer;
}

} // namespace parser

} // namespace CVC4
