/*
 * smt_parser.cpp
 *
 *  Created on: Mar 5, 2010
 *      Author: chris
 */

#include <antlr3.h>

#include "expr/expr_manager.h"
#include "parser/parser_exception.h"
#include "parser/smt/smt_input.h"
#include "parser/smt/generated/SmtLexer.h"
#include "parser/smt/generated/SmtParser.h"

namespace CVC4 {
namespace parser {

/* Use lookahead=2 */
SmtInput::SmtInput(ExprManager* exprManager, const std::string& filename,
                   bool useMmap) :
  AntlrInput(exprManager, filename, 2, useMmap) {
  init();
}

SmtInput::SmtInput(ExprManager* exprManager, const std::string& input,
                   const std::string& name) :
  AntlrInput(exprManager, input, name, 2) {
  init();
}

void SmtInput::init() {
  pANTLR3_INPUT_STREAM input = getInputStream();
  AlwaysAssert( input != NULL );

  d_pSmtLexer = SmtLexerNew(input);
  if( d_pSmtLexer == NULL ) {
    throw ParserException("Failed to create SMT lexer.");
  }

  setLexer( d_pSmtLexer->pLexer );

  pANTLR3_COMMON_TOKEN_STREAM tokenStream = getTokenStream();
  AlwaysAssert( tokenStream != NULL );

  d_pSmtParser = SmtParserNew(tokenStream);
  if( d_pSmtParser == NULL ) {
    throw ParserException("Failed to create SMT parser.");
  }

  setParser(d_pSmtParser->pParser);
}


SmtInput::~SmtInput() {
  d_pSmtLexer->free(d_pSmtLexer);
  d_pSmtParser->free(d_pSmtParser);
}

Command* SmtInput::doParseCommand() throw (ParserException) {
  return d_pSmtParser->parseCommand(d_pSmtParser);
}

Expr SmtInput::doParseExpr() throw (ParserException) {
  return d_pSmtParser->parseExpr(d_pSmtParser);
}

} // namespace parser

} // namespace CVC4
