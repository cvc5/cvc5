/*********************                                                        */
/*! \file smt_input.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add file-specific comments here ]].
 **
 ** [[ Add file-specific comments here ]]
 **/

#include <antlr3.h>

#include "smt_input.h"
#include "expr/expr_manager.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "parser/parser_exception.h"
#include "parser/smt/generated/SmtLexer.h"
#include "parser/smt/generated/SmtParser.h"

namespace CVC4 {
namespace parser {

/* Use lookahead=2 */
SmtInput::SmtInput(AntlrInputStream& inputStream) :
  AntlrInput(inputStream, 2) {
  pANTLR3_INPUT_STREAM input = inputStream.getAntlr3InputStream();
  AlwaysAssert( input != NULL );

  d_pSmtLexer = SmtLexerNew(input);
  if( d_pSmtLexer == NULL ) {
    throw ParserException("Failed to create SMT lexer.");
  }

  setAntlr3Lexer( d_pSmtLexer->pLexer );

  pANTLR3_COMMON_TOKEN_STREAM tokenStream = getTokenStream();
  AlwaysAssert( tokenStream != NULL );

  d_pSmtParser = SmtParserNew(tokenStream);
  if( d_pSmtParser == NULL ) {
    throw ParserException("Failed to create SMT parser.");
  }

  setAntlr3Parser(d_pSmtParser->pParser);
}


SmtInput::~SmtInput() {
  d_pSmtLexer->free(d_pSmtLexer);
  d_pSmtParser->free(d_pSmtParser);
}

Command* SmtInput::parseCommand()
  throw (ParserException, TypeCheckingException, AssertionException) {
  return d_pSmtParser->parseCommand(d_pSmtParser);
}

Expr SmtInput::parseExpr()
  throw (ParserException, TypeCheckingException, AssertionException) {
  return d_pSmtParser->parseExpr(d_pSmtParser);
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
