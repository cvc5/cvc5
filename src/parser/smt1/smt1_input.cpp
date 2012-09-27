/*********************                                                        */
/*! \file smt1_input.cpp
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

#include "parser/smt1/smt1_input.h"
#include "expr/expr_manager.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "parser/parser_exception.h"
#include "parser/smt1/generated/Smt1Lexer.h"
#include "parser/smt1/generated/Smt1Parser.h"

namespace CVC4 {
namespace parser {

/* Use lookahead=2 */
Smt1Input::Smt1Input(AntlrInputStream& inputStream) :
  AntlrInput(inputStream, 2) {
  pANTLR3_INPUT_STREAM input = inputStream.getAntlr3InputStream();
  AlwaysAssert( input != NULL );

  d_pSmt1Lexer = Smt1LexerNew(input);
  if( d_pSmt1Lexer == NULL ) {
    throw ParserException("Failed to create SMT lexer.");
  }

  setAntlr3Lexer( d_pSmt1Lexer->pLexer );

  pANTLR3_COMMON_TOKEN_STREAM tokenStream = getTokenStream();
  AlwaysAssert( tokenStream != NULL );

  d_pSmt1Parser = Smt1ParserNew(tokenStream);
  if( d_pSmt1Parser == NULL ) {
    throw ParserException("Failed to create SMT parser.");
  }

  setAntlr3Parser(d_pSmt1Parser->pParser);
}


Smt1Input::~Smt1Input() {
  d_pSmt1Lexer->free(d_pSmt1Lexer);
  d_pSmt1Parser->free(d_pSmt1Parser);
}

Command* Smt1Input::parseCommand()
  throw (ParserException, TypeCheckingException, AssertionException) {
  return d_pSmt1Parser->parseCommand(d_pSmt1Parser);
}

Expr Smt1Input::parseExpr()
  throw (ParserException, TypeCheckingException, AssertionException) {
  return d_pSmt1Parser->parseExpr(d_pSmt1Parser);
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
