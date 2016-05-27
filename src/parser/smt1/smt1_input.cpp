/*********************                                                        */
/*! \file smt1_input.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add file-specific comments here ]].
 **
 ** [[ Add file-specific comments here ]]
 **/

// These headers must be the first two included.
// See the documentation in "parser/antlr_undefines.h" for more details.
#include <antlr3.h>
#include "parser/antlr_undefines.h"

#include "parser/smt1/smt1_input.h"

#include "expr/expr_manager.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "parser/parser_exception.h"
#include "parser/smt1/Smt1Lexer.h"
#include "parser/smt1/Smt1Parser.h"

namespace CVC4 {
namespace parser {

/* Use lookahead=2 */
Smt1Input::Smt1Input(AntlrInputStream& inputStream) :
  AntlrInput(inputStream, 2) {
  pANTLR3_INPUT_STREAM input = inputStream.getAntlr3InputStream();
  assert( input != NULL );

  d_pSmt1Lexer = Smt1LexerNew(input);
  if( d_pSmt1Lexer == NULL ) {
    throw ParserException("Failed to create SMT lexer.");
  }

  setAntlr3Lexer( d_pSmt1Lexer->pLexer );

  pANTLR3_COMMON_TOKEN_STREAM tokenStream = getTokenStream();
  assert( tokenStream != NULL );

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

Command* Smt1Input::parseCommand() {
  return d_pSmt1Parser->parseCommand(d_pSmt1Parser);
}

Expr Smt1Input::parseExpr() {
  return d_pSmt1Parser->parseExpr(d_pSmt1Parser);
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
