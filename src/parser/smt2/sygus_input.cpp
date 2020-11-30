/*********************                                                        */
/*! \file sygus_input.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add file-specific comments here ]].
 **
 ** [[ Add file-specific comments here ]]
 **/

#include "parser/smt2/sygus_input.h"

#include <antlr3.h>

#include "expr/expr_manager.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "parser/parser_exception.h"
#include "parser/smt2/sygus_input.h"
#include "parser/smt2/Smt2Lexer.h"
#include "parser/smt2/Smt2Parser.h"

namespace CVC4 {
namespace parser {

/* Use lookahead=2 */
SygusInput::SygusInput(AntlrInputStream& inputStream) :
  AntlrInput(inputStream, 2) {

  pANTLR3_INPUT_STREAM input = inputStream.getAntlr3InputStream();
  assert( input != NULL );

  d_pSmt2Lexer = Smt2LexerNew(input);
  if( d_pSmt2Lexer == NULL ) {
    throw ParserException("Failed to create SMT2 lexer.");
  }

  setAntlr3Lexer( d_pSmt2Lexer->pLexer );

  pANTLR3_COMMON_TOKEN_STREAM tokenStream = getTokenStream();
  assert( tokenStream != NULL );

  d_pSmt2Parser = Smt2ParserNew(tokenStream);
  if( d_pSmt2Parser == NULL ) {
    throw ParserException("Failed to create SMT2 parser.");
  }

  setAntlr3Parser(d_pSmt2Parser->pParser);
}

SygusInput::~SygusInput() {
  d_pSmt2Lexer->free(d_pSmt2Lexer);
  d_pSmt2Parser->free(d_pSmt2Parser);
}

Command* SygusInput::parseCommand() {
  return d_pSmt2Parser->parseSygus(d_pSmt2Parser);
}

api::Term SygusInput::parseExpr()
{
  return d_pSmt2Parser->parseExpr(d_pSmt2Parser);
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
