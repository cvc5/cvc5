/*********************                                                        */
/*! \file smt2_input.cpp
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

// These headers should be the first two included.
// See the documentation in "parser/antlr_undefines.h" for more details.
#include <antlr3.h>
#include "parser/antlr_undefines.h"


#include "parser/smt2/smt2_input.h"

#include "expr/expr_manager.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "parser/parser_exception.h"
#include "parser/smt2/smt2.h"
#include "parser/smt2/Smt2Lexer.h"
#include "parser/smt2/Smt2Parser.h"

namespace CVC4 {
namespace parser {

/* Use lookahead=2 */
Smt2Input::Smt2Input(AntlrInputStream& inputStream, InputLanguage lang) :
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

  setLanguage(lang);
}

Smt2Input::~Smt2Input() {
  d_pSmt2Lexer->free(d_pSmt2Lexer);
  d_pSmt2Parser->free(d_pSmt2Parser);
}

void Smt2Input::setLanguage(InputLanguage lang) {
  CheckArgument(lang == language::input::LANG_SMTLIB_V2_0 ||
                lang == language::input::LANG_SMTLIB_V2_5 ||
                lang == language::input::LANG_SMTLIB_V2_6, lang);
  d_lang = lang;
}

Command* Smt2Input::parseCommand() {
  return d_pSmt2Parser->parseCommand(d_pSmt2Parser);
}

Expr Smt2Input::parseExpr() {
  return d_pSmt2Parser->parseExpr(d_pSmt2Parser);
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
