/*********************                                                        */
/*! \file tptp_input.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Francois Bobot, Paul Meng, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add file-specific comments here ]].
 **
 ** [[ Add file-specific comments here ]]
 **/

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__TPTP_INPUT_H
#define __CVC4__PARSER__TPTP_INPUT_H

#include "parser/antlr_input.h"
#include "parser/tptp/TptpLexer.h"
#include "parser/tptp/TptpParser.h"

// extern void TptpParserSetAntlrParser(CVC4::parser::AntlrParser* newAntlrParser);

namespace CVC4 {

class Command;
class Expr;
class ExprManager;

namespace parser {

class Tptp;

class TptpInput : public AntlrInput {
  typedef AntlrInput super;

  /** The ANTLR3 TPTP lexer for the input. */
  pTptpLexer d_pTptpLexer;

  /** The ANTLR3 CVC parser for the input. */
  pTptpParser d_pTptpParser;

  /**
   * Initialize the class. Called from the constructors once the input
   * stream is initialized.
   */
  void init();

 public:
  /**
   * Create an input.
   *
   * @param inputStream the input stream to use
   */
  TptpInput(AntlrInputStream& inputStream);

  /** Destructor. Frees the lexer and the parser. */
  virtual ~TptpInput();

  /** Get the language that this Input is reading. */
  InputLanguage getLanguage() const override
  {
    return language::input::LANG_TPTP;
  }

 protected:
  /**
   * Parse a command from the input. Returns <code>NULL</code> if
   * there is no command there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  Command* parseCommand() override;

  /**
   * Parse an expression from the input. Returns a null
   * <code>Expr</code> if there is no expression there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  Expr parseExpr() override;

};/* class TptpInput */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__TPTP_INPUT_H */
