/*********************                                                        */
/*! \file smt_input.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add file-specific comments here ]].
 **
 ** [[ Add file-specific comments here ]]
 **/

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__SMT_INPUT_H
#define __CVC4__PARSER__SMT_INPUT_H

#include "parser/antlr_input.h"
#include "parser/smt/generated/SmtLexer.h"
#include "parser/smt/generated/SmtParser.h"

// extern void SmtParserSetAntlrParser(CVC4::parser::AntlrParser* newAntlrParser);

namespace CVC4 {

class Command;
class Expr;
class ExprManager;

namespace parser {

class SmtInput : public AntlrInput {

  /** The ANTLR3 SMT lexer for the input. */
  pSmtLexer d_pSmtLexer;

  /** The ANTLR3 CVC parser for the input. */
  pSmtParser d_pSmtParser;

public:

  /**
   * Create an input.
   *
   * @param inputStream the input stream to use
   */
  SmtInput(AntlrInputStream& inputStream);

  /**
   * Create a string input.
   *
   * @param exprManager the manager to use when building expressions from the input
   * @param input the string to read
   * @param name the "filename" to use when reporting errors
   */
//  SmtInput(ExprManager* exprManager, const std::string& input, const std::string& name);

  /** Destructor. Frees the lexer and the parser. */
  ~SmtInput();

protected:

  /**
   * Parse a command from the input. Returns <code>NULL</code> if
   * there is no command there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  Command* parseCommand() 
    throw(ParserException, TypeCheckingException, AssertionException);

  /**
   * Parse an expression from the input. Returns a null
   * <code>Expr</code> if there is no expression there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  Expr parseExpr() 
    throw(ParserException, TypeCheckingException, AssertionException);

private:

  /**
   * Initialize the class. Called from the constructors once the input
   * stream is initialized.
   */
  void init();

};/* class SmtInput */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__SMT_INPUT_H */
