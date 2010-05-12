/*********************                                                        */
/** smt2_input.h
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** [[ Add file-specific comments here ]]
 **/

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__SMT2_INPUT_H
#define __CVC4__PARSER__SMT2_INPUT_H

#include "parser/antlr_input.h"
#include "parser/smt2/generated/Smt2Lexer.h"
#include "parser/smt2/generated/Smt2Parser.h"

// extern void Smt2ParserSetAntlrParser(CVC4::parser::AntlrParser* newAntlrParser);

namespace CVC4 {

class Command;
class Expr;
class ExprManager;

namespace parser {

class Smt2;

class Smt2Input : public AntlrInput {
  typedef AntlrInput super;

  /** The ANTLR3 SMT2 lexer for the input. */
  pSmt2Lexer d_pSmt2Lexer;

  /** The ANTLR3 CVC parser for the input. */
  pSmt2Parser d_pSmt2Parser;

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
  Smt2Input(AntlrInputStream& inputStream);

  /**
   * Create a string input.
   *
   * @param exprManager the manager to use when building expressions from the input
   * @param input the string to read
   * @param name the "filename" to use when reporting errors
   */
//  Smt2Input(ExprManager* exprManager, const std::string& input, const std::string& name);

  /** Destructor. Frees the lexer and the parser. */
  virtual ~Smt2Input();

protected:

  /**
   * Parse a command from the input. Returns <code>NULL</code> if
   * there is no command there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  Command* parseCommand() throw(ParserException);

  /**
   * Parse an expression from the input. Returns a null
   * <code>Expr</code> if there is no expression there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  Expr parseExpr() throw(ParserException);

};/* class Smt2Input */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__SMT2_INPUT_H */
