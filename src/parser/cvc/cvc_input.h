/*********************                                                        */
/** cvc_input.h
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** [[ Add file-specific comments here ]]
 **/

#include "cvc4parser_public.h"

#ifndef __CVC4__PARSER__CVC_INPUT_H
#define __CVC4__PARSER__CVC_INPUT_H

#include "parser/antlr_input.h"
#include "parser/cvc/generated/CvcLexer.h"
#include "parser/cvc/generated/CvcParser.h"

// extern void CvcParserSetAntlrParser(CVC4::parser::AntlrParser* newAntlrParser);

namespace CVC4 {

class Command;
class Expr;
class ExprManager;

namespace parser {

class CvcInput : public AntlrInput {
  /** The ANTLR3 CVC lexer for the input. */
  pCvcLexer d_pCvcLexer;

  /** The ANTLR3 CVC parser for the input. */
  pCvcParser d_pCvcParser;

public:

  /** Create a file input.
   *
   * @param exprManager the manager to use when building expressions from the input
   * @param filename the path of the file to read
   * @param useMmap <code>true</code> if the input should use memory-mapped
   * I/O; otherwise, the input will use the standard ANTLR3 I/O implementation.
   */
  CvcInput(ExprManager* exprManager, const std::string& filename, bool useMmap);

  /** Create a string input.
   *
   * @param exprManager the manager to use when building expressions from the input
   * @param input the string to read
   * @param name the "filename" to use when reporting errors
   */
  CvcInput(ExprManager* exprManager, const std::string& input,
           const std::string& name);

  /* Destructor. Frees the lexer and the parser. */
  ~CvcInput();

protected:

  /** Parse a command from the input. Returns <code>NULL</code> if there is
   * no command there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  Command* doParseCommand() throw(ParserException);

  /** Parse an expression from the input. Returns a null <code>Expr</code>
   * if there is no expression there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  Expr doParseExpr() throw(ParserException);

private:

  /** Initialize the class. Called from the constructors once the input stream
   * is initialized. */
  void init();

}; // class CvcInput

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__CVC_INPUT_H */
