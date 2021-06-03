/******************************************************************************
 * Top contributors (to current version):
 *   Christopher L. Conway, Mathias Preiner, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 */

#include "cvc5parser_private.h"

#ifndef CVC5__PARSER__CVC_INPUT_H
#define CVC5__PARSER__CVC_INPUT_H

#include "parser/antlr_input.h"
#include "parser/cvc/CvcLexer.h"
#include "parser/cvc/CvcParser.h"

// extern void CvcParserSetAntlrParser(cvc5::parser::AntlrParser*
// newAntlrParser);

namespace cvc5 {

class Command;
class Expr;

namespace parser {

class CvcInput : public AntlrInput {
  /** The ANTLR3 CVC lexer for the input. */
  pCvcLexer d_pCvcLexer;

  /** The ANTLR3 CVC parser for the input. */
  pCvcParser d_pCvcParser;

 public:
  /** Create an input.
   *
   * @param inputStream the input to parse
   */
  CvcInput(AntlrInputStream& inputStream);

  /** Destructor. Frees the lexer and the parser. */
  virtual ~CvcInput();

 protected:
  /** Parse a command from the input. Returns <code>NULL</code> if there is
   * no command there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  Command* parseCommand() override;

  /** Parse an expression from the input. Returns a null <code>api::Term</code>
   * if there is no expression there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  api::Term parseExpr() override;

 private:
  /** Initialize the class. Called from the constructors once the input stream
   * is initialized. */
  void init();

}; // class CvcInput

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__CVC_INPUT_H */
