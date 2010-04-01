/*********************                                                        */
/** input.h
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
 ** Parser abstraction.
 **/

#include "cvc4parser_public.h"

#ifndef __CVC4__PARSER__INPUT_H
#define __CVC4__PARSER__INPUT_H

#include <string>

#include "expr/expr.h"
#include "parser/parser_exception.h"
#include "parser/parser_options.h"

namespace CVC4 {

// Forward declarations
class ExprManager;
class Command;
class Type;

namespace parser {

class ParserState;

/**
 * An input to be parsed. This class serves two purposes: to the client, it provides
 * the methods <code>parseNextCommand</code> and <code>parseNextExpression</code> to
 * extract a stream of <code>Command</code>'s and <code>Expr</code>'s from the input;
 * to the parser, it provides a repository for state data, like the variable symbol
 * table, and a variety of convenience functions for updating and checking the state.
 *
 * An Input should be created using the static factory methods,
 * e.g., <code>newFileParser</code> and <code>newStringInput</code>, and
 * should be deleted when done.
 */
class CVC4_PUBLIC Input {
  friend class ParserState;

  /** Whether to de-allocate the input */
  //  bool d_deleteInput;

  ParserState *d_parserState;

public:

  /**
   * Create a new parser for the given file.
   * @param exprManager the ExprManager to use
   * @param filename the path of the file to parse
   */
  Input(ExprManager* exprManager, const std::string& filename);

  /**
   * Destructor.
   */
  virtual ~Input();

  /** Create an input for the given file.
    *
    * @param exprManager the ExprManager for creating expressions from the input
    * @param lang the input language
    * @param filename the input filename
    */
   static Input* newFileInput(ExprManager* exprManager, InputLanguage lang, const std::string& filename, bool useMmap=false);

  /** Create an input for the given stream.
   *
   * @param exprManager the ExprManager for creating expressions from the input
   * @param lang the input language
   * @param input the input stream
   * @param name the name of the stream, for use in error messages
   */
  //static Parser* getNewParser(ExprManager* exprManager, InputLanguage lang, std::istream& input, const std::string& name);

  /** Create an input for the given string
   *
   * @param exprManager the ExprManager for creating expressions from the input
   * @param lang the input language
   * @param input the input string
   * @param name the name of the stream, for use in error messages
   */
  static Input* newStringInput(ExprManager* exprManager, InputLanguage lang, const std::string& input, const std::string& name);

  /**
    * Check if we are done -- either the end of input has been reached, or some
    * error has been encountered.
    * @return true if parser is done
    */
  bool done() const;

  /** Enable semantic checks during parsing. */
  void enableChecks();

  /** Disable semantic checks during parsing. Disabling checks may lead to crashes on bad inputs. */
  void disableChecks();

  /**
   * Parse the next command of the input. If EOF is encountered a EmptyCommand
   * is returned and done flag is set.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  Command* parseNextCommand() throw(ParserException);

  /**
   * Parse the next expression of the stream. If EOF is encountered a null
   * expression is returned and done flag is set.
   * @return the parsed expression
   * @throws ParserException if an error is encountered during parsing.
   */
  Expr parseNextExpression() throw(ParserException);


protected:

  /** Called by <code>parseNextCommand</code> to actually parse a command from
   * the input by invoking the implementation-specific parsing method.  Returns
   * <code>NULL</code> if there is no command there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  virtual Command* doParseCommand() throw(ParserException) = 0;

  /** Called by <code>parseNextExpression</code> to actually parse an
   * expression from the input by invoking the implementation-specific
   * parsing method. Returns a null <code>Expr</code> if there is no
   * expression there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  virtual Expr doParseExpr() throw(ParserException) = 0;

  inline ParserState* getParserState() const {
    return d_parserState;
  }

private:

  /** Throws a <code>ParserException</code> with the given error message.
   * Implementations should fill in the <code>ParserException</code> with
   * line number information, etc. */
  virtual void parseError(const std::string& msg) throw (ParserException) = 0;

}; // end of class Input

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__INPUT_H */
