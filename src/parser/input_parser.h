/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The interface for parsing an input with a parser.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__INPUT_PARSER_H
#define CVC5__PARSER__INPUT_PARSER_H

#include <memory>

#include "api/cpp/cvc5.h"
#include "cvc5_export.h"
#include "parser/parser.h"

namespace cvc5 {
namespace parser {

class Command;
class Input;
class Parser;
class SymbolManager;

/**
 * This class is the main interface for retrieving commands and expressions
 * from an input using a parser.
 *
 * After construction, it is expected that an input is first set via e.g.
 * setFileInput, setStreamInput, or setStringInput. Then, the methods
 * nextCommand and nextExpression can be invoked to parse the input.
 *
 * It currently uses a (deprecated) implementation which relies on ANTLR.
 */
class CVC5_EXPORT InputParser
{
  friend Parser;

 public:
  InputParser(Solver* solver, SymbolManager* sm, bool useOptions);

  /** Set the input for the given file.
   *
   * @param lang the input language
   * @param filename the input filename
   */
  void setFileInput(const std::string& lang, const std::string& filename);

  /** Set the input for the given stream.
   *
   * @param lang the input language
   * @param input the input stream
   * @param name the name of the stream, for use in error messages
   */
  void setStreamInput(const std::string& lang,
                      std::istream& input,
                      const std::string& name);

  /** Set the input for the given string
   *
   * @param lang the input language
   * @param input the input string
   * @param name the name of the stream, for use in error messages
   */
  void setStringInput(const std::string& lang,
                      const std::string& input,
                      const std::string& name);

  /**
   * Parse and return the next command.
   * NOTE: currently memory management of commands is handled internally.
   */
  Command* nextCommand();

  /** Parse and return the next expression. */
  Term nextExpression();

 private:
  //!!!!!!!!!!!!!! TODO: this implementation is deprecated and should be
  // replaced (wishue #142).
  /**  The parser state. */
  std::unique_ptr<Parser> d_state;
  /** The underlying input */
  std::unique_ptr<Input> d_input;
  //!!!!!!!!!!!!!!
};

}  // namespace parser
}  // namespace cvc5

#endif
