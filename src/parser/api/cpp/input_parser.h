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

#ifndef CVC5__PARSER__API__CPP__INPUT_PARSER_H
#define CVC5__PARSER__API__CPP__INPUT_PARSER_H

#include <memory>

#include "api/cpp/cvc5.h"
#include "cvc5_export.h"
#include "parser/flex_parser.h"
#include "parser/parser_antlr.h"

namespace cvc5 {
namespace parser {

class Command;
class SymbolManager;

/**
 * This class is the main interface for retrieving commands and expressions
 * from an input using a parser.
 *
 * After construction, it is expected that an input is first set via e.g.
 * setFileInput, setStreamInput, or setStringInput. Then, the methods
 * nextCommand and nextExpression can be invoked to parse the input.
 */
class CVC5_EXPORT InputParser
{
 public:
  /**
   * Construct an input parser
   *
   * @param solver The solver (e.g. for constructing terms and sorts)
   * @param sm The symbol manager, which contains a symbol table that maps
   * symbols to terms and sorts.
   */
  InputParser(Solver* solver, SymbolManager* sm);
  /**
   * Construct an input parser with an initially empty symbol manager.
   *
   * @param solver The solver (e.g. for constructing terms and sorts)
   */
  InputParser(Solver* solver);

  /** Get the underlying solver of this input parser */
  Solver* getSolver();
  /** Get the underlying symbol manager of this input parser */
  SymbolManager* getSymbolManager();
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

  /**
   * Set that we will be feeding strings to this parser via
   * appendIncrementalStringInput below.
   *
   * @param lang the input language
   * @param name the name of the stream, for use in error messages
   */
  void setIncrementalStringInput(const std::string& lang,
                                 const std::string& name);
  /**
   * Append string to the input being parsed by this parser. Should be
   * called after calling setIncrementalStringInput and only after the
   * previous string (if one was provided) is finished being parsed.
   *
   * @param input The input string
   */
  void appendIncrementalStringInput(const std::string& input);

  /**
   * Parse and return the next command.
   * NOTE: currently memory management of commands is handled internally.
   */
  Command* nextCommand();

  /** Parse and return the next expression. */
  Term nextExpression();

 private:
  /** Initialize this input parser, called during construction */
  void initialize();
  /** Solver */
  Solver* d_solver;
  /** The allocated symbol manager */
  std::unique_ptr<SymbolManager> d_allocSm;
  /** Symbol manager */
  SymbolManager* d_sm;
  /** whether to use flex */
  bool d_useFlex;
  /** Incremental string input language */
  std::string d_istringLang;
  /** Incremental string name */
  std::string d_istringName;
  //!!!!!!!!!!!!!! TODO: this implementation is deprecated and should be
  // replaced (wishue #142).
  /**  The parser state. */
  std::unique_ptr<Parser> d_state;
  /** The underlying input */
  std::unique_ptr<Input> d_input;
  //!!!!!!!!!!!!!!
  //!!!!!!!!!!!!!! new implementation
  std::unique_ptr<FlexParser> d_fparser;
  //!!!!!!!!!!!!!!
};

}  // namespace parser
}  // namespace cvc5

#endif
