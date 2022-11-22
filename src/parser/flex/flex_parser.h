/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definitions of SMT2 tokens.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__FLEX_PARSER_H
#define CVC5__PARSER__FLEX_PARSER_H

#include <memory>
#include "api/cpp/cvc5.h"
#include "parser/flex/flex_input.h"

namespace cvc5 {
namespace parser {

class Command;
class SymbolManager;

/**
 */
class FlexParser
{
 public:
  FlexParser(Solver* solver, SymbolManager* sm);
  virtual ~FlexParser() {}
  /** Set the input for the given file.
   *
   * @param filename the input filename
   */
  void setFileInput(const std::string& filename);

  /** Set the input for the given stream.
   *
   * @param input the input stream
   * @param name the name of the stream, for use in error messages
   */
  void setStreamInput(std::istream& input, const std::string& name);

  /** Set the input for the given string
   *
   * @param input the input string
   * @param name the name of the stream, for use in error messages
   */
  void setStringInput(const std::string& input, const std::string& name);

  /**
   * Parse and return the next command.
   * NOTE: currently memory management of commands is handled internally.
   */
  virtual Command* nextCommand() = 0;

  /** Parse and return the next expression. */
  virtual Term nextExpression() = 0;

  /** make flex parser from language string */
  static std::unique_ptr<FlexParser> mkFlexParser(const std::string& lang,
                                                  Solver* solver,
                                                  SymbolManager* sm);

 protected:
  /** initialize input */
  virtual void initializeInput(std::istream& s,
                               const std::string& inputName) = 0;
  /** Solver */
  Solver* d_solver;
  /** Symbol manager */
  SymbolManager* d_sm;
  /** The flex input */
  std::unique_ptr<FlexInput> d_flexInput;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2_H */
