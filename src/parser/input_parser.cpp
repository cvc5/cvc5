/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The interface for parsing an input with a parser.
 */

#include "parser/input_parser.h"

#include "base/output.h"
#include "parser/input.h"
#include "parser/parser_builder.h"
#include "parser/api/cpp/command.h"

namespace cvc5 {
namespace parser {

  /*
std::unique_ptr<InputParser> Parser::parseFile(const std::string& fname,
                                               bool useMmap)
{
  d_input = Input::newFileInput(d_lang, fname, useMmap);
  d_input->setParser(*this);
  d_done = false;
  return std::unique_ptr<InputParser>(new InputParser(this, d_input));
}

std::unique_ptr<InputParser> Parser::parseStream(const std::string& name,
                                                 std::istream& stream)
{
  d_input = Input::newStreamInput(d_lang, stream, name);
  d_input->setParser(*this);
  d_done = false;
  return std::unique_ptr<InputParser>(new InputParser(this, d_input));
}

std::unique_ptr<InputParser> Parser::parseString(const std::string& name,
                                                 const std::string& str)
{
  d_input = Input::newStringInput(d_lang, str, name);
  d_input->setParser(*this);
  d_done = false;
  return std::unique_ptr<InputParser>(new InputParser(this, d_input));
}
*/

InputParser::InputParser(Solver* solver, SymbolManager* sm, bool useOptions)
{
  ParserBuilder parserBuilder(
      solver, sm, useOptions);
  d_state = parserBuilder.build();
}

Command* InputParser::nextCommand()
{
  Trace("parser") << "nextCommand()" << std::endl;
  return d_state->nextCommand();
}

Term InputParser::nextExpression()
{
  Trace("parser") << "nextExpression()" << std::endl;
  return d_state->nextExpression();
}

void InputParser::forceLogic(const std::string& logic)
{
  d_state->forceLogic(logic);
}

void InputParser::setInput(Input* input)
{
  d_state->setInput(input);
}


}  // namespace parser
}  // namespace cvc5
