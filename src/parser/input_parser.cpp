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

#include "parser/input_parser.h"

#include "base/output.h"
#include "parser/api/cpp/command.h"
#include "parser/flex/smt2_lexer.h"
#include "parser/input.h"
#include "parser/parser_builder.h"

namespace cvc5 {
namespace parser {

InputParser::InputParser(Solver* solver, SymbolManager* sm, bool useOptions)
    : d_solver(solver), d_sm(sm), d_useOptions(useOptions)
{
  d_useFlex = solver->getOptionInfo("flex-parser").boolValue();
  if (d_useFlex)
  {
    // TODO: build parser state object?
  }
  else
  {
    // Allocate an ANTLR parser
    ParserBuilder parserBuilder(solver, sm, useOptions);
    d_state = parserBuilder.build();
  }
}

Command* InputParser::nextCommand()
{
  Trace("parser") << "nextCommand()" << std::endl;
  if (d_useFlex)
  {
    return d_fparser->nextCommand();
  }
  return d_state->nextCommand();
}

Term InputParser::nextExpression()
{
  Trace("parser") << "nextExpression()" << std::endl;
  if (d_useFlex)
  {
    return d_fparser->nextExpression();
  }
  return d_state->nextExpression();
}

void InputParser::setFileInput(const std::string& lang,
                               const std::string& filename)
{
  Trace("parser") << "setFileInput(" << lang << ", " << filename << ")"
                  << std::endl;
  if (d_useFlex)
  {
    d_fparser = FlexParser::mkFlexParser(lang, d_solver, d_sm);
    d_fparser->setFileInput(filename);
  }
  else
  {
    d_state->setInput(Input::newFileInput(lang, filename));
  }
}

void InputParser::setStreamInput(const std::string& lang,
                                 std::istream& input,
                                 const std::string& name)
{
  Trace("parser") << "setStreamInput(" << lang << ", ..., " << name << ")"
                  << std::endl;
  if (d_useFlex)
  {
    d_fparser = FlexParser::mkFlexParser(lang, d_solver, d_sm);
    d_fparser->setStreamInput(input, name);
  }
  else
  {
    d_state->setInput(Input::newStreamInput(lang, input, name));
  }
}

void InputParser::setStringInput(const std::string& lang,
                                 const std::string& input,
                                 const std::string& name)
{
  Trace("parser") << "setStringInput(" << lang << ", ..., " << name << ")"
                  << std::endl;
  if (d_useFlex)
  {
    d_fparser = FlexParser::mkFlexParser(lang, d_solver, d_sm);
    d_fparser->setStringInput(input, name);
  }
  else
  {
    d_state->setInput(Input::newStringInput(lang, input, name));
  }
}

}  // namespace parser
}  // namespace cvc5
