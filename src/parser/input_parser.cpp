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
#include "parser/api/cpp/command.h"
#include "parser/input.h"
#include "parser/parser_builder.h"

namespace cvc5 {
namespace parser {

InputParser::InputParser(Solver* solver, SymbolManager* sm, bool useOptions)
{
  ParserBuilder parserBuilder(solver, sm, useOptions);
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

void InputParser::setInput(Input* input) { d_state->setInput(input); }

}  // namespace parser
}  // namespace cvc5
