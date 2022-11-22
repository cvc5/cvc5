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
{
  // Allocate an ANTLR parser
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

void InputParser::setFileInput(const std::string& lang,
                               const std::string& filename)
{
  Trace("parser") << "setFileInput(" << lang << ", " << filename << ")"
                  << std::endl;
  Smt2Lexer slex;
  Trace("ajr-temp") << "Set file to " << filename << std::endl;
  slex.setFileInput(filename);
  Trace("ajr-temp") << "Get tokens" << std::endl;
  Token t;
  while ((t = slex.next_token()) != Token::EOF_TOK)
  {
    Trace("ajr-temp") << "token: " << t << std::endl;
  }
  Trace("ajr-temp") << "Finished" << std::endl;
  exit(1);

  d_state->setInput(Input::newFileInput(lang, filename));
}

void InputParser::setStreamInput(const std::string& lang,
                                 std::istream& input,
                                 const std::string& name)
{
  Trace("parser") << "setStreamInput(" << lang << ", ..., " << name << ")"
                  << std::endl;
  d_state->setInput(Input::newStreamInput(lang, input, name));
}

void InputParser::setStringInput(const std::string& lang,
                                 const std::string& input,
                                 const std::string& name)
{
  Trace("parser") << "setStringInput(" << lang << ", ..., " << name << ")"
                  << std::endl;
  d_state->setInput(Input::newStringInput(lang, input, name));
}

}  // namespace parser
}  // namespace cvc5
