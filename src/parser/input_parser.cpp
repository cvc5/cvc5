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
#include "parser/parser.h"
#include "smt/command.h"

namespace cvc5 {
namespace parser {

Command* InputParser::nextCommand()
{
  Debug("parser") << "nextCommand()" << std::endl;
  Command* cmd = nullptr;
  if (d_state->hasCommand())
  {
    cmd = d_state->getNextCommand();
    d_state->setDone(cmd == nullptr);
  }
  else
  {
    try
    {
      cmd = d_input->parseCommand();
      d_state->preemptCommand(cmd);
      cmd = d_state->getNextCommand();
      d_state->setDone(cmd == nullptr);
    }
    catch (ParserException& e)
    {
      d_state->setDone();
      throw;
    }
    catch (std::exception& e)
    {
      d_state->setDone();
      d_input->parseError(e.what());
    }
  }
  Debug("parser") << "nextCommand() => " << cmd << std::endl;
  return cmd;
}

api::Term InputParser::nextExpression()
{
  Debug("parser") << "nextExpression()" << std::endl;
  api::Term result;
  if (!d_state->done())
  {
    try
    {
      result = d_input->parseExpr();
      d_state->setDone(result.isNull());
    }
    catch (ParserException& e)
    {
      d_state->setDone();
      throw;
    }
    catch (std::exception& e)
    {
      d_state->setDone();
      d_input->parseError(e.what());
    }
  }
  Debug("parser") << "nextExpression() => " << result << std::endl;
  return result;
}

InputParser::InputParser(Parser* state, Input* input)
    : d_state(state), d_input(input)
{
}

}  // namespace parser
}  // namespace cvc5
