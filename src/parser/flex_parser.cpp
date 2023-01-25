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
 * Base class for Flex parsing.
 */

#include "parser/flex_parser.h"

#include "base/check.h"
#include "base/output.h"
#include "parser/parser_exception.h"
#include "parser/flex_lexer.h"

namespace cvc5 {
namespace parser {

FlexParser::FlexParser(Solver* solver, SymbolManager* sm)
    : d_solver(solver), d_sm(sm), d_lex(nullptr), d_done(true)
{
}

void FlexParser::setFileInput(const std::string& filename)
{
  d_flexInput = FlexInput::mkFileInput(filename);
  initializeInput(filename);
}

void FlexParser::setStreamInput(std::istream& input, const std::string& name)
{
  d_flexInput = FlexInput::mkStreamInput(input);
  initializeInput(name);
  d_done = false;
  d_lex->initialize(d_flexInput->getStream(), name);
}

void FlexParser::setStringInput(const std::string& input,
                                const std::string& name)
{
  d_flexInput = FlexInput::mkStringInput(input);
  initializeInput(name);
}

void FlexParser::initializeInput(const std::string& name)
{
  d_done = false;
  d_lex->initialize(d_flexInput->getStream(), name);
}

void FlexParser::warning(const std::string& msg) { d_lex->warning(msg); }

void FlexParser::parseError(const std::string& msg) { d_lex->parseError(msg); }

void FlexParser::unexpectedEOF(const std::string& msg)
{
  d_lex->parseError(msg, true);
}

void FlexParser::preemptCommand(Command* cmd) { d_commandQueue.push_back(cmd); }

Command* FlexParser::nextCommand()
{
  Trace("parser") << "nextCommand()" << std::endl;
  Command* cmd = nullptr;
  if (!d_commandQueue.empty())
  {
    cmd = d_commandQueue.front();
    d_commandQueue.pop_front();
    setDone(cmd == nullptr);
  }
  else
  {
    try
    {
      cmd = parseNextCommand();
      d_commandQueue.push_back(cmd);
      cmd = d_commandQueue.front();
      d_commandQueue.pop_front();
      setDone(cmd == nullptr);
    }
    catch (ParserException& e)
    {
      setDone();
      throw;
    }
    catch (std::exception& e)
    {
      setDone();
      parseError(e.what());
    }
  }
  Trace("parser") << "nextCommand() => " << cmd << std::endl;
  return cmd;
}

Term FlexParser::nextExpression()
{
  Trace("parser") << "nextExpression()" << std::endl;
  Term result;
  if (!d_done)
  {
    try
    {
      result = parseNextExpression();
      setDone(result.isNull());
    }
    catch (ParserException& e)
    {
      setDone();
      throw;
    }
    catch (std::exception& e)
    {
      setDone();
      parseError(e.what());
    }
  }
  Trace("parser") << "nextExpression() => " << result << std::endl;
  return result;
}

}  // namespace parser
}  // namespace cvc5
