/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "parser/api/cpp/command.h"
#include "parser/flex_lexer.h"
#include "parser/parser_exception.h"
#include "parser/smt2/smt2_parser.h"

namespace cvc5 {
namespace parser {

FlexParser::FlexParser(Solver* solver, SymbolManager* sm)
    : d_solver(solver), d_sm(sm), d_lex(nullptr), d_done(true)
{
}

void FlexParser::setLogic(const std::string& name) {}

void FlexParser::setFileInput(const std::string& filename)
{
  d_flexInput = FlexInput::mkFileInput(filename);
  initializeInput(filename);
}

void FlexParser::setStreamInput(std::istream& input, const std::string& name)
{
  d_flexInput = FlexInput::mkStreamInput(input);
  initializeInput(name);
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
  d_lex->initialize(d_flexInput.get(), name);
}

void FlexParser::warning(const std::string& msg) { d_lex->warning(msg); }

void FlexParser::parseError(const std::string& msg) { d_lex->parseError(msg); }

void FlexParser::unexpectedEOF(const std::string& msg)
{
  d_lex->parseError(msg, true);
}

void FlexParser::preemptCommand(std::unique_ptr<Command> cmd)
{
  d_commandQueue.push_back(std::move(cmd));
}

std::unique_ptr<Command> FlexParser::nextCommand()
{
  Trace("parser") << "nextCommand()" << std::endl;
  std::unique_ptr<Command> cmd;
  if (!d_commandQueue.empty())
  {
    cmd = std::move(d_commandQueue.front());
    d_commandQueue.pop_front();
    setDone(cmd == nullptr);
  }
  else
  {
    try
    {
      cmd = parseNextCommand();
      d_commandQueue.push_back(std::move(cmd));
      cmd = std::move(d_commandQueue.front());
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
  Trace("parser") << "nextCommand() => " << cmd.get() << std::endl;
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

std::unique_ptr<FlexParser> FlexParser::mkFlexParser(const std::string& lang,
                                                     Solver* solver,
                                                     SymbolManager* sm)
{
  std::unique_ptr<FlexParser> parser;
  if (lang == "LANG_SYGUS_V2" || lang == "LANG_SMTLIB_V2_6")
  {
    bool isSygus = (lang == "LANG_SYGUS_V2");
    bool strictMode = solver->getOptionInfo("strict-parsing").boolValue();
    parser.reset(new Smt2Parser(solver, sm, strictMode, isSygus));
  }
  else if (lang == "LANG_TPTP")
  {
    // TPTP is not supported
    Unhandled() << "the TPTP input language is not supported with flex.";
  }
  else
  {
    Unhandled() << "unable to detect input file format, try --lang";
  }
  return parser;
}

}  // namespace parser
}  // namespace cvc5
