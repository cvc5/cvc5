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
 * Base class for  parsing.
 */

#include "parser/parser.h"

#include "base/check.h"
#include "base/output.h"
#include "parser/api/cpp/command.h"
#include "parser/lexer.h"
#include "parser/parser_exception.h"
#include "parser/smt2/smt2_parser.h"

namespace cvc5 {
namespace parser {

Parser::Parser(Solver* solver, SymbolManager* sm)
    : d_solver(solver), d_sm(sm), d_lex(nullptr), d_done(true)
{
}

void Parser::setLogic(const std::string& name) {}

void Parser::setFileInput(const std::string& filename)
{
  d_flexInput = Input::mkFileInput(filename);
  initializeInput(filename);
}

void Parser::setStreamInput(std::istream& input, const std::string& name)
{
  d_flexInput = Input::mkStreamInput(input);
  initializeInput(name);
}

void Parser::setStringInput(const std::string& input,
                                const std::string& name)
{
  d_flexInput = Input::mkStringInput(input);
  initializeInput(name);
}

void Parser::initializeInput(const std::string& name)
{
  d_done = false;
  d_lex->initialize(d_flexInput.get(), name);
}

void Parser::warning(const std::string& msg) { d_lex->warning(msg); }

void Parser::parseError(const std::string& msg) { d_lex->parseError(msg); }

void Parser::unexpectedEOF(const std::string& msg)
{
  d_lex->parseError(msg, true);
}

std::unique_ptr<Command> Parser::nextCommand()
{
  Trace("parser") << "nextCommand()" << std::endl;
  std::unique_ptr<Command> cmd;
  try
  {
    cmd = parseNextCommand();
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
  Trace("parser") << "nextCommand() => " << cmd.get() << std::endl;
  return cmd;
}

Term Parser::nextExpression()
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

bool Parser::done() const { return d_done; }

std::unique_ptr<Parser> Parser::mkParser(const std::string& lang,
                                                     Solver* solver,
                                                     SymbolManager* sm)
{
  std::unique_ptr<Parser> parser;
  if (lang == "LANG_SYGUS_V2" || lang == "LANG_SMTLIB_V2_6")
  {
    bool isSygus = (lang == "LANG_SYGUS_V2");
    bool strictMode = solver->getOptionInfo("strict-parsing").boolValue();
    parser.reset(new Smt2Parser(solver, sm, strictMode, isSygus));
  }
  else
  {
    Unhandled() << "unable to detect input file format, try --lang";
  }
  return parser;
}

}  // namespace parser
}  // namespace cvc5
