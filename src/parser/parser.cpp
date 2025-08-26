/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
#include "parser/commands.h"
#include "parser/lexer.h"
#include <cvc5/cvc5_parser.h>
#include "parser/smt2/smt2_parser.h"

namespace cvc5 {
namespace parser {

Parser::Parser(Solver* solver, SymManager* sm)
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

std::unique_ptr<Cmd> Parser::nextCommand()
{
  Trace("parser") << "nextCommand()" << std::endl;
  std::unique_ptr<Cmd> cmd;
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

Term Parser::nextTerm()
{
  Trace("parser") << "nextTerm()" << std::endl;
  Term result;
  if (!d_done)
  {
    try
    {
      result = parseNextTerm();
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
  Trace("parser") << "nextTerm() => " << result << std::endl;
  return result;
}

bool Parser::done() const { return d_done; }

std::unique_ptr<Parser> Parser::mkParser(modes::InputLanguage lang,
                                         Solver* solver,
                                         SymManager* sm)
{
  std::unique_ptr<Parser> parser;
  if (lang == modes::InputLanguage::SMT_LIB_2_6
      || lang == modes::InputLanguage::SYGUS_2_1)
  {
    bool isSygus = (lang == modes::InputLanguage::SYGUS_2_1);
    ParsingMode parsingMode = ParsingMode::DEFAULT;
    std::string mode = solver->getOption("parsing-mode");
    if (mode == "strict")
    {
      parsingMode = ParsingMode::STRICT;
    }
    else if (mode == "lenient")
    {
      parsingMode = ParsingMode::LENIENT;
    }
    parser.reset(new Smt2Parser(solver, sm, parsingMode, isSygus));
  }
  else
  {
    Unhandled() << "unable to detect input file format, try --lang";
  }
  return parser;
}

}  // namespace parser
}  // namespace cvc5
