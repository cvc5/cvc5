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
 * The interface for parsing an input with a parser.
 */

#include "parser/api/cpp/input_parser.h"

#include "base/check.h"
#include "base/output.h"
#include "parser/api/cpp/command.h"
#include "parser/input.h"
#include "parser/parser_builder.h"
#include "theory/logic_info.h"

namespace cvc5 {
namespace parser {

InputParser::InputParser(Solver* solver, SymbolManager* sm)
    : d_solver(solver), d_allocSm(nullptr), d_sm(sm)
{
  initialize();
}

InputParser::InputParser(Solver* solver)
    : d_solver(solver),
      d_allocSm(new SymbolManager(solver)),
      d_sm(d_allocSm.get())
{
  initialize();
}

void InputParser::initialize()
{
  d_useFlex = d_solver->getOptionInfo("flex-parser").boolValue();
  // flex not supported with TPTP yet
  if (d_solver->getOption("input-language") == "LANG_TPTP")
  {
    d_useFlex = false;
  }
  if (d_useFlex)
  {
    // process the forced logic
    auto info = d_solver->getOptionInfo("force-logic");
    if (info.setByUser)
    {
      internal::LogicInfo tmp(info.stringValue());
      d_sm->setLogic(tmp.getLogicString(), true);
    }
  }
  else
  {
    // Allocate an ANTLR parser
    ParserBuilder parserBuilder(d_solver, d_sm, true);
    d_state = parserBuilder.build();
  }
  // if flex, don't make anything yet
}

Solver* InputParser::getSolver() { return d_solver; }

SymbolManager* InputParser::getSymbolManager() { return d_sm; }

void InputParser::setLogic(const std::string& name)
{
  if (d_useFlex)
  {
    d_sm->setLogic(name);
    d_fparser->setLogic(name);
  }
  else
  {
    // not supported in ANTLR
    Unhandled() << "set-logic not supported in input parser using ANTLR.";
  }
}

std::unique_ptr<Command> InputParser::nextCommand()
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

void InputParser::setIncrementalStringInput(const std::string& lang,
                                            const std::string& name)
{
  Trace("parser") << "setIncrementalStringInput(" << lang << ", ..., " << name
                  << ")" << std::endl;
  d_istringLang = lang;
  d_istringName = name;
  if (d_useFlex)
  {
    // initialize the parser
    d_fparser = FlexParser::mkFlexParser(lang, d_solver, d_sm);
  }
  // if ANTLR, parser is already initialized
}
void InputParser::appendIncrementalStringInput(const std::string& input)
{
  Trace("parser") << "appendIncrementalStringInput(...)" << std::endl;
  if (d_useFlex)
  {
    d_fparser->setStringInput(input, d_istringName);
  }
  else
  {
    d_state->setInput(
        Input::newStringInput(d_istringLang, input, d_istringName));
  }
}

}  // namespace parser
}  // namespace cvc5
