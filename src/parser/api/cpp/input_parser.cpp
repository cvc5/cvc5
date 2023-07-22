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
  // process the forced logic
  auto info = d_solver->getOptionInfo("force-logic");
  if (info.setByUser)
  {
    internal::LogicInfo tmp(info.stringValue());
    d_sm->setLogic(tmp.getLogicString(), true);
  }
  // notice that we don't create the parser object until the input is set.
}

Solver* InputParser::getSolver() { return d_solver; }

SymbolManager* InputParser::getSymbolManager() { return d_sm; }

void InputParser::setLogic(const std::string& name)
{
  Assert(d_fparser != nullptr);
  d_sm->setLogic(name);
  d_fparser->setLogic(name);
}

std::unique_ptr<Command> InputParser::nextCommand()
{
  Assert(d_fparser != nullptr);
  Trace("parser") << "nextCommand()" << std::endl;
  return d_fparser->nextCommand();
}

Term InputParser::nextExpression()
{
  Assert(d_fparser != nullptr);
  Trace("parser") << "nextExpression()" << std::endl;
  return d_fparser->nextExpression();
}

void InputParser::setFileInput(const std::string& lang,
                               const std::string& filename)
{
  Trace("parser") << "setFileInput(" << lang << ", " << filename << ")"
                  << std::endl;
  d_fparser = Parser::mkParser(lang, d_solver, d_sm);
  d_fparser->setFileInput(filename);
}

void InputParser::setStreamInput(const std::string& lang,
                                 std::istream& input,
                                 const std::string& name)
{
  Trace("parser") << "setStreamInput(" << lang << ", ..., " << name << ")"
                  << std::endl;
  d_fparser = Parser::mkParser(lang, d_solver, d_sm);
  d_fparser->setStreamInput(input, name);
}

void InputParser::setIncrementalStringInput(const std::string& lang,
                                            const std::string& name)
{
  Trace("parser") << "setIncrementalStringInput(" << lang << ", ..., " << name
                  << ")" << std::endl;
  d_istringLang = lang;
  d_istringName = name;
  // initialize the parser
  d_fparser = Parser::mkParser(lang, d_solver, d_sm);
}
void InputParser::appendIncrementalStringInput(const std::string& input)
{
  Assert(d_fparser != nullptr);
  Trace("parser") << "appendIncrementalStringInput(...)" << std::endl;
  d_fparser->setStringInput(input, d_istringName);
}

bool InputParser::done() const
{
  return d_fparser == nullptr || d_fparser->done();
}

}  // namespace parser
}  // namespace cvc5
