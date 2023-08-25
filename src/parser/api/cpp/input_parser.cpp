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
#include "parser/api/cpp/symbol_manager.h"
#include "parser/parser.h"
#include "parser/sym_manager.h"
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
    std::string logic = tmp.getLogicString();
    // Setting the logic in the symbol manager for the first time
    // corresponds to setting the logic in the solver.
    SymManager * sm = d_sm->get();
    if (!sm->isLogicSet())
    {
      d_solver->setLogic(logic);
    }
    sm->setLogic(logic, true);
  }
  info = d_solver->getOptionInfo("global-declarations");
  if (info.setByUser)
  {
    d_sm->get()->setGlobalDeclarations(info.boolValue());
  }
  info = d_solver->getOptionInfo("fresh-declarations");
  if (info.setByUser)
  {
    d_sm->get()->setFreshDeclarations(info.boolValue());
  }
  // notice that we don't create the parser object until the input is set.
}

void InputParser::initializeInternal()
{
  SymManager * sm = d_sm->get();
  // If we have already set the logic in the symbol manager, set it in the
  // parser, which impacts which symbols are created.
  if (sm->isLogicSet())
  {
    d_parser->setLogic(sm->getLogic());
  }
}

Solver* InputParser::getSolver() { return d_solver; }

SymbolManager* InputParser::getSymbolManager() { return d_sm; }

std::unique_ptr<Command> InputParser::nextCommand()
{
  Assert(d_parser != nullptr);
  Trace("parser") << "nextCommand()" << std::endl;
  return d_parser->nextCommand();
}

Term InputParser::nextExpression()
{
  Assert(d_parser != nullptr);
  Trace("parser") << "nextExpression()" << std::endl;
  return d_parser->nextExpression();
}

void InputParser::setFileInput(const std::string& lang,
                               const std::string& filename)
{
  Trace("parser") << "setFileInput(" << lang << ", " << filename << ")"
                  << std::endl;
  d_parser = Parser::mkParser(lang, d_solver, d_sm->get());
  initializeInternal();
  d_parser->setFileInput(filename);
}

void InputParser::setStreamInput(const std::string& lang,
                                 std::istream& input,
                                 const std::string& name)
{
  Trace("parser") << "setStreamInput(" << lang << ", ..., " << name << ")"
                  << std::endl;
  d_parser = Parser::mkParser(lang, d_solver, d_sm->get());
  initializeInternal();
  d_parser->setStreamInput(input, name);
}

void InputParser::setIncrementalStringInput(const std::string& lang,
                                            const std::string& name)
{
  Trace("parser") << "setIncrementalStringInput(" << lang << ", ..., " << name
                  << ")" << std::endl;
  d_istringLang = lang;
  d_istringName = name;
  // initialize the parser
  d_parser = Parser::mkParser(lang, d_solver, d_sm->d_sm.get());
  initializeInternal();
}
void InputParser::appendIncrementalStringInput(const std::string& input)
{
  Assert(d_parser != nullptr);
  Trace("parser") << "appendIncrementalStringInput(...)" << std::endl;
  d_parser->setStringInput(input, d_istringName);
}

bool InputParser::done() const
{
  return d_parser == nullptr || d_parser->done();
}

}  // namespace parser
}  // namespace cvc5
