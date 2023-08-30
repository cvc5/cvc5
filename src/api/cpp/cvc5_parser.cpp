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

#include <cvc5/cvc5_parser.h>

#include <iostream>

#include "base/check.h"
#include "base/output.h"
#include "expr/node_manager.h"
#include "parser/command_status.h"
#include "parser/commands.h"
#include "parser/parser.h"
#include "parser/sym_manager.h"
#include "theory/logic_info.h"

namespace cvc5 {
namespace parser {

/* -------------------------------------------------------------------------- */
/* SymbolManager                                                              */
/* -------------------------------------------------------------------------- */

SymbolManager::SymbolManager(cvc5::Solver* s) { d_sm.reset(new SymManager(s)); }

SymbolManager::~SymbolManager() {}

SymManager* SymbolManager::toSymManager() { return d_sm.get(); }

/* -------------------------------------------------------------------------- */
/* Command                                                                    */
/* -------------------------------------------------------------------------- */

Command::Command() : d_cmd(nullptr) {}

Command::Command(const Command& cmd) { d_cmd = cmd.d_cmd; }

Command::Command(std::shared_ptr<Cmd> cmd) : d_cmd(cmd) {}

Command::~Command() {}

bool Command::ok() const { return d_cmd->ok(); }

bool Command::fail() const { return d_cmd->fail(); }

bool Command::interrupted() const { return d_cmd->interrupted(); }

void Command::invoke(cvc5::Solver* solver,
                     parser::SymbolManager* sm,
                     std::ostream& out)
{
  d_cmd->invoke(solver, sm->toSymManager(), out);
}

std::string Command::toString() const { return d_cmd->toString(); }

std::string Command::getCommandName() const { return d_cmd->getCommandName(); }

Cmd* Command::toCmd() { return d_cmd.get(); }

std::ostream& operator<<(std::ostream& out, const Command& c)
{
  out << c.toString();
  return out;
}

std::ostream& operator<<(std::ostream& out, const Command* c)
{
  if (c == nullptr)
  {
    out << "null";
  }
  else
  {
    out << *c;
  }
  return out;
}

/* -------------------------------------------------------------------------- */
/* InputParser                                                                */
/* -------------------------------------------------------------------------- */

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
    d_sm->toSymManager()->setLogic(tmp.getLogicString(), true);
  }
  info = d_solver->getOptionInfo("global-declarations");
  if (info.setByUser)
  {
    d_sm->toSymManager()->setGlobalDeclarations(info.boolValue());
  }
  info = d_solver->getOptionInfo("fresh-declarations");
  if (info.setByUser)
  {
    d_sm->toSymManager()->setFreshDeclarations(info.boolValue());
  }
  // notice that we don't create the parser object until the input is set.
}

Solver* InputParser::getSolver() { return d_solver; }

SymbolManager* InputParser::getSymbolManager() { return d_sm; }

void InputParser::setLogic(const std::string& name)
{
  Assert(d_fparser != nullptr);
  d_sm->toSymManager()->setLogic(name);
  d_fparser->setLogic(name);
}

std::unique_ptr<Command> InputParser::nextCommand()
{
  Assert(d_fparser != nullptr);
  Trace("parser") << "nextCommand()" << std::endl;
  std::shared_ptr<Cmd> cmd = d_fparser->nextCommand();
  if (cmd == nullptr)
  {
    return nullptr;
  }
  std::unique_ptr<Command> cc;
  cc.reset(new Command(cmd));
  return cc;
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
  d_fparser = Parser::mkParser(lang, d_solver, d_sm->toSymManager());
  d_fparser->setFileInput(filename);
}

void InputParser::setStreamInput(const std::string& lang,
                                 std::istream& input,
                                 const std::string& name)
{
  Trace("parser") << "setStreamInput(" << lang << ", ..., " << name << ")"
                  << std::endl;
  d_fparser = Parser::mkParser(lang, d_solver, d_sm->toSymManager());
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
  d_fparser = Parser::mkParser(lang, d_solver, d_sm->toSymManager());
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
