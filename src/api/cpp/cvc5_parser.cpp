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

#include "base/check.h"
#include "base/output.h"
#include "parser/command_status.h"
#include "parser/commands.h"
#include "parser/parser.h"
#include "parser/sym_manager.h"
#include "theory/logic_info.h"

namespace cvc5 {
namespace parser {

SymbolManager::SymbolManager(cvc5::Solver* s) { d_sm.reset(new SymManager(s)); }

SymbolManager::~SymbolManager() {}

SymManager* SymbolManager::get() { return d_sm.get(); }

Command::Command() : d_commandStatus(nullptr) {}

Command::Command(const Command& cmd)
{
  d_commandStatus =
      (cmd.d_commandStatus == NULL) ? NULL : &cmd.d_commandStatus->clone();
}

Command::~Command()
{
  if (d_commandStatus != NULL && d_commandStatus != CommandSuccess::instance())
  {
    delete d_commandStatus;
  }
}

bool Command::ok() const
{
  // either we haven't run the command yet, or it ran successfully
  return d_commandStatus == NULL
         || dynamic_cast<const CommandSuccess*>(d_commandStatus) != NULL;
}

bool Command::fail() const
{
  return d_commandStatus != NULL
         && dynamic_cast<const CommandFailure*>(d_commandStatus) != NULL;
}

bool Command::interrupted() const
{
  return d_commandStatus != NULL
         && dynamic_cast<const CommandInterrupted*>(d_commandStatus) != NULL;
}

void Command::invoke(cvc5::Solver* solver,
                     parser::SymbolManager* sm,
                     std::ostream& out)
{
  invokeInternal(solver, sm->get(), out);
}
void Command::invokeInternal(cvc5::Solver* solver,
                             parser::SymManager* sm,
                             std::ostream& out)
{
  invokeInternal(solver, sm);
  if (!ok())
  {
    out << *d_commandStatus;
  }
  else
  {
    printResult(solver, out);
  }
  // always flush the output
  out << std::flush;
}

std::string Command::toString() const
{
  std::stringstream ss;
  toStream(ss);
  return ss.str();
}

void Command::printResult(cvc5::Solver* solver, std::ostream& out) const
{
  if (!ok()
      || (d_commandStatus != nullptr
          && solver->getOption("print-success") == "true"))
  {
    out << *d_commandStatus;
  }
}

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
    d_sm->get()->setLogic(tmp.getLogicString(), true);
  }
  // notice that we don't create the parser object until the input is set.
}

Solver* InputParser::getSolver() { return d_solver; }

SymbolManager* InputParser::getSymbolManager() { return d_sm; }

void InputParser::setLogic(const std::string& name)
{
  Assert(d_fparser != nullptr);
  d_sm->get()->setLogic(name);
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
  d_fparser = Parser::mkParser(lang, d_solver, d_sm->get());
  d_fparser->setFileInput(filename);
}

void InputParser::setStreamInput(const std::string& lang,
                                 std::istream& input,
                                 const std::string& name)
{
  Trace("parser") << "setStreamInput(" << lang << ", ..., " << name << ")"
                  << std::endl;
  d_fparser = Parser::mkParser(lang, d_solver, d_sm->get());
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
  d_fparser = Parser::mkParser(lang, d_solver, d_sm->d_sm.get());
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
