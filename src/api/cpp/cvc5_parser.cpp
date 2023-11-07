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

#include "api/cpp/cvc5_checks.h"
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

/**
 * The base check macro.
 * Throws a CVC5ApiException if 'cond' is false.
 */
#define CVC5_PARSER_API_CHECK(cond) \
  CVC5_PREDICT_TRUE(cond)           \
  ? (void)0                         \
  : cvc5::internal::OstreamVoider() & CVC5ParserApiExceptionStream().ostream()

class CVC5ParserApiExceptionStream
{
 public:
  CVC5ParserApiExceptionStream() {}
  /* Note: This needs to be explicitly set to 'noexcept(false)' since it is
   * a destructor that throws an exception and in C++11 all destructors
   * default to noexcept(true) (else this triggers a call to std::terminate). */
  ~CVC5ParserApiExceptionStream() noexcept(false)
  {
    if (std::uncaught_exceptions() == 0)
    {
      throw CVC5ApiException(d_stream.str());
    }
  }
  std::ostream& ostream() { return d_stream; }

 private:
  std::stringstream d_stream;
};

/* -------------------------------------------------------------------------- */
/* SymbolManager                                                              */
/* -------------------------------------------------------------------------- */

SymbolManager::SymbolManager(cvc5::Solver* s) { d_sm.reset(new SymManager(s)); }

SymbolManager::~SymbolManager() {}

bool SymbolManager::isLogicSet() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_sm->isLogicSet();
  ////////
  CVC5_API_TRY_CATCH_END;
}
const std::string& SymbolManager::getLogic() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_PARSER_API_CHECK(d_sm->isLogicSet())
      << "Invalid call to 'getLogic', logic has not yet been set";
  //////// all checks before this line
  return d_sm->getLogic();
  ////////
  CVC5_API_TRY_CATCH_END;
}

SymManager* SymbolManager::toSymManager() { return d_sm.get(); }

/* -------------------------------------------------------------------------- */
/* Command                                                                    */
/* -------------------------------------------------------------------------- */

Command::Command() {}

Command::Command(std::shared_ptr<Cmd> cmd) : d_cmd(cmd) {}

bool Command::isNull() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_cmd == nullptr;
  ////////
  CVC5_API_TRY_CATCH_END;
}

void Command::invoke(cvc5::Solver* solver,
                     parser::SymbolManager* sm,
                     std::ostream& out)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_PARSER_API_CHECK(d_cmd != nullptr) << "Invoking a null command";
  //////// all checks before this line
  d_cmd->invoke(solver, sm->toSymManager(), out);
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Command::toString() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  if (d_cmd == nullptr)
  {
    return "null";
  }
  return d_cmd->toString();
  ////////
  CVC5_API_TRY_CATCH_END;
}

std::string Command::getCommandName() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_PARSER_API_CHECK(d_cmd != nullptr)
      << "getCommandName called on a null command";
  //////// all checks before this line
  return d_cmd->getCommandName();
  ////////
  CVC5_API_TRY_CATCH_END;
}

Cmd* Command::toCmd() { return d_cmd.get(); }

std::ostream& operator<<(std::ostream& out, const Command& c)
{
  out << c.toString();
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
  SymManager* sm = d_sm->toSymManager();
  // process the forced logic
  auto info = d_solver->getOptionInfo("force-logic");
  if (info.setByUser)
  {
    internal::LogicInfo tmp(info.stringValue());
    std::string logic = tmp.getLogicString();
    // set the logic in the solver if not done so already
    if (!d_solver->isLogicSet())
    {
      d_solver->setLogic(logic);
    }
    // set the logic in the symbol manager, marking as forced
    sm->setLogic(logic, true);
  }
  info = d_solver->getOptionInfo("global-declarations");
  if (info.setByUser)
  {
    sm->setGlobalDeclarations(info.boolValue());
  }
  info = d_solver->getOptionInfo("fresh-declarations");
  if (info.setByUser)
  {
    sm->setFreshDeclarations(info.boolValue());
  }
  // notice that we don't create the parser object until the input is set.
}

void InputParser::initializeInternal()
{
  SymManager* sm = d_sm->toSymManager();
  bool slvLogicSet = d_solver->isLogicSet();
  bool smLogicSet = sm->isLogicSet();
  bool initParserLogic = false;
  std::string initLogic;
  if (slvLogicSet)
  {
    initParserLogic = true;
    initLogic = d_solver->getLogic();
    if (smLogicSet)
    {
      // both set, ensure they are the same
      std::string smLogic = sm->getLogic();
      if (initLogic != smLogic)
      {
        std::stringstream ss;
        ss << "Logic mismatch when initializing InputParser." << std::endl;
        ss << "The solver's logic: " << initLogic << std::endl;
        ss << "The symbol manager's logic: " << smLogic << std::endl;
        throw CVC5ApiException(ss.str());
      }
    }
    else
    {
      // ensure the symbol manager's logic is set
      sm->setLogic(initLogic);
    }
  }
  else if (smLogicSet)
  {
    // solver logic not set, symbol manager set
    initParserLogic = true;
    initLogic = sm->getLogic();
    // ensure the solver's logic is set
    d_solver->setLogic(initLogic);
  }
  // If we have already set the logic in the symbol manager or the solver, set
  // it in the parser, which impacts which symbols are created.
  if (initParserLogic)
  {
    d_parser->setLogic(initLogic);
  }
}

Solver* InputParser::getSolver() { return d_solver; }

SymbolManager* InputParser::getSymbolManager() { return d_sm; }

Command InputParser::nextCommand()
{
  CVC5_PARSER_API_CHECK(d_parser != nullptr)
      << "Input to parser not initialized";
  //////// all checks before this line
  Trace("parser") << "nextCommand()" << std::endl;
  std::shared_ptr<Cmd> cmd = d_parser->nextCommand();
  return Command(cmd);
}

Term InputParser::nextTerm()
{
  CVC5_PARSER_API_CHECK(d_parser != nullptr)
      << "Input to parser not initialized";
  //////// all checks before this line
  Trace("parser") << "nextTerm()" << std::endl;
  return d_parser->nextTerm();
}

void InputParser::setFileInput(modes::InputLanguage lang,
                               const std::string& filename)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  Trace("parser") << "setFileInput(" << lang << ", " << filename << ")"
                  << std::endl;
  d_parser = Parser::mkParser(lang, d_solver, d_sm->toSymManager());
  initializeInternal();
  d_parser->setFileInput(filename);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void InputParser::setStreamInput(modes::InputLanguage lang,
                                 std::istream& input,
                                 const std::string& name)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  Trace("parser") << "setStreamInput(" << lang << ", ..., " << name << ")"
                  << std::endl;
  d_parser = Parser::mkParser(lang, d_solver, d_sm->toSymManager());
  initializeInternal();
  d_parser->setStreamInput(input, name);
  ////////
  CVC5_API_TRY_CATCH_END;
}

void InputParser::setIncrementalStringInput(modes::InputLanguage lang,
                                            const std::string& name)
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  Trace("parser") << "setIncrementalStringInput(" << lang << ", ..., " << name
                  << ")" << std::endl;
  d_istringLang = lang;
  d_istringName = name;
  // initialize the parser
  d_parser = Parser::mkParser(lang, d_solver, d_sm->toSymManager());
  initializeInternal();
  ////////
  CVC5_API_TRY_CATCH_END;
}
void InputParser::appendIncrementalStringInput(const std::string& input)
{
  CVC5_API_TRY_CATCH_BEGIN;
  CVC5_PARSER_API_CHECK(d_parser != nullptr)
      << "Input to parser not initialized";
  //////// all checks before this line
  Trace("parser") << "appendIncrementalStringInput(...)" << std::endl;
  d_parser->setStringInput(input, d_istringName);
  ////////
  CVC5_API_TRY_CATCH_END;
}

bool InputParser::done() const
{
  CVC5_API_TRY_CATCH_BEGIN;
  //////// all checks before this line
  return d_parser == nullptr || d_parser->done();
  ////////
  CVC5_API_TRY_CATCH_END;
}

}  // namespace parser
}  // namespace cvc5
