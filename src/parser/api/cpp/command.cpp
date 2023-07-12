/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of command objects.
 */

#include "parser/api/cpp/command.h"

#include <exception>
#include <iostream>
#include <iterator>
#include <sstream>
#include <utility>
#include <vector>

#include "base/check.h"
#include "base/modal_exception.h"
#include "base/output.h"
#include "expr/node_manager.h"
#include "options/io_utils.h"
#include "options/main_options.h"
#include "options/options.h"
#include "options/printer_options.h"
#include "options/smt_options.h"
#include "parser/api/cpp/symbol_manager.h"
#include "printer/printer.h"
#include "proof/unsat_core.h"
#include "util/smt2_quote_string.h"
#include "util/utility.h"

using namespace std;
using namespace cvc5::parser;

namespace cvc5::parser {

/* -------------------------------------------------------------------------- */
/* class Command                                                              */
/* -------------------------------------------------------------------------- */

Command::Command() : d_commandStatus(nullptr), d_muted(false) {}

Command::Command(const Command& cmd)
{
  d_commandStatus =
      (cmd.d_commandStatus == NULL) ? NULL : &cmd.d_commandStatus->clone();
  d_muted = cmd.d_muted;
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

void Command::invoke(cvc5::Solver* solver, SymbolManager* sm, std::ostream& out)
{
  invoke(solver, sm);
  if (!ok())
  {
    out << *d_commandStatus;
  }
  else if (!isMuted())
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

void Command::resetSolver(cvc5::Solver* solver)
{
  std::unique_ptr<internal::Options> opts =
      std::make_unique<internal::Options>();
  opts->copyValues(*solver->d_originalOptions);
  // This reconstructs a new solver object at the same memory location as the
  // current one. Note that this command does not own the solver object!
  // It may be safer to instead make the ResetCommand a special case in the
  // CommandExecutor such that this reconstruction can be done within the
  // CommandExecutor, who actually owns the solver.
  solver->~Solver();
  new (solver) cvc5::Solver(std::move(opts));
}

internal::Node Command::termToNode(const cvc5::Term& term)
{
  return term.getNode();
}

std::vector<internal::Node> Command::termVectorToNodes(
    const std::vector<cvc5::Term>& terms)
{
  return cvc5::Term::termVectorToNodes(terms);
}

internal::TypeNode Command::sortToTypeNode(const cvc5::Sort& sort)
{
  return sort.getTypeNode();
}

std::vector<internal::TypeNode> Command::sortVectorToTypeNodes(
    const std::vector<cvc5::Sort>& sorts)
{
  return cvc5::Sort::sortVectorToTypeNodes(sorts);
}

internal::TypeNode Command::grammarToTypeNode(cvc5::Grammar* grammar)
{
  return grammar == nullptr ? internal::TypeNode::null()
                            : sortToTypeNode(grammar->resolve());
}

}  // namespace cvc5::parser
