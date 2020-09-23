/*********************                                                        */
/*! \file command.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of command objects.
 **
 ** Implementation of command objects.
 **/

#include "smt/command.h"

#include <exception>
#include <iostream>
#include <iterator>
#include <sstream>
#include <utility>
#include <vector>

#include "api/cvc4cpp.h"
#include "base/check.h"
#include "base/output.h"
#include "expr/expr_iomanip.h"
#include "expr/node.h"
#include "expr/type.h"
#include "options/options.h"
#include "options/smt_options.h"
#include "printer/printer.h"
#include "smt/dump.h"
#include "smt/model.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "util/sexpr.h"
#include "util/utility.h"

using namespace std;

namespace CVC4 {

const int CommandPrintSuccess::s_iosIndex = std::ios_base::xalloc();
const CommandSuccess* CommandSuccess::s_instance = new CommandSuccess();
const CommandInterrupted* CommandInterrupted::s_instance =
    new CommandInterrupted();

std::ostream& operator<<(std::ostream& out, const Command& c)
{
  c.toStream(out,
             Node::setdepth::getDepth(out),
             Node::printtypes::getPrintTypes(out),
             Node::dag::getDag(out),
             Node::setlanguage::getLanguage(out));
  return out;
}

ostream& operator<<(ostream& out, const Command* c)
{
  if (c == NULL)
  {
    out << "null";
  }
  else
  {
    out << *c;
  }
  return out;
}

std::ostream& operator<<(std::ostream& out, const CommandStatus& s)
{
  s.toStream(out, Node::setlanguage::getLanguage(out));
  return out;
}

ostream& operator<<(ostream& out, const CommandStatus* s)
{
  if (s == NULL)
  {
    out << "null";
  }
  else
  {
    out << *s;
  }
  return out;
}

/* output stream insertion operator for benchmark statuses */
std::ostream& operator<<(std::ostream& out, BenchmarkStatus status)
{
  switch (status)
  {
    case SMT_SATISFIABLE: return out << "sat";

    case SMT_UNSATISFIABLE: return out << "unsat";

    case SMT_UNKNOWN: return out << "unknown";

    default: return out << "BenchmarkStatus::[UNKNOWNSTATUS!]";
  }
}

/* -------------------------------------------------------------------------- */
/* class CommandPrintSuccess                                                  */
/* -------------------------------------------------------------------------- */

void CommandPrintSuccess::applyPrintSuccess(std::ostream& out)
{
  out.iword(s_iosIndex) = d_printSuccess;
}

bool CommandPrintSuccess::getPrintSuccess(std::ostream& out)
{
  return out.iword(s_iosIndex);
}

void CommandPrintSuccess::setPrintSuccess(std::ostream& out, bool printSuccess)
{
  out.iword(s_iosIndex) = printSuccess;
}

std::ostream& operator<<(std::ostream& out, CommandPrintSuccess cps)
{
  cps.applyPrintSuccess(out);
  return out;
}

/* -------------------------------------------------------------------------- */
/* class Command                                                              */
/* -------------------------------------------------------------------------- */

Command::Command() : d_commandStatus(nullptr), d_muted(false) {}

Command::Command(const api::Solver* solver)
    : d_commandStatus(nullptr), d_muted(false)
{
}

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

void Command::invoke(api::Solver* solver, std::ostream& out)
{
  invoke(solver);
  if (!(isMuted() && ok()))
  {
    printResult(
        out,
        std::stoul(solver->getOption("command-verbosity:" + getCommandName())));
  }
}

std::string Command::toString() const
{
  std::stringstream ss;
  toStream(ss);
  return ss.str();
}

void CommandStatus::toStream(std::ostream& out, OutputLanguage language) const
{
  Printer::getPrinter(language)->toStream(out, this);
}

void Command::printResult(std::ostream& out, uint32_t verbosity) const
{
  if (d_commandStatus != NULL)
  {
    if ((!ok() && verbosity >= 1) || verbosity >= 2)
    {
      out << *d_commandStatus;
    }
  }
}

/* -------------------------------------------------------------------------- */
/* class EmptyCommand                                                         */
/* -------------------------------------------------------------------------- */

EmptyCommand::EmptyCommand(std::string name) : d_name(name) {}
std::string EmptyCommand::getName() const { return d_name; }
void EmptyCommand::invoke(api::Solver* solver)
{
  /* empty commands have no implementation */
  d_commandStatus = CommandSuccess::instance();
}

Command* EmptyCommand::clone() const { return new EmptyCommand(d_name); }
std::string EmptyCommand::getCommandName() const { return "empty"; }

void EmptyCommand::toStream(std::ostream& out,
                            int toDepth,
                            bool types,
                            size_t dag,
                            OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdEmpty(out, d_name);
}

/* -------------------------------------------------------------------------- */
/* class EchoCommand                                                          */
/* -------------------------------------------------------------------------- */

EchoCommand::EchoCommand(std::string output) : d_output(output) {}
std::string EchoCommand::getOutput() const { return d_output; }
void EchoCommand::invoke(api::Solver* solver)
{
  /* we don't have an output stream here, nothing to do */
  d_commandStatus = CommandSuccess::instance();
}

void EchoCommand::invoke(api::Solver* solver, std::ostream& out)
{
  out << d_output << std::endl;
  Trace("dtview::command") << "* ~COMMAND: echo |" << d_output << "|~"
                           << std::endl;
  d_commandStatus = CommandSuccess::instance();
  printResult(
      out,
      std::stoul(solver->getOption("command-verbosity:" + getCommandName())));
}

Command* EchoCommand::clone() const { return new EchoCommand(d_output); }
std::string EchoCommand::getCommandName() const { return "echo"; }

void EchoCommand::toStream(std::ostream& out,
                           int toDepth,
                           bool types,
                           size_t dag,
                           OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdEcho(out, d_output);
}

/* -------------------------------------------------------------------------- */
/* class AssertCommand                                                        */
/* -------------------------------------------------------------------------- */

AssertCommand::AssertCommand(const api::Term& t, bool inUnsatCore)
    : d_term(t), d_inUnsatCore(inUnsatCore)
{
}

api::Term AssertCommand::getTerm() const { return d_term; }
void AssertCommand::invoke(api::Solver* solver)
{
  try
  {
    solver->getSmtEngine()->assertFormula(d_term.getExpr(), d_inUnsatCore);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (UnsafeInterruptException& e)
  {
    d_commandStatus = new CommandInterrupted();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* AssertCommand::clone() const
{
  return new AssertCommand(d_term, d_inUnsatCore);
}

std::string AssertCommand::getCommandName() const { return "assert"; }

void AssertCommand::toStream(std::ostream& out,
                             int toDepth,
                             bool types,
                             size_t dag,
                             OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdAssert(out, d_term.getNode());
}

/* -------------------------------------------------------------------------- */
/* class PushCommand                                                          */
/* -------------------------------------------------------------------------- */

void PushCommand::invoke(api::Solver* solver)
{
  try
  {
    solver->push();
    d_commandStatus = CommandSuccess::instance();
  }
  catch (UnsafeInterruptException& e)
  {
    d_commandStatus = new CommandInterrupted();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* PushCommand::clone() const { return new PushCommand(); }
std::string PushCommand::getCommandName() const { return "push"; }

void PushCommand::toStream(std::ostream& out,
                           int toDepth,
                           bool types,
                           size_t dag,
                           OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdPush(out);
}

/* -------------------------------------------------------------------------- */
/* class PopCommand                                                           */
/* -------------------------------------------------------------------------- */

void PopCommand::invoke(api::Solver* solver)
{
  try
  {
    solver->pop();
    d_commandStatus = CommandSuccess::instance();
  }
  catch (UnsafeInterruptException& e)
  {
    d_commandStatus = new CommandInterrupted();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* PopCommand::clone() const { return new PopCommand(); }
std::string PopCommand::getCommandName() const { return "pop"; }

void PopCommand::toStream(std::ostream& out,
                          int toDepth,
                          bool types,
                          size_t dag,
                          OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdPop(out);
}

/* -------------------------------------------------------------------------- */
/* class CheckSatCommand                                                      */
/* -------------------------------------------------------------------------- */

CheckSatCommand::CheckSatCommand() : d_term() {}

CheckSatCommand::CheckSatCommand(const api::Term& term) : d_term(term) {}

api::Term CheckSatCommand::getTerm() const { return d_term; }
void CheckSatCommand::invoke(api::Solver* solver)
{
  Trace("dtview::command") << "* ~COMMAND: " << getCommandName() << "~"
                           << std::endl;
  try
  {
    d_result =
        d_term.isNull() ? solver->checkSat() : solver->checkSatAssuming(d_term);

    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

api::Result CheckSatCommand::getResult() const { return d_result; }
void CheckSatCommand::printResult(std::ostream& out, uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    Trace("dtview::command") << "* RESULT: " << d_result << std::endl;
    out << d_result << endl;
  }
}

Command* CheckSatCommand::clone() const
{
  CheckSatCommand* c = new CheckSatCommand(d_term);
  c->d_result = d_result;
  return c;
}

std::string CheckSatCommand::getCommandName() const { return "check-sat"; }

void CheckSatCommand::toStream(std::ostream& out,
                               int toDepth,
                               bool types,
                               size_t dag,
                               OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdCheckSat(out, d_term.getNode());
}

/* -------------------------------------------------------------------------- */
/* class CheckSatAssumingCommand                                              */
/* -------------------------------------------------------------------------- */

CheckSatAssumingCommand::CheckSatAssumingCommand(api::Term term)
    : d_terms({term})
{
}

CheckSatAssumingCommand::CheckSatAssumingCommand(
    const std::vector<api::Term>& terms)
    : d_terms(terms)
{
}

const std::vector<api::Term>& CheckSatAssumingCommand::getTerms() const
{
  return d_terms;
}

void CheckSatAssumingCommand::invoke(api::Solver* solver)
{
  Trace("dtview::command") << "* ~COMMAND: (check-sat-assuming ( " << d_terms
                           << " )~" << std::endl;
  try
  {
    d_result = solver->checkSatAssuming(d_terms);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

api::Result CheckSatAssumingCommand::getResult() const
{
  Trace("dtview::command") << "* ~RESULT: " << d_result << "~" << std::endl;
  return d_result;
}

void CheckSatAssumingCommand::printResult(std::ostream& out,
                                          uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    out << d_result << endl;
  }
}

Command* CheckSatAssumingCommand::clone() const
{
  CheckSatAssumingCommand* c = new CheckSatAssumingCommand(d_terms);
  c->d_result = d_result;
  return c;
}

std::string CheckSatAssumingCommand::getCommandName() const
{
  return "check-sat-assuming";
}

void CheckSatAssumingCommand::toStream(std::ostream& out,
                                       int toDepth,
                                       bool types,
                                       size_t dag,
                                       OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdCheckSatAssuming(
      out, api::termVectorToNodes(d_terms));
}

/* -------------------------------------------------------------------------- */
/* class QueryCommand                                                         */
/* -------------------------------------------------------------------------- */

QueryCommand::QueryCommand(const api::Term& t, bool inUnsatCore)
    : d_term(t), d_inUnsatCore(inUnsatCore)
{
}

api::Term QueryCommand::getTerm() const { return d_term; }
void QueryCommand::invoke(api::Solver* solver)
{
  try
  {
    d_result = solver->checkEntailed(d_term);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

api::Result QueryCommand::getResult() const { return d_result; }
void QueryCommand::printResult(std::ostream& out, uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    out << d_result << endl;
  }
}

Command* QueryCommand::clone() const
{
  QueryCommand* c = new QueryCommand(d_term, d_inUnsatCore);
  c->d_result = d_result;
  return c;
}

std::string QueryCommand::getCommandName() const { return "query"; }

void QueryCommand::toStream(std::ostream& out,
                            int toDepth,
                            bool types,
                            size_t dag,
                            OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdQuery(out, d_term.getNode());
}

/* -------------------------------------------------------------------------- */
/* class DeclareSygusVarCommand */
/* -------------------------------------------------------------------------- */

DeclareSygusVarCommand::DeclareSygusVarCommand(const std::string& id,
                                               api::Term var,
                                               api::Sort sort)
    : DeclarationDefinitionCommand(id), d_var(var), d_sort(sort)
{
}

api::Term DeclareSygusVarCommand::getVar() const { return d_var; }
api::Sort DeclareSygusVarCommand::getSort() const { return d_sort; }

void DeclareSygusVarCommand::invoke(api::Solver* solver)
{
  try
  {
    solver->getSmtEngine()->declareSygusVar(
        d_symbol, d_var.getNode(), TypeNode::fromType(d_sort.getType()));
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* DeclareSygusVarCommand::clone() const
{
  return new DeclareSygusVarCommand(d_symbol, d_var, d_sort);
}

std::string DeclareSygusVarCommand::getCommandName() const
{
  return "declare-var";
}

void DeclareSygusVarCommand::toStream(std::ostream& out,
                                      int toDepth,
                                      bool types,
                                      size_t dag,
                                      OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdDeclareVar(
      out, d_var.getNode(), TypeNode::fromType(d_sort.getType()));
}

/* -------------------------------------------------------------------------- */
/* class SynthFunCommand                                                      */
/* -------------------------------------------------------------------------- */

SynthFunCommand::SynthFunCommand(const std::string& id,
                                 api::Term fun,
                                 const std::vector<api::Term>& vars,
                                 api::Sort sort,
                                 bool isInv,
                                 api::Grammar* g)
    : DeclarationDefinitionCommand(id),
      d_fun(fun),
      d_vars(vars),
      d_sort(sort),
      d_isInv(isInv),
      d_grammar(g)
{
}

api::Term SynthFunCommand::getFunction() const { return d_fun; }

const std::vector<api::Term>& SynthFunCommand::getVars() const
{
  return d_vars;
}

api::Sort SynthFunCommand::getSort() const { return d_sort; }
bool SynthFunCommand::isInv() const { return d_isInv; }

const api::Grammar* SynthFunCommand::getGrammar() const { return d_grammar; }

void SynthFunCommand::invoke(api::Solver* solver)
{
  try
  {
    std::vector<Node> vns;
    for (const api::Term& t : d_vars)
    {
      vns.push_back(Node::fromExpr(t.getExpr()));
    }
    solver->getSmtEngine()->declareSynthFun(
        d_symbol,
        Node::fromExpr(d_fun.getExpr()),
        TypeNode::fromType(d_grammar == nullptr
                               ? d_sort.getType()
                               : d_grammar->resolve().getType()),
        d_isInv,
        vns);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* SynthFunCommand::clone() const
{
  return new SynthFunCommand(
      d_symbol, d_fun, d_vars, d_sort, d_isInv, d_grammar);
}

std::string SynthFunCommand::getCommandName() const
{
  return d_isInv ? "synth-inv" : "synth-fun";
}

void SynthFunCommand::toStream(std::ostream& out,
                               int toDepth,
                               bool types,
                               size_t dag,
                               OutputLanguage language) const
{
  std::vector<Node> nodeVars = termVectorToNodes(d_vars);
  Printer::getPrinter(language)->toStreamCmdSynthFun(
      out,
      d_symbol,
      nodeVars,
      TypeNode::fromType(d_sort.getType()),
      d_isInv,
      TypeNode::fromType(d_grammar->resolve().getType()));
}

/* -------------------------------------------------------------------------- */
/* class SygusConstraintCommand */
/* -------------------------------------------------------------------------- */

SygusConstraintCommand::SygusConstraintCommand(const api::Term& t) : d_term(t)
{
}

void SygusConstraintCommand::invoke(api::Solver* solver)
{
  try
  {
    solver->addSygusConstraint(d_term);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

api::Term SygusConstraintCommand::getTerm() const { return d_term; }

Command* SygusConstraintCommand::clone() const
{
  return new SygusConstraintCommand(d_term);
}

std::string SygusConstraintCommand::getCommandName() const
{
  return "constraint";
}

void SygusConstraintCommand::toStream(std::ostream& out,
                                      int toDepth,
                                      bool types,
                                      size_t dag,
                                      OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdConstraint(out, d_term.getNode());
}

/* -------------------------------------------------------------------------- */
/* class SygusInvConstraintCommand */
/* -------------------------------------------------------------------------- */

SygusInvConstraintCommand::SygusInvConstraintCommand(
    const std::vector<api::Term>& predicates)
    : d_predicates(predicates)
{
}

SygusInvConstraintCommand::SygusInvConstraintCommand(const api::Term& inv,
                                                     const api::Term& pre,
                                                     const api::Term& trans,
                                                     const api::Term& post)
    : SygusInvConstraintCommand(std::vector<api::Term>{inv, pre, trans, post})
{
}

void SygusInvConstraintCommand::invoke(api::Solver* solver)
{
  try
  {
    solver->addSygusInvConstraint(
        d_predicates[0], d_predicates[1], d_predicates[2], d_predicates[3]);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

const std::vector<api::Term>& SygusInvConstraintCommand::getPredicates() const
{
  return d_predicates;
}

Command* SygusInvConstraintCommand::clone() const
{
  return new SygusInvConstraintCommand(d_predicates);
}

std::string SygusInvConstraintCommand::getCommandName() const
{
  return "inv-constraint";
}

void SygusInvConstraintCommand::toStream(std::ostream& out,
                                         int toDepth,
                                         bool types,
                                         size_t dag,
                                         OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdInvConstraint(
      out,
      d_predicates[0].getNode(),
      d_predicates[1].getNode(),
      d_predicates[2].getNode(),
      d_predicates[3].getNode());
}

/* -------------------------------------------------------------------------- */
/* class CheckSynthCommand                                                    */
/* -------------------------------------------------------------------------- */

void CheckSynthCommand::invoke(api::Solver* solver)
{
  try
  {
    d_result = solver->checkSynth();
    d_commandStatus = CommandSuccess::instance();
    d_solution.clear();
    // check whether we should print the status
    if (!d_result.isUnsat()
        || options::sygusOut() == options::SygusSolutionOutMode::STATUS_AND_DEF
        || options::sygusOut() == options::SygusSolutionOutMode::STATUS)
    {
      if (options::sygusOut() == options::SygusSolutionOutMode::STANDARD)
      {
        d_solution << "(fail)" << endl;
      }
      else
      {
        d_solution << d_result << endl;
      }
    }
    // check whether we should print the solution
    if (d_result.isUnsat()
        && options::sygusOut() != options::SygusSolutionOutMode::STATUS)
    {
      // printing a synthesis solution is a non-constant
      // method, since it invokes a sophisticated algorithm
      // (Figure 5 of Reynolds et al. CAV 2015).
      // Hence, we must call here print solution here,
      // instead of during printResult.
      solver->printSynthSolution(d_solution);
    }
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

api::Result CheckSynthCommand::getResult() const { return d_result; }
void CheckSynthCommand::printResult(std::ostream& out, uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    out << d_solution.str();
  }
}

Command* CheckSynthCommand::clone() const { return new CheckSynthCommand(); }

std::string CheckSynthCommand::getCommandName() const { return "check-synth"; }

void CheckSynthCommand::toStream(std::ostream& out,
                                 int toDepth,
                                 bool types,
                                 size_t dag,
                                 OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdCheckSynth(out);
}

/* -------------------------------------------------------------------------- */
/* class ResetCommand                                                         */
/* -------------------------------------------------------------------------- */

void ResetCommand::invoke(api::Solver* solver)
{
  try
  {
    solver->getSmtEngine()->reset();
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* ResetCommand::clone() const { return new ResetCommand(); }
std::string ResetCommand::getCommandName() const { return "reset"; }

void ResetCommand::toStream(std::ostream& out,
                            int toDepth,
                            bool types,
                            size_t dag,
                            OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdReset(out);
}

/* -------------------------------------------------------------------------- */
/* class ResetAssertionsCommand                                               */
/* -------------------------------------------------------------------------- */

void ResetAssertionsCommand::invoke(api::Solver* solver)
{
  try
  {
    solver->resetAssertions();
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* ResetAssertionsCommand::clone() const
{
  return new ResetAssertionsCommand();
}

std::string ResetAssertionsCommand::getCommandName() const
{
  return "reset-assertions";
}

void ResetAssertionsCommand::toStream(std::ostream& out,
                                      int toDepth,
                                      bool types,
                                      size_t dag,
                                      OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdResetAssertions(out);
}

/* -------------------------------------------------------------------------- */
/* class QuitCommand                                                          */
/* -------------------------------------------------------------------------- */

void QuitCommand::invoke(api::Solver* solver)
{
  Dump("benchmark") << *this;
  d_commandStatus = CommandSuccess::instance();
}

Command* QuitCommand::clone() const { return new QuitCommand(); }
std::string QuitCommand::getCommandName() const { return "exit"; }

void QuitCommand::toStream(std::ostream& out,
                           int toDepth,
                           bool types,
                           size_t dag,
                           OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdQuit(out);
}

/* -------------------------------------------------------------------------- */
/* class CommentCommand                                                       */
/* -------------------------------------------------------------------------- */

CommentCommand::CommentCommand(std::string comment) : d_comment(comment) {}
std::string CommentCommand::getComment() const { return d_comment; }
void CommentCommand::invoke(api::Solver* solver)
{
  Dump("benchmark") << *this;
  d_commandStatus = CommandSuccess::instance();
}

Command* CommentCommand::clone() const { return new CommentCommand(d_comment); }
std::string CommentCommand::getCommandName() const { return "comment"; }

void CommentCommand::toStream(std::ostream& out,
                              int toDepth,
                              bool types,
                              size_t dag,
                              OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdComment(out, d_comment);
}

/* -------------------------------------------------------------------------- */
/* class CommandSequence                                                      */
/* -------------------------------------------------------------------------- */

CommandSequence::CommandSequence() : d_index(0) {}
CommandSequence::~CommandSequence()
{
  for (unsigned i = d_index; i < d_commandSequence.size(); ++i)
  {
    delete d_commandSequence[i];
  }
}

void CommandSequence::addCommand(Command* cmd)
{
  d_commandSequence.push_back(cmd);
}

void CommandSequence::clear() { d_commandSequence.clear(); }
void CommandSequence::invoke(api::Solver* solver)
{
  for (; d_index < d_commandSequence.size(); ++d_index)
  {
    d_commandSequence[d_index]->invoke(solver);
    if (!d_commandSequence[d_index]->ok())
    {
      // abort execution
      d_commandStatus = d_commandSequence[d_index]->getCommandStatus();
      return;
    }
    delete d_commandSequence[d_index];
  }

  AlwaysAssert(d_commandStatus == NULL);
  d_commandStatus = CommandSuccess::instance();
}

void CommandSequence::invoke(api::Solver* solver, std::ostream& out)
{
  for (; d_index < d_commandSequence.size(); ++d_index)
  {
    d_commandSequence[d_index]->invoke(solver, out);
    if (!d_commandSequence[d_index]->ok())
    {
      // abort execution
      d_commandStatus = d_commandSequence[d_index]->getCommandStatus();
      return;
    }
    delete d_commandSequence[d_index];
  }

  AlwaysAssert(d_commandStatus == NULL);
  d_commandStatus = CommandSuccess::instance();
}

Command* CommandSequence::clone() const
{
  CommandSequence* seq = new CommandSequence();
  for (const_iterator i = begin(); i != end(); ++i)
  {
    seq->addCommand((*i)->clone());
  }
  seq->d_index = d_index;
  return seq;
}

CommandSequence::const_iterator CommandSequence::begin() const
{
  return d_commandSequence.begin();
}

CommandSequence::const_iterator CommandSequence::end() const
{
  return d_commandSequence.end();
}

CommandSequence::iterator CommandSequence::begin()
{
  return d_commandSequence.begin();
}

CommandSequence::iterator CommandSequence::end()
{
  return d_commandSequence.end();
}

std::string CommandSequence::getCommandName() const { return "sequence"; }

void CommandSequence::toStream(std::ostream& out,
                               int toDepth,
                               bool types,
                               size_t dag,
                               OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdCommandSequence(out,
                                                            d_commandSequence);
}

/* -------------------------------------------------------------------------- */
/* class DeclarationSequence                                                  */
/* -------------------------------------------------------------------------- */

void DeclarationSequence::toStream(std::ostream& out,
                                   int toDepth,
                                   bool types,
                                   size_t dag,
                                   OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdDeclarationSequence(
      out, d_commandSequence);
}

/* -------------------------------------------------------------------------- */
/* class DeclarationDefinitionCommand                                         */
/* -------------------------------------------------------------------------- */

DeclarationDefinitionCommand::DeclarationDefinitionCommand(
    const std::string& id)
    : d_symbol(id)
{
}

std::string DeclarationDefinitionCommand::getSymbol() const { return d_symbol; }

/* -------------------------------------------------------------------------- */
/* class DeclareFunctionCommand                                               */
/* -------------------------------------------------------------------------- */

DeclareFunctionCommand::DeclareFunctionCommand(const std::string& id,
                                               api::Term func,
                                               api::Sort sort)
    : DeclarationDefinitionCommand(id),
      d_func(func),
      d_sort(sort),
      d_printInModel(true),
      d_printInModelSetByUser(false)
{
}

api::Term DeclareFunctionCommand::getFunction() const { return d_func; }
api::Sort DeclareFunctionCommand::getSort() const { return d_sort; }
bool DeclareFunctionCommand::getPrintInModel() const { return d_printInModel; }
bool DeclareFunctionCommand::getPrintInModelSetByUser() const
{
  return d_printInModelSetByUser;
}

void DeclareFunctionCommand::setPrintInModel(bool p)
{
  d_printInModel = p;
  d_printInModelSetByUser = true;
}

void DeclareFunctionCommand::invoke(api::Solver* solver)
{
  d_commandStatus = CommandSuccess::instance();
}

Command* DeclareFunctionCommand::clone() const
{
  DeclareFunctionCommand* dfc =
      new DeclareFunctionCommand(d_symbol, d_func, d_sort);
  dfc->d_printInModel = d_printInModel;
  dfc->d_printInModelSetByUser = d_printInModelSetByUser;
  return dfc;
}

std::string DeclareFunctionCommand::getCommandName() const
{
  return "declare-fun";
}

void DeclareFunctionCommand::toStream(std::ostream& out,
                                      int toDepth,
                                      bool types,
                                      size_t dag,
                                      OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdDeclareFunction(
      out, d_func.toString(), TypeNode::fromType(d_sort.getType()));
}

/* -------------------------------------------------------------------------- */
/* class DeclareSortCommand                                                   */
/* -------------------------------------------------------------------------- */

DeclareSortCommand::DeclareSortCommand(const std::string& id,
                                       size_t arity,
                                       api::Sort sort)
    : DeclarationDefinitionCommand(id), d_arity(arity), d_sort(sort)
{
}

size_t DeclareSortCommand::getArity() const { return d_arity; }
api::Sort DeclareSortCommand::getSort() const { return d_sort; }
void DeclareSortCommand::invoke(api::Solver* solver)
{
  d_commandStatus = CommandSuccess::instance();
}

Command* DeclareSortCommand::clone() const
{
  return new DeclareSortCommand(d_symbol, d_arity, d_sort);
}

std::string DeclareSortCommand::getCommandName() const
{
  return "declare-sort";
}

void DeclareSortCommand::toStream(std::ostream& out,
                                  int toDepth,
                                  bool types,
                                  size_t dag,
                                  OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdDeclareType(
      out, d_sort.toString(), d_arity, TypeNode::fromType(d_sort.getType()));
}

/* -------------------------------------------------------------------------- */
/* class DefineSortCommand                                                    */
/* -------------------------------------------------------------------------- */

DefineSortCommand::DefineSortCommand(const std::string& id, api::Sort sort)
    : DeclarationDefinitionCommand(id), d_params(), d_sort(sort)
{
}

DefineSortCommand::DefineSortCommand(const std::string& id,
                                     const std::vector<api::Sort>& params,
                                     api::Sort sort)
    : DeclarationDefinitionCommand(id), d_params(params), d_sort(sort)
{
}

const std::vector<api::Sort>& DefineSortCommand::getParameters() const
{
  return d_params;
}

api::Sort DefineSortCommand::getSort() const { return d_sort; }
void DefineSortCommand::invoke(api::Solver* solver)
{
  d_commandStatus = CommandSuccess::instance();
}

Command* DefineSortCommand::clone() const
{
  return new DefineSortCommand(d_symbol, d_params, d_sort);
}

std::string DefineSortCommand::getCommandName() const { return "define-sort"; }

void DefineSortCommand::toStream(std::ostream& out,
                                 int toDepth,
                                 bool types,
                                 size_t dag,
                                 OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdDefineType(
      out,
      d_symbol,
      api::sortVectorToTypeNodes(d_params),
      TypeNode::fromType(d_sort.getType()));
}

/* -------------------------------------------------------------------------- */
/* class DefineFunctionCommand                                                */
/* -------------------------------------------------------------------------- */

DefineFunctionCommand::DefineFunctionCommand(const std::string& id,
                                             api::Term func,
                                             api::Term formula,
                                             bool global)
    : DeclarationDefinitionCommand(id),
      d_func(func),
      d_formals(),
      d_formula(formula),
      d_global(global)
{
}

DefineFunctionCommand::DefineFunctionCommand(
    const std::string& id,
    api::Term func,
    const std::vector<api::Term>& formals,
    api::Term formula,
    bool global)
    : DeclarationDefinitionCommand(id),
      d_func(func),
      d_formals(formals),
      d_formula(formula),
      d_global(global)
{
}

api::Term DefineFunctionCommand::getFunction() const { return d_func; }
const std::vector<api::Term>& DefineFunctionCommand::getFormals() const
{
  return d_formals;
}

api::Term DefineFunctionCommand::getFormula() const { return d_formula; }
void DefineFunctionCommand::invoke(api::Solver* solver)
{
  try
  {
    if (!d_func.isNull())
    {
      solver->defineFun(d_func, d_formals, d_formula, d_global);
    }
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* DefineFunctionCommand::clone() const
{
  return new DefineFunctionCommand(
      d_symbol, d_func, d_formals, d_formula, d_global);
}

std::string DefineFunctionCommand::getCommandName() const
{
  return "define-fun";
}

void DefineFunctionCommand::toStream(std::ostream& out,
                                     int toDepth,
                                     bool types,
                                     size_t dag,
                                     OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdDefineFunction(
      out,
      d_func.toString(),
      api::termVectorToNodes(d_formals),
      d_func.getNode().getType().getRangeType(),
      d_formula.getNode());
}

/* -------------------------------------------------------------------------- */
/* class DefineNamedFunctionCommand                                           */
/* -------------------------------------------------------------------------- */

DefineNamedFunctionCommand::DefineNamedFunctionCommand(

    const std::string& id,
    api::Term func,
    const std::vector<api::Term>& formals,
    api::Term formula,
    bool global)
    : DefineFunctionCommand(id, func, formals, formula, global)
{
}

void DefineNamedFunctionCommand::invoke(api::Solver* solver)
{
  this->DefineFunctionCommand::invoke(solver);
  if (!d_func.isNull() && d_func.getSort().isBoolean())
  {
    solver->getSmtEngine()->addToAssignment(d_func.getExpr());
  }
  d_commandStatus = CommandSuccess::instance();
}

Command* DefineNamedFunctionCommand::clone() const
{
  return new DefineNamedFunctionCommand(
      d_symbol, d_func, d_formals, d_formula, d_global);
}

void DefineNamedFunctionCommand::toStream(std::ostream& out,
                                          int toDepth,
                                          bool types,
                                          size_t dag,
                                          OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdDefineNamedFunction(
      out,
      d_func.toString(),
      api::termVectorToNodes(d_formals),
      TypeNode::fromType(d_func.getSort().getFunctionCodomainSort().getType()),
      d_formula.getNode());
}

/* -------------------------------------------------------------------------- */
/* class DefineFunctionRecCommand                                             */
/* -------------------------------------------------------------------------- */

DefineFunctionRecCommand::DefineFunctionRecCommand(

    api::Term func,
    const std::vector<api::Term>& formals,
    api::Term formula,
    bool global)
    : d_global(global)
{
  d_funcs.push_back(func);
  d_formals.push_back(formals);
  d_formulas.push_back(formula);
}

DefineFunctionRecCommand::DefineFunctionRecCommand(

    const std::vector<api::Term>& funcs,
    const std::vector<std::vector<api::Term>>& formals,
    const std::vector<api::Term>& formulas,
    bool global)
    : d_funcs(funcs), d_formals(formals), d_formulas(formulas), d_global(global)
{
}

const std::vector<api::Term>& DefineFunctionRecCommand::getFunctions() const
{
  return d_funcs;
}

const std::vector<std::vector<api::Term>>&
DefineFunctionRecCommand::getFormals() const
{
  return d_formals;
}

const std::vector<api::Term>& DefineFunctionRecCommand::getFormulas() const
{
  return d_formulas;
}

void DefineFunctionRecCommand::invoke(api::Solver* solver)
{
  try
  {
    solver->defineFunsRec(d_funcs, d_formals, d_formulas, d_global);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* DefineFunctionRecCommand::clone() const
{
  return new DefineFunctionRecCommand(d_funcs, d_formals, d_formulas, d_global);
}

std::string DefineFunctionRecCommand::getCommandName() const
{
  return "define-fun-rec";
}

void DefineFunctionRecCommand::toStream(std::ostream& out,
                                        int toDepth,
                                        bool types,
                                        size_t dag,
                                        OutputLanguage language) const
{
  std::vector<std::vector<Node>> formals;
  formals.reserve(d_formals.size());
  for (const std::vector<api::Term>& formal : d_formals)
  {
    formals.push_back(api::termVectorToNodes(formal));
  }

  Printer::getPrinter(language)->toStreamCmdDefineFunctionRec(
      out,
      api::termVectorToNodes(d_funcs),
      formals,
      api::termVectorToNodes(d_formulas));
}

/* -------------------------------------------------------------------------- */
/* class SetUserAttribute                                                     */
/* -------------------------------------------------------------------------- */

SetUserAttributeCommand::SetUserAttributeCommand(
    const std::string& attr,
    api::Term term,
    const std::vector<api::Term>& termValues,
    const std::string& strValue)
    : d_attr(attr), d_term(term), d_termValues(termValues), d_strValue(strValue)
{
}

SetUserAttributeCommand::SetUserAttributeCommand(const std::string& attr,
                                                 api::Term term)
    : SetUserAttributeCommand(attr, term, {}, "")
{
}

SetUserAttributeCommand::SetUserAttributeCommand(
    const std::string& attr,
    api::Term term,
    const std::vector<api::Term>& values)
    : SetUserAttributeCommand(attr, term, values, "")
{
}

SetUserAttributeCommand::SetUserAttributeCommand(const std::string& attr,
                                                 api::Term term,
                                                 const std::string& value)
    : SetUserAttributeCommand(attr, term, {}, value)
{
}

void SetUserAttributeCommand::invoke(api::Solver* solver)
{
  try
  {
    if (!d_term.isNull())
    {
      solver->getSmtEngine()->setUserAttribute(
          d_attr,
          d_term.getExpr(),
          api::termVectorToExprs(d_termValues),
          d_strValue);
    }
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* SetUserAttributeCommand::clone() const
{
  return new SetUserAttributeCommand(d_attr, d_term, d_termValues, d_strValue);
}

std::string SetUserAttributeCommand::getCommandName() const
{
  return "set-user-attribute";
}

void SetUserAttributeCommand::toStream(std::ostream& out,
                                       int toDepth,
                                       bool types,
                                       size_t dag,
                                       OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdSetUserAttribute(
      out, d_attr, d_term.getNode());
}

/* -------------------------------------------------------------------------- */
/* class SimplifyCommand                                                      */
/* -------------------------------------------------------------------------- */

SimplifyCommand::SimplifyCommand(api::Term term) : d_term(term) {}
api::Term SimplifyCommand::getTerm() const { return d_term; }
void SimplifyCommand::invoke(api::Solver* solver)
{
  try
  {
    d_result = solver->simplify(d_term);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (UnsafeInterruptException& e)
  {
    d_commandStatus = new CommandInterrupted();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

api::Term SimplifyCommand::getResult() const { return d_result; }
void SimplifyCommand::printResult(std::ostream& out, uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    out << d_result << endl;
  }
}

Command* SimplifyCommand::clone() const
{
  SimplifyCommand* c = new SimplifyCommand(d_term);
  c->d_result = d_result;
  return c;
}

std::string SimplifyCommand::getCommandName() const { return "simplify"; }

void SimplifyCommand::toStream(std::ostream& out,
                               int toDepth,
                               bool types,
                               size_t dag,
                               OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdSimplify(out, d_term.getNode());
}

/* -------------------------------------------------------------------------- */
/* class ExpandDefinitionsCommand                                             */
/* -------------------------------------------------------------------------- */

ExpandDefinitionsCommand::ExpandDefinitionsCommand(api::Term term)
    : d_term(term)
{
}
api::Term ExpandDefinitionsCommand::getTerm() const { return d_term; }
void ExpandDefinitionsCommand::invoke(api::Solver* solver)
{
  Node t = d_term.getNode();
  d_result = api::Term(solver, solver->getSmtEngine()->expandDefinitions(t));
  d_commandStatus = CommandSuccess::instance();
}

api::Term ExpandDefinitionsCommand::getResult() const { return d_result; }
void ExpandDefinitionsCommand::printResult(std::ostream& out,
                                           uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    out << d_result << endl;
  }
}

Command* ExpandDefinitionsCommand::clone() const
{
  ExpandDefinitionsCommand* c = new ExpandDefinitionsCommand(d_term);
  c->d_result = d_result;
  return c;
}

std::string ExpandDefinitionsCommand::getCommandName() const
{
  return "expand-definitions";
}

void ExpandDefinitionsCommand::toStream(std::ostream& out,
                                        int toDepth,
                                        bool types,
                                        size_t dag,
                                        OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdExpandDefinitions(out,
                                                              d_term.getNode());
}

/* -------------------------------------------------------------------------- */
/* class GetValueCommand                                                      */
/* -------------------------------------------------------------------------- */

GetValueCommand::GetValueCommand(api::Term term) : d_terms()
{
  d_terms.push_back(term);
}

GetValueCommand::GetValueCommand(const std::vector<api::Term>& terms)
    : d_terms(terms)
{
  PrettyCheckArgument(
      terms.size() >= 1, terms, "cannot get-value of an empty set of terms");
}

const std::vector<api::Term>& GetValueCommand::getTerms() const
{
  return d_terms;
}
void GetValueCommand::invoke(api::Solver* solver)
{
  try
  {
    NodeManager* nm = solver->getNodeManager();
    smt::SmtScope scope(solver->getSmtEngine());
    std::vector<Node> result;
    for (const Expr& e :
         solver->getSmtEngine()->getValues(api::termVectorToExprs(d_terms)))
    {
      result.push_back(Node::fromExpr(e));
    }
    Assert(result.size() == d_terms.size());
    for (int i = 0, size = d_terms.size(); i < size; i++)
    {
      api::Term t = d_terms[i];
      Node tNode = t.getNode();
      Node request = options::expandDefinitions()
                         ? solver->getSmtEngine()->expandDefinitions(tNode)
                         : tNode;
      Node value = result[i];
      if (value.getType().isInteger() && request.getType() == nm->realType())
      {
        // Need to wrap in division-by-one so that output printers know this
        // is an integer-looking constant that really should be output as
        // a rational.  Necessary for SMT-LIB standards compliance.
        value = nm->mkNode(kind::DIVISION, value, nm->mkConst(Rational(1)));
      }
      result[i] = nm->mkNode(kind::SEXPR, request, value);
    }
    d_result = api::Term(solver, nm->mkNode(kind::SEXPR, result));
    d_commandStatus = CommandSuccess::instance();
  }
  catch (RecoverableModalException& e)
  {
    d_commandStatus = new CommandRecoverableFailure(e.what());
  }
  catch (UnsafeInterruptException& e)
  {
    d_commandStatus = new CommandInterrupted();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

api::Term GetValueCommand::getResult() const { return d_result; }
void GetValueCommand::printResult(std::ostream& out, uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    expr::ExprDag::Scope scope(out, false);
    out << d_result << endl;
  }
}

Command* GetValueCommand::clone() const
{
  GetValueCommand* c = new GetValueCommand(d_terms);
  c->d_result = d_result;
  return c;
}

std::string GetValueCommand::getCommandName() const { return "get-value"; }

void GetValueCommand::toStream(std::ostream& out,
                               int toDepth,
                               bool types,
                               size_t dag,
                               OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdGetValue(
      out, api::termVectorToNodes(d_terms));
}

/* -------------------------------------------------------------------------- */
/* class GetAssignmentCommand                                                 */
/* -------------------------------------------------------------------------- */

GetAssignmentCommand::GetAssignmentCommand() {}
void GetAssignmentCommand::invoke(api::Solver* solver)
{
  try
  {
    std::vector<std::pair<Expr, Expr>> assignments =
        solver->getSmtEngine()->getAssignment();
    vector<SExpr> sexprs;
    for (const auto& p : assignments)
    {
      vector<SExpr> v;
      v.emplace_back(SExpr::Keyword(p.first.toString()));
      v.emplace_back(SExpr::Keyword(p.second.toString()));
      sexprs.emplace_back(v);
    }
    d_result = SExpr(sexprs);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (RecoverableModalException& e)
  {
    d_commandStatus = new CommandRecoverableFailure(e.what());
  }
  catch (UnsafeInterruptException& e)
  {
    d_commandStatus = new CommandInterrupted();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

SExpr GetAssignmentCommand::getResult() const { return d_result; }
void GetAssignmentCommand::printResult(std::ostream& out,
                                       uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    out << d_result << endl;
  }
}

Command* GetAssignmentCommand::clone() const
{
  GetAssignmentCommand* c = new GetAssignmentCommand();
  c->d_result = d_result;
  return c;
}

std::string GetAssignmentCommand::getCommandName() const
{
  return "get-assignment";
}

void GetAssignmentCommand::toStream(std::ostream& out,
                                    int toDepth,
                                    bool types,
                                    size_t dag,
                                    OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdGetAssignment(out);
}

/* -------------------------------------------------------------------------- */
/* class GetModelCommand                                                      */
/* -------------------------------------------------------------------------- */

GetModelCommand::GetModelCommand() : d_result(nullptr), d_smtEngine(nullptr) {}
void GetModelCommand::invoke(api::Solver* solver)
{
  try
  {
    d_result = solver->getSmtEngine()->getModel();
    d_smtEngine = solver->getSmtEngine();
    d_commandStatus = CommandSuccess::instance();
  }
  catch (RecoverableModalException& e)
  {
    d_commandStatus = new CommandRecoverableFailure(e.what());
  }
  catch (UnsafeInterruptException& e)
  {
    d_commandStatus = new CommandInterrupted();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

/* Model is private to the library -- for now
Model* GetModelCommand::getResult() const  {
  return d_result;
}
*/

void GetModelCommand::printResult(std::ostream& out, uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    out << *d_result;
  }
}

Command* GetModelCommand::clone() const
{
  GetModelCommand* c = new GetModelCommand();
  c->d_result = d_result;
  c->d_smtEngine = d_smtEngine;
  return c;
}

std::string GetModelCommand::getCommandName() const { return "get-model"; }

void GetModelCommand::toStream(std::ostream& out,
                               int toDepth,
                               bool types,
                               size_t dag,
                               OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdGetModel(out);
}

/* -------------------------------------------------------------------------- */
/* class BlockModelCommand */
/* -------------------------------------------------------------------------- */

BlockModelCommand::BlockModelCommand() {}
void BlockModelCommand::invoke(api::Solver* solver)
{
  try
  {
    solver->getSmtEngine()->blockModel();
    d_commandStatus = CommandSuccess::instance();
  }
  catch (RecoverableModalException& e)
  {
    d_commandStatus = new CommandRecoverableFailure(e.what());
  }
  catch (UnsafeInterruptException& e)
  {
    d_commandStatus = new CommandInterrupted();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* BlockModelCommand::clone() const
{
  BlockModelCommand* c = new BlockModelCommand();
  return c;
}

std::string BlockModelCommand::getCommandName() const { return "block-model"; }

void BlockModelCommand::toStream(std::ostream& out,
                                 int toDepth,
                                 bool types,
                                 size_t dag,
                                 OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdBlockModel(out);
}

/* -------------------------------------------------------------------------- */
/* class BlockModelValuesCommand */
/* -------------------------------------------------------------------------- */

BlockModelValuesCommand::BlockModelValuesCommand(
    const std::vector<api::Term>& terms)
    : d_terms(terms)
{
  PrettyCheckArgument(terms.size() >= 1,
                      terms,
                      "cannot block-model-values of an empty set of terms");
}

const std::vector<api::Term>& BlockModelValuesCommand::getTerms() const
{
  return d_terms;
}
void BlockModelValuesCommand::invoke(api::Solver* solver)
{
  try
  {
    solver->getSmtEngine()->blockModelValues(api::termVectorToExprs(d_terms));
    d_commandStatus = CommandSuccess::instance();
  }
  catch (RecoverableModalException& e)
  {
    d_commandStatus = new CommandRecoverableFailure(e.what());
  }
  catch (UnsafeInterruptException& e)
  {
    d_commandStatus = new CommandInterrupted();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* BlockModelValuesCommand::clone() const
{
  BlockModelValuesCommand* c = new BlockModelValuesCommand(d_terms);
  return c;
}

std::string BlockModelValuesCommand::getCommandName() const
{
  return "block-model-values";
}

void BlockModelValuesCommand::toStream(std::ostream& out,
                                       int toDepth,
                                       bool types,
                                       size_t dag,
                                       OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdBlockModelValues(
      out, api::termVectorToNodes(d_terms));
}

/* -------------------------------------------------------------------------- */
/* class GetProofCommand                                                      */
/* -------------------------------------------------------------------------- */

GetProofCommand::GetProofCommand() {}
void GetProofCommand::invoke(api::Solver* solver)
{
  Unimplemented() << "Unimplemented get-proof\n";
}

Command* GetProofCommand::clone() const
{
  GetProofCommand* c = new GetProofCommand();
  return c;
}

std::string GetProofCommand::getCommandName() const { return "get-proof"; }

void GetProofCommand::toStream(std::ostream& out,
                               int toDepth,
                               bool types,
                               size_t dag,
                               OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdGetProof(out);
}

/* -------------------------------------------------------------------------- */
/* class GetInstantiationsCommand                                             */
/* -------------------------------------------------------------------------- */

GetInstantiationsCommand::GetInstantiationsCommand() : d_smtEngine(nullptr) {}
void GetInstantiationsCommand::invoke(api::Solver* solver)
{
  try
  {
    d_smtEngine = solver->getSmtEngine();
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

void GetInstantiationsCommand::printResult(std::ostream& out,
                                           uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    d_smtEngine->printInstantiations(out);
  }
}

Command* GetInstantiationsCommand::clone() const
{
  GetInstantiationsCommand* c = new GetInstantiationsCommand();
  // c->d_result = d_result;
  c->d_smtEngine = d_smtEngine;
  return c;
}

std::string GetInstantiationsCommand::getCommandName() const
{
  return "get-instantiations";
}

void GetInstantiationsCommand::toStream(std::ostream& out,
                                        int toDepth,
                                        bool types,
                                        size_t dag,
                                        OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdGetInstantiations(out);
}

/* -------------------------------------------------------------------------- */
/* class GetSynthSolutionCommand                                              */
/* -------------------------------------------------------------------------- */

GetSynthSolutionCommand::GetSynthSolutionCommand() : d_smtEngine(nullptr) {}
void GetSynthSolutionCommand::invoke(api::Solver* solver)
{
  try
  {
    d_smtEngine = solver->getSmtEngine();
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

void GetSynthSolutionCommand::printResult(std::ostream& out,
                                          uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    d_smtEngine->printSynthSolution(out);
  }
}

Command* GetSynthSolutionCommand::clone() const
{
  GetSynthSolutionCommand* c = new GetSynthSolutionCommand();
  c->d_smtEngine = d_smtEngine;
  return c;
}

std::string GetSynthSolutionCommand::getCommandName() const
{
  return "get-synth-solution";
}

void GetSynthSolutionCommand::toStream(std::ostream& out,
                                       int toDepth,
                                       bool types,
                                       size_t dag,
                                       OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdGetSynthSolution(out);
}

/* -------------------------------------------------------------------------- */
/* class GetInterpolCommand                                                   */
/* -------------------------------------------------------------------------- */

GetInterpolCommand::GetInterpolCommand(const std::string& name, api::Term conj)
    : d_name(name), d_conj(conj), d_resultStatus(false)
{
}
GetInterpolCommand::GetInterpolCommand(const std::string& name,
                                       api::Term conj,
                                       api::Grammar* g)
    : d_name(name), d_conj(conj), d_sygus_grammar(g), d_resultStatus(false)
{
}

api::Term GetInterpolCommand::getConjecture() const { return d_conj; }

const api::Grammar* GetInterpolCommand::getGrammar() const
{
  return d_sygus_grammar;
}

api::Term GetInterpolCommand::getResult() const { return d_result; }

void GetInterpolCommand::invoke(api::Solver* solver)
{
  try
  {
    if (d_sygus_grammar == nullptr)
    {
      d_resultStatus = solver->getInterpolant(d_conj, d_result);
    }
    else
    {
      d_resultStatus =
          solver->getInterpolant(d_conj, *d_sygus_grammar, d_result);
    }
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

void GetInterpolCommand::printResult(std::ostream& out,
                                     uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    expr::ExprDag::Scope scope(out, false);
    if (d_resultStatus)
    {
      out << "(define-fun " << d_name << " () Bool " << d_result << ")"
          << std::endl;
    }
    else
    {
      out << "none" << std::endl;
    }
  }
}

Command* GetInterpolCommand::clone() const
{
  GetInterpolCommand* c =
      new GetInterpolCommand(d_name, d_conj, d_sygus_grammar);
  c->d_result = d_result;
  c->d_resultStatus = d_resultStatus;
  return c;
}

std::string GetInterpolCommand::getCommandName() const
{
  return "get-interpol";
}

void GetInterpolCommand::toStream(std::ostream& out,
                                  int toDepth,
                                  bool types,
                                  size_t dag,
                                  OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdGetInterpol(
      out,
      d_name,
      d_conj.getNode(),
      TypeNode::fromType(d_sygus_grammar->resolve().getType()));
}

/* -------------------------------------------------------------------------- */
/* class GetAbductCommand                                                     */
/* -------------------------------------------------------------------------- */

GetAbductCommand::GetAbductCommand(const std::string& name, api::Term conj)
    : d_name(name), d_conj(conj), d_resultStatus(false)
{
}
GetAbductCommand::GetAbductCommand(const std::string& name,
                                   api::Term conj,
                                   api::Grammar* g)
    : d_name(name), d_conj(conj), d_sygus_grammar(g), d_resultStatus(false)
{
}

api::Term GetAbductCommand::getConjecture() const { return d_conj; }

const api::Grammar* GetAbductCommand::getGrammar() const
{
  return d_sygus_grammar;
}

std::string GetAbductCommand::getAbductName() const { return d_name; }
api::Term GetAbductCommand::getResult() const { return d_result; }

void GetAbductCommand::invoke(api::Solver* solver)
{
  try
  {
    if (d_sygus_grammar == nullptr)
    {
      d_resultStatus = solver->getAbduct(d_conj, d_result);
    }
    else
    {
      d_resultStatus = solver->getAbduct(d_conj, *d_sygus_grammar, d_result);
    }
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

void GetAbductCommand::printResult(std::ostream& out, uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    expr::ExprDag::Scope scope(out, false);
    if (d_resultStatus)
    {
      out << "(define-fun " << d_name << " () Bool " << d_result << ")"
          << std::endl;
    }
    else
    {
      out << "none" << std::endl;
    }
  }
}

Command* GetAbductCommand::clone() const
{
  GetAbductCommand* c = new GetAbductCommand(d_name, d_conj, d_sygus_grammar);
  c->d_result = d_result;
  c->d_resultStatus = d_resultStatus;
  return c;
}

std::string GetAbductCommand::getCommandName() const { return "get-abduct"; }

void GetAbductCommand::toStream(std::ostream& out,
                                int toDepth,
                                bool types,
                                size_t dag,
                                OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdGetAbduct(
      out,
      d_name,
      d_conj.getNode(),
      TypeNode::fromType(d_sygus_grammar->resolve().getType()));
}

/* -------------------------------------------------------------------------- */
/* class GetQuantifierEliminationCommand                                      */
/* -------------------------------------------------------------------------- */

GetQuantifierEliminationCommand::GetQuantifierEliminationCommand()
    : d_term(), d_doFull(true)
{
}
GetQuantifierEliminationCommand::GetQuantifierEliminationCommand(
    const api::Term& term, bool doFull)
    : d_term(term), d_doFull(doFull)
{
}

api::Term GetQuantifierEliminationCommand::getTerm() const { return d_term; }
bool GetQuantifierEliminationCommand::getDoFull() const { return d_doFull; }
void GetQuantifierEliminationCommand::invoke(api::Solver* solver)
{
  try
  {
    d_result = api::Term(solver,
                         solver->getSmtEngine()->getQuantifierElimination(
                             d_term.getNode(), d_doFull));
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

api::Term GetQuantifierEliminationCommand::getResult() const
{
  return d_result;
}
void GetQuantifierEliminationCommand::printResult(std::ostream& out,
                                                  uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    out << d_result << endl;
  }
}

Command* GetQuantifierEliminationCommand::clone() const
{
  GetQuantifierEliminationCommand* c =
      new GetQuantifierEliminationCommand(d_term, d_doFull);
  c->d_result = d_result;
  return c;
}

std::string GetQuantifierEliminationCommand::getCommandName() const
{
  return d_doFull ? "get-qe" : "get-qe-disjunct";
}

void GetQuantifierEliminationCommand::toStream(std::ostream& out,
                                               int toDepth,
                                               bool types,
                                               size_t dag,
                                               OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdGetQuantifierElimination(
      out, d_term.getNode());
}

/* -------------------------------------------------------------------------- */
/* class GetUnsatAssumptionsCommand                                           */
/* -------------------------------------------------------------------------- */

GetUnsatAssumptionsCommand::GetUnsatAssumptionsCommand() {}

void GetUnsatAssumptionsCommand::invoke(api::Solver* solver)
{
  try
  {
    d_result = solver->getUnsatAssumptions();
    d_commandStatus = CommandSuccess::instance();
  }
  catch (RecoverableModalException& e)
  {
    d_commandStatus = new CommandRecoverableFailure(e.what());
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

std::vector<api::Term> GetUnsatAssumptionsCommand::getResult() const
{
  return d_result;
}

void GetUnsatAssumptionsCommand::printResult(std::ostream& out,
                                             uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    container_to_stream(out, d_result, "(", ")\n", " ");
  }
}

Command* GetUnsatAssumptionsCommand::clone() const
{
  GetUnsatAssumptionsCommand* c = new GetUnsatAssumptionsCommand;
  c->d_result = d_result;
  return c;
}

std::string GetUnsatAssumptionsCommand::getCommandName() const
{
  return "get-unsat-assumptions";
}

void GetUnsatAssumptionsCommand::toStream(std::ostream& out,
                                          int toDepth,
                                          bool types,
                                          size_t dag,
                                          OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdGetUnsatAssumptions(out);
}

/* -------------------------------------------------------------------------- */
/* class GetUnsatCoreCommand                                                  */
/* -------------------------------------------------------------------------- */

GetUnsatCoreCommand::GetUnsatCoreCommand() {}
void GetUnsatCoreCommand::invoke(api::Solver* solver)
{
  try
  {
    d_result = solver->getSmtEngine()->getUnsatCore();
    d_commandStatus = CommandSuccess::instance();
  }
  catch (RecoverableModalException& e)
  {
    d_commandStatus = new CommandRecoverableFailure(e.what());
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

void GetUnsatCoreCommand::printResult(std::ostream& out,
                                      uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    d_result.toStream(out);
  }
}

const UnsatCore& GetUnsatCoreCommand::getUnsatCore() const
{
  // of course, this will be empty if the command hasn't been invoked yet
  return d_result;
}

Command* GetUnsatCoreCommand::clone() const
{
  GetUnsatCoreCommand* c = new GetUnsatCoreCommand;
  c->d_result = d_result;
  return c;
}

std::string GetUnsatCoreCommand::getCommandName() const
{
  return "get-unsat-core";
}

void GetUnsatCoreCommand::toStream(std::ostream& out,
                                   int toDepth,
                                   bool types,
                                   size_t dag,
                                   OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdGetUnsatCore(out);
}

/* -------------------------------------------------------------------------- */
/* class GetAssertionsCommand                                                 */
/* -------------------------------------------------------------------------- */

GetAssertionsCommand::GetAssertionsCommand() {}
void GetAssertionsCommand::invoke(api::Solver* solver)
{
  try
  {
    stringstream ss;
    const vector<api::Term> v = solver->getAssertions();
    ss << "(\n";
    copy(v.begin(), v.end(), ostream_iterator<api::Term>(ss, "\n"));
    ss << ")\n";
    d_result = ss.str();
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

std::string GetAssertionsCommand::getResult() const { return d_result; }
void GetAssertionsCommand::printResult(std::ostream& out,
                                       uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    out << d_result;
  }
}

Command* GetAssertionsCommand::clone() const
{
  GetAssertionsCommand* c = new GetAssertionsCommand();
  c->d_result = d_result;
  return c;
}

std::string GetAssertionsCommand::getCommandName() const
{
  return "get-assertions";
}

void GetAssertionsCommand::toStream(std::ostream& out,
                                    int toDepth,
                                    bool types,
                                    size_t dag,
                                    OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdGetAssertions(out);
}

/* -------------------------------------------------------------------------- */
/* class SetBenchmarkStatusCommand                                            */
/* -------------------------------------------------------------------------- */

SetBenchmarkStatusCommand::SetBenchmarkStatusCommand(BenchmarkStatus status)
    : d_status(status)
{
}

BenchmarkStatus SetBenchmarkStatusCommand::getStatus() const
{
  return d_status;
}

void SetBenchmarkStatusCommand::invoke(api::Solver* solver)
{
  try
  {
    stringstream ss;
    ss << d_status;
    solver->setInfo("status", ss.str());
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* SetBenchmarkStatusCommand::clone() const
{
  return new SetBenchmarkStatusCommand(d_status);
}

std::string SetBenchmarkStatusCommand::getCommandName() const
{
  return "set-info";
}

void SetBenchmarkStatusCommand::toStream(std::ostream& out,
                                         int toDepth,
                                         bool types,
                                         size_t dag,
                                         OutputLanguage language) const
{
  Result::Sat status = Result::SAT_UNKNOWN;
  switch (d_status)
  {
    case BenchmarkStatus::SMT_SATISFIABLE: status = Result::SAT; break;
    case BenchmarkStatus::SMT_UNSATISFIABLE: status = Result::UNSAT; break;
    case BenchmarkStatus::SMT_UNKNOWN: status = Result::SAT_UNKNOWN; break;
  }

  Printer::getPrinter(language)->toStreamCmdSetBenchmarkStatus(out, status);
}

/* -------------------------------------------------------------------------- */
/* class SetBenchmarkLogicCommand                                             */
/* -------------------------------------------------------------------------- */

SetBenchmarkLogicCommand::SetBenchmarkLogicCommand(std::string logic)
    : d_logic(logic)
{
}

std::string SetBenchmarkLogicCommand::getLogic() const { return d_logic; }
void SetBenchmarkLogicCommand::invoke(api::Solver* solver)
{
  try
  {
    solver->setLogic(d_logic);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* SetBenchmarkLogicCommand::clone() const
{
  return new SetBenchmarkLogicCommand(d_logic);
}

std::string SetBenchmarkLogicCommand::getCommandName() const
{
  return "set-logic";
}

void SetBenchmarkLogicCommand::toStream(std::ostream& out,
                                        int toDepth,
                                        bool types,
                                        size_t dag,
                                        OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdSetBenchmarkLogic(out, d_logic);
}

/* -------------------------------------------------------------------------- */
/* class SetInfoCommand                                                       */
/* -------------------------------------------------------------------------- */

SetInfoCommand::SetInfoCommand(std::string flag, const SExpr& sexpr)
    : d_flag(flag), d_sexpr(sexpr)
{
}

std::string SetInfoCommand::getFlag() const { return d_flag; }
SExpr SetInfoCommand::getSExpr() const { return d_sexpr; }
void SetInfoCommand::invoke(api::Solver* solver)
{
  try
  {
    solver->getSmtEngine()->setInfo(d_flag, d_sexpr);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (UnrecognizedOptionException&)
  {
    // As per SMT-LIB spec, silently accept unknown set-info keys
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* SetInfoCommand::clone() const
{
  return new SetInfoCommand(d_flag, d_sexpr);
}

std::string SetInfoCommand::getCommandName() const { return "set-info"; }

void SetInfoCommand::toStream(std::ostream& out,
                              int toDepth,
                              bool types,
                              size_t dag,
                              OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdSetInfo(out, d_flag, d_sexpr);
}

/* -------------------------------------------------------------------------- */
/* class GetInfoCommand                                                       */
/* -------------------------------------------------------------------------- */

GetInfoCommand::GetInfoCommand(std::string flag) : d_flag(flag) {}
std::string GetInfoCommand::getFlag() const { return d_flag; }
void GetInfoCommand::invoke(api::Solver* solver)
{
  try
  {
    vector<SExpr> v;
    v.push_back(SExpr(SExpr::Keyword(string(":") + d_flag)));
    v.emplace_back(solver->getSmtEngine()->getInfo(d_flag));
    stringstream ss;
    if (d_flag == "all-options" || d_flag == "all-statistics")
    {
      ss << PrettySExprs(true);
    }
    ss << SExpr(v);
    d_result = ss.str();
    d_commandStatus = CommandSuccess::instance();
  }
  catch (UnrecognizedOptionException&)
  {
    d_commandStatus = new CommandUnsupported();
  }
  catch (RecoverableModalException& e)
  {
    d_commandStatus = new CommandRecoverableFailure(e.what());
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

std::string GetInfoCommand::getResult() const { return d_result; }
void GetInfoCommand::printResult(std::ostream& out, uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else if (d_result != "")
  {
    out << d_result << endl;
  }
}

Command* GetInfoCommand::clone() const
{
  GetInfoCommand* c = new GetInfoCommand(d_flag);
  c->d_result = d_result;
  return c;
}

std::string GetInfoCommand::getCommandName() const { return "get-info"; }

void GetInfoCommand::toStream(std::ostream& out,
                              int toDepth,
                              bool types,
                              size_t dag,
                              OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdGetInfo(out, d_flag);
}

/* -------------------------------------------------------------------------- */
/* class SetOptionCommand                                                     */
/* -------------------------------------------------------------------------- */

SetOptionCommand::SetOptionCommand(std::string flag, const SExpr& sexpr)
    : d_flag(flag), d_sexpr(sexpr)
{
}

std::string SetOptionCommand::getFlag() const { return d_flag; }
SExpr SetOptionCommand::getSExpr() const { return d_sexpr; }
void SetOptionCommand::invoke(api::Solver* solver)
{
  try
  {
    solver->getSmtEngine()->setOption(d_flag, d_sexpr);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (UnrecognizedOptionException&)
  {
    d_commandStatus = new CommandUnsupported();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* SetOptionCommand::clone() const
{
  return new SetOptionCommand(d_flag, d_sexpr);
}

std::string SetOptionCommand::getCommandName() const { return "set-option"; }

void SetOptionCommand::toStream(std::ostream& out,
                                int toDepth,
                                bool types,
                                size_t dag,
                                OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdSetOption(out, d_flag, d_sexpr);
}

/* -------------------------------------------------------------------------- */
/* class GetOptionCommand                                                     */
/* -------------------------------------------------------------------------- */

GetOptionCommand::GetOptionCommand(std::string flag) : d_flag(flag) {}
std::string GetOptionCommand::getFlag() const { return d_flag; }
void GetOptionCommand::invoke(api::Solver* solver)
{
  try
  {
    d_result = solver->getOption(d_flag);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (UnrecognizedOptionException&)
  {
    d_commandStatus = new CommandUnsupported();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

std::string GetOptionCommand::getResult() const { return d_result; }
void GetOptionCommand::printResult(std::ostream& out, uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else if (d_result != "")
  {
    out << d_result << endl;
  }
}

Command* GetOptionCommand::clone() const
{
  GetOptionCommand* c = new GetOptionCommand(d_flag);
  c->d_result = d_result;
  return c;
}

std::string GetOptionCommand::getCommandName() const { return "get-option"; }

void GetOptionCommand::toStream(std::ostream& out,
                                int toDepth,
                                bool types,
                                size_t dag,
                                OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdGetOption(out, d_flag);
}

/* -------------------------------------------------------------------------- */
/* class SetExpressionNameCommand                                             */
/* -------------------------------------------------------------------------- */

SetExpressionNameCommand::SetExpressionNameCommand(api::Term term,
                                                   std::string name)
    : d_term(term), d_name(name)
{
}

void SetExpressionNameCommand::invoke(api::Solver* solver)
{
  solver->getSmtEngine()->setExpressionName(d_term.getExpr(), d_name);
  d_commandStatus = CommandSuccess::instance();
}

Command* SetExpressionNameCommand::clone() const
{
  SetExpressionNameCommand* c = new SetExpressionNameCommand(d_term, d_name);
  return c;
}

std::string SetExpressionNameCommand::getCommandName() const
{
  return "set-expr-name";
}

void SetExpressionNameCommand::toStream(std::ostream& out,
                                        int toDepth,
                                        bool types,
                                        size_t dag,
                                        OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdSetExpressionName(
      out, d_term.getNode(), d_name);
}

/* -------------------------------------------------------------------------- */
/* class DatatypeDeclarationCommand                                           */
/* -------------------------------------------------------------------------- */

DatatypeDeclarationCommand::DatatypeDeclarationCommand(
    const api::Sort& datatype)
    : d_datatypes()
{
  d_datatypes.push_back(datatype);
}

DatatypeDeclarationCommand::DatatypeDeclarationCommand(
    const std::vector<api::Sort>& datatypes)
    : d_datatypes(datatypes)
{
}

const std::vector<api::Sort>& DatatypeDeclarationCommand::getDatatypes() const
{
  return d_datatypes;
}

void DatatypeDeclarationCommand::invoke(api::Solver* solver)
{
  d_commandStatus = CommandSuccess::instance();
}

Command* DatatypeDeclarationCommand::clone() const
{
  return new DatatypeDeclarationCommand(d_datatypes);
}

std::string DatatypeDeclarationCommand::getCommandName() const
{
  return "declare-datatypes";
}

void DatatypeDeclarationCommand::toStream(std::ostream& out,
                                          int toDepth,
                                          bool types,
                                          size_t dag,
                                          OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdDatatypeDeclaration(
      out, api::sortVectorToTypeNodes(d_datatypes));
}

}  // namespace CVC4
