/*********************                                                        */
/*! \file command.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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

// !!! Temporary until commands are migrated to the new API !!!
std::vector<Node> exprVectorToNodes(const std::vector<Expr>& exprs)
{
  std::vector<Node> nodes;
  nodes.reserve(exprs.size());

  for (Expr e : exprs)
  {
    nodes.push_back(Node::fromExpr(e));
  }

  return nodes;
}

// !!! Temporary until commands are migrated to the new API !!!
std::vector<TypeNode> typeVectorToTypeNodes(const std::vector<Type>& types)
{
  std::vector<TypeNode> typeNodes;
  typeNodes.reserve(types.size());

  for (Type t : types)
  {
    typeNodes.push_back(TypeNode::fromType(t));
  }

  return typeNodes;
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
    : d_solver(solver), d_commandStatus(nullptr), d_muted(false)
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

void Command::invoke(SmtEngine* smtEngine, std::ostream& out)
{
  invoke(smtEngine);
  if (!(isMuted() && ok()))
  {
    printResult(out,
                smtEngine->getOption("command-verbosity:" + getCommandName())
                    .getIntegerValue()
                    .toUnsignedInt());
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
void EmptyCommand::invoke(SmtEngine* smtEngine)
{
  /* empty commands have no implementation */
  d_commandStatus = CommandSuccess::instance();
}

Command* EmptyCommand::exportTo(ExprManager* exprManager,
                                ExprManagerMapCollection& variableMap)
{
  return new EmptyCommand(d_name);
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
void EchoCommand::invoke(SmtEngine* smtEngine)
{
  /* we don't have an output stream here, nothing to do */
  d_commandStatus = CommandSuccess::instance();
}

void EchoCommand::invoke(SmtEngine* smtEngine, std::ostream& out)
{
  out << d_output << std::endl;
  Trace("dtview::command") << "* ~COMMAND: echo |" << d_output << "|~"
                           << std::endl;
  d_commandStatus = CommandSuccess::instance();
  printResult(out,
              smtEngine->getOption("command-verbosity:" + getCommandName())
                  .getIntegerValue()
                  .toUnsignedInt());
}

Command* EchoCommand::exportTo(ExprManager* exprManager,
                               ExprManagerMapCollection& variableMap)
{
  return new EchoCommand(d_output);
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

AssertCommand::AssertCommand(const Expr& e, bool inUnsatCore)
    : d_expr(e), d_inUnsatCore(inUnsatCore)
{
}

Expr AssertCommand::getExpr() const { return d_expr; }
void AssertCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    smtEngine->assertFormula(d_expr, d_inUnsatCore);
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

Command* AssertCommand::exportTo(ExprManager* exprManager,
                                 ExprManagerMapCollection& variableMap)
{
  return new AssertCommand(d_expr.exportTo(exprManager, variableMap),
                           d_inUnsatCore);
}

Command* AssertCommand::clone() const
{
  return new AssertCommand(d_expr, d_inUnsatCore);
}

std::string AssertCommand::getCommandName() const { return "assert"; }

void AssertCommand::toStream(std::ostream& out,
                             int toDepth,
                             bool types,
                             size_t dag,
                             OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdAssert(out, Node::fromExpr(d_expr));
}

/* -------------------------------------------------------------------------- */
/* class PushCommand                                                          */
/* -------------------------------------------------------------------------- */

void PushCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    smtEngine->push();
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

Command* PushCommand::exportTo(ExprManager* exprManager,
                               ExprManagerMapCollection& variableMap)
{
  return new PushCommand();
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

void PopCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    smtEngine->pop();
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

Command* PopCommand::exportTo(ExprManager* exprManager,
                              ExprManagerMapCollection& variableMap)
{
  return new PopCommand();
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

CheckSatCommand::CheckSatCommand() : d_expr() {}

CheckSatCommand::CheckSatCommand(const Expr& expr) : d_expr(expr) {}

Expr CheckSatCommand::getExpr() const { return d_expr; }
void CheckSatCommand::invoke(SmtEngine* smtEngine)
{
  Trace("dtview::command") << "* ~COMMAND: " << getCommandName() << "~"
                           << std::endl;
  try
  {
    d_result = smtEngine->checkSat(d_expr);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Result CheckSatCommand::getResult() const { return d_result; }
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

Command* CheckSatCommand::exportTo(ExprManager* exprManager,
                                   ExprManagerMapCollection& variableMap)
{
  CheckSatCommand* c =
      new CheckSatCommand(d_expr.exportTo(exprManager, variableMap));
  c->d_result = d_result;
  return c;
}

Command* CheckSatCommand::clone() const
{
  CheckSatCommand* c = new CheckSatCommand(d_expr);
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
  Printer::getPrinter(language)->toStreamCmdCheckSat(out,
                                                     Node::fromExpr(d_expr));
}

/* -------------------------------------------------------------------------- */
/* class CheckSatAssumingCommand                                              */
/* -------------------------------------------------------------------------- */

CheckSatAssumingCommand::CheckSatAssumingCommand(Expr term) : d_terms({term}) {}

CheckSatAssumingCommand::CheckSatAssumingCommand(const std::vector<Expr>& terms)
    : d_terms(terms)
{
}

const std::vector<Expr>& CheckSatAssumingCommand::getTerms() const
{
  return d_terms;
}

void CheckSatAssumingCommand::invoke(SmtEngine* smtEngine)
{
  Trace("dtview::command") << "* ~COMMAND: (check-sat-assuming ( " << d_terms
                           << " )~" << std::endl;
  try
  {
    d_result = smtEngine->checkSat(d_terms);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Result CheckSatAssumingCommand::getResult() const
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

Command* CheckSatAssumingCommand::exportTo(
    ExprManager* exprManager, ExprManagerMapCollection& variableMap)
{
  vector<Expr> exportedTerms;
  for (const Expr& e : d_terms)
  {
    exportedTerms.push_back(e.exportTo(exprManager, variableMap));
  }
  CheckSatAssumingCommand* c = new CheckSatAssumingCommand(exportedTerms);
  c->d_result = d_result;
  return c;
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
  std::vector<Node> nodes;
  nodes.reserve(d_terms.size());
  for (const Expr& e : d_terms)
  {
    nodes.push_back(Node::fromExpr(e));
  }
  Printer::getPrinter(language)->toStreamCmdCheckSatAssuming(out, nodes);
}

/* -------------------------------------------------------------------------- */
/* class QueryCommand                                                         */
/* -------------------------------------------------------------------------- */

QueryCommand::QueryCommand(const Expr& e, bool inUnsatCore)
    : d_expr(e), d_inUnsatCore(inUnsatCore)
{
}

Expr QueryCommand::getExpr() const { return d_expr; }
void QueryCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    d_result = smtEngine->checkEntailed(d_expr);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Result QueryCommand::getResult() const { return d_result; }
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

Command* QueryCommand::exportTo(ExprManager* exprManager,
                                ExprManagerMapCollection& variableMap)
{
  QueryCommand* c = new QueryCommand(d_expr.exportTo(exprManager, variableMap),
                                     d_inUnsatCore);
  c->d_result = d_result;
  return c;
}

Command* QueryCommand::clone() const
{
  QueryCommand* c = new QueryCommand(d_expr, d_inUnsatCore);
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
  Printer::getPrinter(language)->toStreamCmdQuery(out, d_expr);
}

/* -------------------------------------------------------------------------- */
/* class DeclareSygusVarCommand */
/* -------------------------------------------------------------------------- */

DeclareSygusVarCommand::DeclareSygusVarCommand(const std::string& id,
                                               Expr var,
                                               Type t)
    : DeclarationDefinitionCommand(id), d_var(var), d_type(t)
{
}

Expr DeclareSygusVarCommand::getVar() const { return d_var; }
Type DeclareSygusVarCommand::getType() const { return d_type; }

void DeclareSygusVarCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    smtEngine->declareSygusVar(
        d_symbol, Node::fromExpr(d_var), TypeNode::fromType(d_type));
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* DeclareSygusVarCommand::exportTo(ExprManager* exprManager,
                                          ExprManagerMapCollection& variableMap)
{
  return new DeclareSygusVarCommand(d_symbol,
                                    d_var.exportTo(exprManager, variableMap),
                                    d_type.exportTo(exprManager, variableMap));
}

Command* DeclareSygusVarCommand::clone() const
{
  return new DeclareSygusVarCommand(d_symbol, d_var, d_type);
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
      out, Node::fromExpr(d_var), TypeNode::fromType(d_type));
}

/* -------------------------------------------------------------------------- */
/* class SynthFunCommand                                                      */
/* -------------------------------------------------------------------------- */

SynthFunCommand::SynthFunCommand(const api::Solver* solver,
                                 const std::string& id,
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
  d_solver = solver;
}

api::Term SynthFunCommand::getFunction() const { return d_fun; }

const std::vector<api::Term>& SynthFunCommand::getVars() const
{
  return d_vars;
}

api::Sort SynthFunCommand::getSort() const { return d_sort; }
bool SynthFunCommand::isInv() const { return d_isInv; }

const api::Grammar* SynthFunCommand::getGrammar() const { return d_grammar; }

void SynthFunCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    std::vector<Node> vns;
    for (const api::Term& t : d_vars)
    {
      vns.push_back(Node::fromExpr(t.getExpr()));
    }
    smtEngine->declareSynthFun(
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

Command* SynthFunCommand::exportTo(ExprManager* exprManager,
                                   ExprManagerMapCollection& variableMap)
{
  Unimplemented();
}

Command* SynthFunCommand::clone() const
{
  return new SynthFunCommand(
      d_solver, d_symbol, d_fun, d_vars, d_sort, d_isInv, d_grammar);
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

SygusConstraintCommand::SygusConstraintCommand(const Expr& e) : d_expr(e) {}

void SygusConstraintCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    smtEngine->assertSygusConstraint(d_expr);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Expr SygusConstraintCommand::getExpr() const { return d_expr; }

Command* SygusConstraintCommand::exportTo(ExprManager* exprManager,
                                          ExprManagerMapCollection& variableMap)
{
  return new SygusConstraintCommand(d_expr.exportTo(exprManager, variableMap));
}

Command* SygusConstraintCommand::clone() const
{
  return new SygusConstraintCommand(d_expr);
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
  Printer::getPrinter(language)->toStreamCmdConstraint(out,
                                                       Node::fromExpr(d_expr));
}

/* -------------------------------------------------------------------------- */
/* class SygusInvConstraintCommand */
/* -------------------------------------------------------------------------- */

SygusInvConstraintCommand::SygusInvConstraintCommand(
    const std::vector<Expr>& predicates)
    : d_predicates(predicates)
{
}

SygusInvConstraintCommand::SygusInvConstraintCommand(const Expr& inv,
                                                     const Expr& pre,
                                                     const Expr& trans,
                                                     const Expr& post)
    : SygusInvConstraintCommand(std::vector<Expr>{inv, pre, trans, post})
{
}

void SygusInvConstraintCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    smtEngine->assertSygusInvConstraint(
        d_predicates[0], d_predicates[1], d_predicates[2], d_predicates[3]);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

const std::vector<Expr>& SygusInvConstraintCommand::getPredicates() const
{
  return d_predicates;
}

Command* SygusInvConstraintCommand::exportTo(
    ExprManager* exprManager, ExprManagerMapCollection& variableMap)
{
  return new SygusInvConstraintCommand(d_predicates);
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
      Node::fromExpr(d_predicates[0]),
      Node::fromExpr(d_predicates[1]),
      Node::fromExpr(d_predicates[2]),
      Node::fromExpr(d_predicates[3]));
}

/* -------------------------------------------------------------------------- */
/* class CheckSynthCommand                                                    */
/* -------------------------------------------------------------------------- */

void CheckSynthCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    d_result = smtEngine->checkSynth();
    d_commandStatus = CommandSuccess::instance();
    smt::SmtScope scope(smtEngine);
    d_solution.clear();
    // check whether we should print the status
    if (d_result.asSatisfiabilityResult() != Result::UNSAT
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
    if (d_result.asSatisfiabilityResult() == Result::UNSAT
        && options::sygusOut() != options::SygusSolutionOutMode::STATUS)
    {
      // printing a synthesis solution is a non-constant
      // method, since it invokes a sophisticated algorithm
      // (Figure 5 of Reynolds et al. CAV 2015).
      // Hence, we must call here print solution here,
      // instead of during printResult.
      smtEngine->printSynthSolution(d_solution);
    }
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Result CheckSynthCommand::getResult() const { return d_result; }
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

Command* CheckSynthCommand::exportTo(ExprManager* exprManager,
                                     ExprManagerMapCollection& variableMap)
{
  return new CheckSynthCommand();
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

void ResetCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    smtEngine->reset();
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* ResetCommand::exportTo(ExprManager* exprManager,
                                ExprManagerMapCollection& variableMap)
{
  return new ResetCommand();
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

void ResetAssertionsCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    smtEngine->resetAssertions();
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* ResetAssertionsCommand::exportTo(ExprManager* exprManager,
                                          ExprManagerMapCollection& variableMap)
{
  return new ResetAssertionsCommand();
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

void QuitCommand::invoke(SmtEngine* smtEngine)
{
  Dump("benchmark") << *this;
  d_commandStatus = CommandSuccess::instance();
}

Command* QuitCommand::exportTo(ExprManager* exprManager,
                               ExprManagerMapCollection& variableMap)
{
  return new QuitCommand();
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
void CommentCommand::invoke(SmtEngine* smtEngine)
{
  Dump("benchmark") << *this;
  d_commandStatus = CommandSuccess::instance();
}

Command* CommentCommand::exportTo(ExprManager* exprManager,
                                  ExprManagerMapCollection& variableMap)
{
  return new CommentCommand(d_comment);
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
void CommandSequence::invoke(SmtEngine* smtEngine)
{
  for (; d_index < d_commandSequence.size(); ++d_index)
  {
    d_commandSequence[d_index]->invoke(smtEngine);
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

void CommandSequence::invoke(SmtEngine* smtEngine, std::ostream& out)
{
  for (; d_index < d_commandSequence.size(); ++d_index)
  {
    d_commandSequence[d_index]->invoke(smtEngine, out);
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

Command* CommandSequence::exportTo(ExprManager* exprManager,
                                   ExprManagerMapCollection& variableMap)
{
  CommandSequence* seq = new CommandSequence();
  for (iterator i = begin(); i != end(); ++i)
  {
    Command* cmd_to_export = *i;
    Command* cmd = cmd_to_export->exportTo(exprManager, variableMap);
    seq->addCommand(cmd);
    Debug("export") << "[export] so far converted: " << seq << endl;
  }
  seq->d_index = d_index;
  return seq;
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
                                               Expr func,
                                               Type t)
    : DeclarationDefinitionCommand(id),
      d_func(func),
      d_type(t),
      d_printInModel(true),
      d_printInModelSetByUser(false)
{
}

Expr DeclareFunctionCommand::getFunction() const { return d_func; }
Type DeclareFunctionCommand::getType() const { return d_type; }
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

void DeclareFunctionCommand::invoke(SmtEngine* smtEngine)
{
  d_commandStatus = CommandSuccess::instance();
}

Command* DeclareFunctionCommand::exportTo(ExprManager* exprManager,
                                          ExprManagerMapCollection& variableMap)
{
  DeclareFunctionCommand* dfc =
      new DeclareFunctionCommand(d_symbol,
                                 d_func.exportTo(exprManager, variableMap),
                                 d_type.exportTo(exprManager, variableMap));
  dfc->d_printInModel = d_printInModel;
  dfc->d_printInModelSetByUser = d_printInModelSetByUser;
  return dfc;
}

Command* DeclareFunctionCommand::clone() const
{
  DeclareFunctionCommand* dfc =
      new DeclareFunctionCommand(d_symbol, d_func, d_type);
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
      out, d_func.toString(), TypeNode::fromType(d_type));
}

/* -------------------------------------------------------------------------- */
/* class DeclareTypeCommand                                                   */
/* -------------------------------------------------------------------------- */

DeclareTypeCommand::DeclareTypeCommand(const std::string& id,
                                       size_t arity,
                                       Type t)
    : DeclarationDefinitionCommand(id), d_arity(arity), d_type(t)
{
}

size_t DeclareTypeCommand::getArity() const { return d_arity; }
Type DeclareTypeCommand::getType() const { return d_type; }
void DeclareTypeCommand::invoke(SmtEngine* smtEngine)
{
  d_commandStatus = CommandSuccess::instance();
}

Command* DeclareTypeCommand::exportTo(ExprManager* exprManager,
                                      ExprManagerMapCollection& variableMap)
{
  return new DeclareTypeCommand(
      d_symbol, d_arity, d_type.exportTo(exprManager, variableMap));
}

Command* DeclareTypeCommand::clone() const
{
  return new DeclareTypeCommand(d_symbol, d_arity, d_type);
}

std::string DeclareTypeCommand::getCommandName() const
{
  return "declare-sort";
}

void DeclareTypeCommand::toStream(std::ostream& out,
                                  int toDepth,
                                  bool types,
                                  size_t dag,
                                  OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdDeclareType(
      out, d_type.toString(), d_arity, TypeNode::fromType(d_type));
}

/* -------------------------------------------------------------------------- */
/* class DefineTypeCommand                                                    */
/* -------------------------------------------------------------------------- */

DefineTypeCommand::DefineTypeCommand(const std::string& id, Type t)
    : DeclarationDefinitionCommand(id), d_params(), d_type(t)
{
}

DefineTypeCommand::DefineTypeCommand(const std::string& id,
                                     const std::vector<Type>& params,
                                     Type t)
    : DeclarationDefinitionCommand(id), d_params(params), d_type(t)
{
}

const std::vector<Type>& DefineTypeCommand::getParameters() const
{
  return d_params;
}

Type DefineTypeCommand::getType() const { return d_type; }
void DefineTypeCommand::invoke(SmtEngine* smtEngine)
{
  d_commandStatus = CommandSuccess::instance();
}

Command* DefineTypeCommand::exportTo(ExprManager* exprManager,
                                     ExprManagerMapCollection& variableMap)
{
  vector<Type> params;
  transform(d_params.begin(),
            d_params.end(),
            back_inserter(params),
            ExportTransformer(exprManager, variableMap));
  Type type = d_type.exportTo(exprManager, variableMap);
  return new DefineTypeCommand(d_symbol, params, type);
}

Command* DefineTypeCommand::clone() const
{
  return new DefineTypeCommand(d_symbol, d_params, d_type);
}

std::string DefineTypeCommand::getCommandName() const { return "define-sort"; }

void DefineTypeCommand::toStream(std::ostream& out,
                                 int toDepth,
                                 bool types,
                                 size_t dag,
                                 OutputLanguage language) const
{
  Printer::getPrinter(language)->toStreamCmdDefineType(
      out,
      d_symbol,
      typeVectorToTypeNodes(d_params),
      TypeNode::fromType(d_type));
}

/* -------------------------------------------------------------------------- */
/* class DefineFunctionCommand                                                */
/* -------------------------------------------------------------------------- */

DefineFunctionCommand::DefineFunctionCommand(const std::string& id,
                                             Expr func,
                                             Expr formula,
                                             bool global)
    : DeclarationDefinitionCommand(id),
      d_func(func),
      d_formals(),
      d_formula(formula),
      d_global(global)
{
}

DefineFunctionCommand::DefineFunctionCommand(const std::string& id,
                                             Expr func,
                                             const std::vector<Expr>& formals,
                                             Expr formula,
                                             bool global)
    : DeclarationDefinitionCommand(id),
      d_func(func),
      d_formals(formals),
      d_formula(formula),
      d_global(global)

{
}

Expr DefineFunctionCommand::getFunction() const { return d_func; }
const std::vector<Expr>& DefineFunctionCommand::getFormals() const
{
  return d_formals;
}

Expr DefineFunctionCommand::getFormula() const { return d_formula; }
void DefineFunctionCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    if (!d_func.isNull())
    {
      smtEngine->defineFunction(d_func, d_formals, d_formula, d_global);
    }
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* DefineFunctionCommand::exportTo(ExprManager* exprManager,
                                         ExprManagerMapCollection& variableMap)
{
  Expr func = d_func.exportTo(
      exprManager, variableMap, /* flags = */ ExprManager::VAR_FLAG_DEFINED);
  vector<Expr> formals;
  transform(d_formals.begin(),
            d_formals.end(),
            back_inserter(formals),
            ExportTransformer(exprManager, variableMap));
  Expr formula = d_formula.exportTo(exprManager, variableMap);
  return new DefineFunctionCommand(d_symbol, func, formals, formula, d_global);
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
      exprVectorToNodes(d_formals),
      Node::fromExpr(d_func).getType().getRangeType(),
      Node::fromExpr(d_formula));
}

/* -------------------------------------------------------------------------- */
/* class DefineNamedFunctionCommand                                           */
/* -------------------------------------------------------------------------- */

DefineNamedFunctionCommand::DefineNamedFunctionCommand(
    const std::string& id,
    Expr func,
    const std::vector<Expr>& formals,
    Expr formula,
    bool global)
    : DefineFunctionCommand(id, func, formals, formula, global)
{
}

void DefineNamedFunctionCommand::invoke(SmtEngine* smtEngine)
{
  this->DefineFunctionCommand::invoke(smtEngine);
  if (!d_func.isNull() && d_func.getType().isBoolean())
  {
    smtEngine->addToAssignment(d_func);
  }
  d_commandStatus = CommandSuccess::instance();
}

Command* DefineNamedFunctionCommand::exportTo(
    ExprManager* exprManager, ExprManagerMapCollection& variableMap)
{
  Expr func = d_func.exportTo(exprManager, variableMap);
  vector<Expr> formals;
  transform(d_formals.begin(),
            d_formals.end(),
            back_inserter(formals),
            ExportTransformer(exprManager, variableMap));
  Expr formula = d_formula.exportTo(exprManager, variableMap);
  return new DefineNamedFunctionCommand(
      d_symbol, func, formals, formula, d_global);
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
      exprVectorToNodes(d_formals),
      Node::fromExpr(d_func).getType().getRangeType(),
      Node::fromExpr(d_formula));
}

/* -------------------------------------------------------------------------- */
/* class DefineFunctionRecCommand                                             */
/* -------------------------------------------------------------------------- */

DefineFunctionRecCommand::DefineFunctionRecCommand(
    const api::Solver* solver,
    api::Term func,
    const std::vector<api::Term>& formals,
    api::Term formula,
    bool global)
    : Command(solver), d_global(global)
{
  d_funcs.push_back(func);
  d_formals.push_back(formals);
  d_formulas.push_back(formula);
}

DefineFunctionRecCommand::DefineFunctionRecCommand(
    const api::Solver* solver,
    const std::vector<api::Term>& funcs,
    const std::vector<std::vector<api::Term>>& formals,
    const std::vector<api::Term>& formulas,
    bool global)
    : Command(solver),
      d_funcs(funcs),
      d_formals(formals),
      d_formulas(formulas),
      d_global(global)
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

void DefineFunctionRecCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    d_solver->defineFunsRec(d_funcs, d_formals, d_formulas, d_global);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* DefineFunctionRecCommand::exportTo(
    ExprManager* exprManager, ExprManagerMapCollection& variableMap)
{
  Unimplemented();
}

Command* DefineFunctionRecCommand::clone() const
{
  return new DefineFunctionRecCommand(
      d_solver, d_funcs, d_formals, d_formulas, d_global);
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
    Expr expr,
    const std::vector<Expr>& expr_values,
    const std::string& str_value)
    : d_attr(attr),
      d_expr(expr),
      d_expr_values(expr_values),
      d_str_value(str_value)
{
}

SetUserAttributeCommand::SetUserAttributeCommand(const std::string& attr,
                                                 Expr expr)
    : SetUserAttributeCommand(attr, expr, {}, "")
{
}

SetUserAttributeCommand::SetUserAttributeCommand(
    const std::string& attr, Expr expr, const std::vector<Expr>& values)
    : SetUserAttributeCommand(attr, expr, values, "")
{
}

SetUserAttributeCommand::SetUserAttributeCommand(const std::string& attr,
                                                 Expr expr,
                                                 const std::string& value)
    : SetUserAttributeCommand(attr, expr, {}, value)
{
}

void SetUserAttributeCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    if (!d_expr.isNull())
    {
      smtEngine->setUserAttribute(d_attr, d_expr, d_expr_values, d_str_value);
    }
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* SetUserAttributeCommand::exportTo(
    ExprManager* exprManager, ExprManagerMapCollection& variableMap)
{
  Expr expr = d_expr.exportTo(exprManager, variableMap);
  return new SetUserAttributeCommand(d_attr, expr, d_expr_values, d_str_value);
}

Command* SetUserAttributeCommand::clone() const
{
  return new SetUserAttributeCommand(
      d_attr, d_expr, d_expr_values, d_str_value);
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
      out, d_attr, Node::fromExpr(d_expr));
}

/* -------------------------------------------------------------------------- */
/* class SimplifyCommand                                                      */
/* -------------------------------------------------------------------------- */

SimplifyCommand::SimplifyCommand(Expr term) : d_term(term) {}
Expr SimplifyCommand::getTerm() const { return d_term; }
void SimplifyCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    d_result = smtEngine->simplify(Node::fromExpr(d_term)).toExpr();
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

Expr SimplifyCommand::getResult() const { return d_result; }
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

Command* SimplifyCommand::exportTo(ExprManager* exprManager,
                                   ExprManagerMapCollection& variableMap)
{
  SimplifyCommand* c =
      new SimplifyCommand(d_term.exportTo(exprManager, variableMap));
  c->d_result = d_result.exportTo(exprManager, variableMap);
  return c;
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
  Printer::getPrinter(language)->toStreamCmdSimplify(out, d_term);
}

/* -------------------------------------------------------------------------- */
/* class ExpandDefinitionsCommand                                             */
/* -------------------------------------------------------------------------- */

ExpandDefinitionsCommand::ExpandDefinitionsCommand(Expr term) : d_term(term) {}
Expr ExpandDefinitionsCommand::getTerm() const { return d_term; }
void ExpandDefinitionsCommand::invoke(SmtEngine* smtEngine)
{
  Node t = Node::fromExpr(d_term);
  d_result = smtEngine->expandDefinitions(t).toExpr();
  d_commandStatus = CommandSuccess::instance();
}

Expr ExpandDefinitionsCommand::getResult() const { return d_result; }
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

Command* ExpandDefinitionsCommand::exportTo(
    ExprManager* exprManager, ExprManagerMapCollection& variableMap)
{
  ExpandDefinitionsCommand* c =
      new ExpandDefinitionsCommand(d_term.exportTo(exprManager, variableMap));
  c->d_result = d_result.exportTo(exprManager, variableMap);
  return c;
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
  Printer::getPrinter(language)->toStreamCmdExpandDefinitions(
      out, Node::fromExpr(d_term));
}

/* -------------------------------------------------------------------------- */
/* class GetValueCommand                                                      */
/* -------------------------------------------------------------------------- */

GetValueCommand::GetValueCommand(Expr term) : d_terms()
{
  d_terms.push_back(term);
}

GetValueCommand::GetValueCommand(const std::vector<Expr>& terms)
    : d_terms(terms)
{
  PrettyCheckArgument(
      terms.size() >= 1, terms, "cannot get-value of an empty set of terms");
}

const std::vector<Expr>& GetValueCommand::getTerms() const { return d_terms; }
void GetValueCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    ExprManager* em = smtEngine->getExprManager();
    NodeManager* nm = NodeManager::fromExprManager(em);
    smt::SmtScope scope(smtEngine);
    vector<Expr> result = smtEngine->getValues(d_terms);
    Assert(result.size() == d_terms.size());
    for (int i = 0, size = d_terms.size(); i < size; i++)
    {
      Expr e = d_terms[i];
      Node eNode = Node::fromExpr(e);
      Assert(nm == NodeManager::fromExprManager(e.getExprManager()));
      Node request = options::expandDefinitions()
                         ? smtEngine->expandDefinitions(eNode)
                         : eNode;
      Node value = Node::fromExpr(result[i]);
      if (value.getType().isInteger() && request.getType() == nm->realType())
      {
        // Need to wrap in division-by-one so that output printers know this
        // is an integer-looking constant that really should be output as
        // a rational.  Necessary for SMT-LIB standards compliance.
        value = nm->mkNode(kind::DIVISION, value, nm->mkConst(Rational(1)));
      }
      result[i] = nm->mkNode(kind::SEXPR, request, value).toExpr();
    }
    d_result = em->mkExpr(kind::SEXPR, result);
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

Expr GetValueCommand::getResult() const { return d_result; }
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

Command* GetValueCommand::exportTo(ExprManager* exprManager,
                                   ExprManagerMapCollection& variableMap)
{
  vector<Expr> exportedTerms;
  for (std::vector<Expr>::const_iterator i = d_terms.begin();
       i != d_terms.end();
       ++i)
  {
    exportedTerms.push_back((*i).exportTo(exprManager, variableMap));
  }
  GetValueCommand* c = new GetValueCommand(exportedTerms);
  c->d_result = d_result.exportTo(exprManager, variableMap);
  return c;
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
      out, exprVectorToNodes(d_terms));
}

/* -------------------------------------------------------------------------- */
/* class GetAssignmentCommand                                                 */
/* -------------------------------------------------------------------------- */

GetAssignmentCommand::GetAssignmentCommand() {}
void GetAssignmentCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    std::vector<std::pair<Expr, Expr>> assignments = smtEngine->getAssignment();
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

Command* GetAssignmentCommand::exportTo(ExprManager* exprManager,
                                        ExprManagerMapCollection& variableMap)
{
  GetAssignmentCommand* c = new GetAssignmentCommand();
  c->d_result = d_result;
  return c;
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
void GetModelCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    d_result = smtEngine->getModel();
    d_smtEngine = smtEngine;
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

Command* GetModelCommand::exportTo(ExprManager* exprManager,
                                   ExprManagerMapCollection& variableMap)
{
  GetModelCommand* c = new GetModelCommand();
  c->d_result = d_result;
  c->d_smtEngine = d_smtEngine;
  return c;
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
void BlockModelCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    smtEngine->blockModel();
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

Command* BlockModelCommand::exportTo(ExprManager* exprManager,
                                     ExprManagerMapCollection& variableMap)
{
  BlockModelCommand* c = new BlockModelCommand();
  return c;
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

BlockModelValuesCommand::BlockModelValuesCommand(const std::vector<Expr>& terms)
    : d_terms(terms)
{
  PrettyCheckArgument(terms.size() >= 1,
                      terms,
                      "cannot block-model-values of an empty set of terms");
}

const std::vector<Expr>& BlockModelValuesCommand::getTerms() const
{
  return d_terms;
}
void BlockModelValuesCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    smtEngine->blockModelValues(d_terms);
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

Command* BlockModelValuesCommand::exportTo(
    ExprManager* exprManager, ExprManagerMapCollection& variableMap)
{
  vector<Expr> exportedTerms;
  for (std::vector<Expr>::const_iterator i = d_terms.begin();
       i != d_terms.end();
       ++i)
  {
    exportedTerms.push_back((*i).exportTo(exprManager, variableMap));
  }
  BlockModelValuesCommand* c = new BlockModelValuesCommand(exportedTerms);
  return c;
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
      out, exprVectorToNodes(d_terms));
}

/* -------------------------------------------------------------------------- */
/* class GetProofCommand                                                      */
/* -------------------------------------------------------------------------- */

GetProofCommand::GetProofCommand() : d_smtEngine(nullptr), d_result(nullptr) {}
void GetProofCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    d_smtEngine = smtEngine;
    d_result = &smtEngine->getProof();
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

const Proof& GetProofCommand::getResult() const { return *d_result; }
void GetProofCommand::printResult(std::ostream& out, uint32_t verbosity) const
{
  if (!ok())
  {
    this->Command::printResult(out, verbosity);
  }
  else
  {
    smt::SmtScope scope(d_smtEngine);
    d_result->toStream(out);
  }
}

Command* GetProofCommand::exportTo(ExprManager* exprManager,
                                   ExprManagerMapCollection& variableMap)
{
  GetProofCommand* c = new GetProofCommand();
  c->d_result = d_result;
  c->d_smtEngine = d_smtEngine;
  return c;
}

Command* GetProofCommand::clone() const
{
  GetProofCommand* c = new GetProofCommand();
  c->d_result = d_result;
  c->d_smtEngine = d_smtEngine;
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
void GetInstantiationsCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    d_smtEngine = smtEngine;
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

Command* GetInstantiationsCommand::exportTo(
    ExprManager* exprManager, ExprManagerMapCollection& variableMap)
{
  GetInstantiationsCommand* c = new GetInstantiationsCommand();
  // c->d_result = d_result;
  c->d_smtEngine = d_smtEngine;
  return c;
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
void GetSynthSolutionCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    d_smtEngine = smtEngine;
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

Command* GetSynthSolutionCommand::exportTo(
    ExprManager* exprManager, ExprManagerMapCollection& variableMap)
{
  GetSynthSolutionCommand* c = new GetSynthSolutionCommand();
  c->d_smtEngine = d_smtEngine;
  return c;
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

GetInterpolCommand::GetInterpolCommand(const api::Solver* solver,
                                       const std::string& name,
                                       api::Term conj)
    : Command(solver), d_name(name), d_conj(conj), d_resultStatus(false)
{
}
GetInterpolCommand::GetInterpolCommand(const api::Solver* solver,
                                       const std::string& name,
                                       api::Term conj,
                                       api::Grammar* g)
    : Command(solver),
      d_name(name),
      d_conj(conj),
      d_sygus_grammar(g),
      d_resultStatus(false)
{
}

api::Term GetInterpolCommand::getConjecture() const { return d_conj; }

const api::Grammar* GetInterpolCommand::getGrammar() const
{
  return d_sygus_grammar;
}

api::Term GetInterpolCommand::getResult() const { return d_result; }

void GetInterpolCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    if (!d_sygus_grammar)
    {
      d_resultStatus = d_solver->getInterpolant(d_conj, d_result);
    }
    else
    {
      d_resultStatus =
          d_solver->getInterpolant(d_conj, *d_sygus_grammar, d_result);
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

Command* GetInterpolCommand::exportTo(ExprManager* exprManager,
                                      ExprManagerMapCollection& variableMap)
{
  Unimplemented();
}

Command* GetInterpolCommand::clone() const
{
  GetInterpolCommand* c =
      new GetInterpolCommand(d_solver, d_name, d_conj, d_sygus_grammar);
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

GetAbductCommand::GetAbductCommand(const api::Solver* solver,
                                   const std::string& name,
                                   api::Term conj)
    : Command(solver), d_name(name), d_conj(conj), d_resultStatus(false)
{
}
GetAbductCommand::GetAbductCommand(const api::Solver* solver,
                                   const std::string& name,
                                   api::Term conj,
                                   api::Grammar* g)
    : Command(solver),
      d_name(name),
      d_conj(conj),
      d_sygus_grammar(g),
      d_resultStatus(false)
{
}

api::Term GetAbductCommand::getConjecture() const { return d_conj; }

const api::Grammar* GetAbductCommand::getGrammar() const
{
  return d_sygus_grammar;
}

std::string GetAbductCommand::getAbductName() const { return d_name; }
api::Term GetAbductCommand::getResult() const { return d_result; }

void GetAbductCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    if (!d_sygus_grammar)
    {
      d_resultStatus = d_solver->getAbduct(d_conj, d_result);
    }
    else
    {
      d_resultStatus = d_solver->getAbduct(d_conj, *d_sygus_grammar, d_result);
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

Command* GetAbductCommand::exportTo(ExprManager* exprManager,
                                    ExprManagerMapCollection& variableMap)
{
  Unimplemented();
}

Command* GetAbductCommand::clone() const
{
  GetAbductCommand* c =
      new GetAbductCommand(d_solver, d_name, d_conj, d_sygus_grammar);
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
    : d_expr(), d_doFull(true)
{
}
GetQuantifierEliminationCommand::GetQuantifierEliminationCommand(
    const Expr& expr, bool doFull)
    : d_expr(expr), d_doFull(doFull)
{
}

Expr GetQuantifierEliminationCommand::getExpr() const { return d_expr; }
bool GetQuantifierEliminationCommand::getDoFull() const { return d_doFull; }
void GetQuantifierEliminationCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    d_result =
        smtEngine->getQuantifierElimination(Node::fromExpr(d_expr), d_doFull)
            .toExpr();
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Expr GetQuantifierEliminationCommand::getResult() const { return d_result; }
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

Command* GetQuantifierEliminationCommand::exportTo(
    ExprManager* exprManager, ExprManagerMapCollection& variableMap)
{
  GetQuantifierEliminationCommand* c = new GetQuantifierEliminationCommand(
      d_expr.exportTo(exprManager, variableMap), d_doFull);
  c->d_result = d_result;
  return c;
}

Command* GetQuantifierEliminationCommand::clone() const
{
  GetQuantifierEliminationCommand* c =
      new GetQuantifierEliminationCommand(d_expr, d_doFull);
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
      out, Node::fromExpr(d_expr));
}

/* -------------------------------------------------------------------------- */
/* class GetUnsatAssumptionsCommand                                           */
/* -------------------------------------------------------------------------- */

GetUnsatAssumptionsCommand::GetUnsatAssumptionsCommand() {}

void GetUnsatAssumptionsCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    std::vector<Node> uassumps = smtEngine->getUnsatAssumptions();
    d_result.clear();
    for (const Node& n : uassumps)
    {
      d_result.push_back(n.toExpr());
    }
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

std::vector<Expr> GetUnsatAssumptionsCommand::getResult() const
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

Command* GetUnsatAssumptionsCommand::exportTo(
    ExprManager* exprManager, ExprManagerMapCollection& variableMap)
{
  GetUnsatAssumptionsCommand* c = new GetUnsatAssumptionsCommand;
  c->d_result = d_result;
  return c;
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
void GetUnsatCoreCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    d_result = smtEngine->getUnsatCore();
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

Command* GetUnsatCoreCommand::exportTo(ExprManager* exprManager,
                                       ExprManagerMapCollection& variableMap)
{
  GetUnsatCoreCommand* c = new GetUnsatCoreCommand;
  c->d_result = d_result;
  return c;
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
void GetAssertionsCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    stringstream ss;
    const vector<Expr> v = smtEngine->getAssertions();
    ss << "(\n";
    copy(v.begin(), v.end(), ostream_iterator<Expr>(ss, "\n"));
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

Command* GetAssertionsCommand::exportTo(ExprManager* exprManager,
                                        ExprManagerMapCollection& variableMap)
{
  GetAssertionsCommand* c = new GetAssertionsCommand();
  c->d_result = d_result;
  return c;
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

void SetBenchmarkStatusCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    stringstream ss;
    ss << d_status;
    SExpr status = SExpr(ss.str());
    smtEngine->setInfo("status", status);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* SetBenchmarkStatusCommand::exportTo(
    ExprManager* exprManager, ExprManagerMapCollection& variableMap)
{
  return new SetBenchmarkStatusCommand(d_status);
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
  Printer::getPrinter(language)->toStreamCmdSetBenchmarkStatus(out, d_status);
}

/* -------------------------------------------------------------------------- */
/* class SetBenchmarkLogicCommand                                             */
/* -------------------------------------------------------------------------- */

SetBenchmarkLogicCommand::SetBenchmarkLogicCommand(std::string logic)
    : d_logic(logic)
{
}

std::string SetBenchmarkLogicCommand::getLogic() const { return d_logic; }
void SetBenchmarkLogicCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    smtEngine->setLogic(d_logic);
    d_commandStatus = CommandSuccess::instance();
  }
  catch (exception& e)
  {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* SetBenchmarkLogicCommand::exportTo(
    ExprManager* exprManager, ExprManagerMapCollection& variableMap)
{
  return new SetBenchmarkLogicCommand(d_logic);
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
void SetInfoCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    smtEngine->setInfo(d_flag, d_sexpr);
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

Command* SetInfoCommand::exportTo(ExprManager* exprManager,
                                  ExprManagerMapCollection& variableMap)
{
  return new SetInfoCommand(d_flag, d_sexpr);
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
void GetInfoCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    vector<SExpr> v;
    v.push_back(SExpr(SExpr::Keyword(string(":") + d_flag)));
    v.push_back(smtEngine->getInfo(d_flag));
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

Command* GetInfoCommand::exportTo(ExprManager* exprManager,
                                  ExprManagerMapCollection& variableMap)
{
  GetInfoCommand* c = new GetInfoCommand(d_flag);
  c->d_result = d_result;
  return c;
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
void SetOptionCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    smtEngine->setOption(d_flag, d_sexpr);
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

Command* SetOptionCommand::exportTo(ExprManager* exprManager,
                                    ExprManagerMapCollection& variableMap)
{
  return new SetOptionCommand(d_flag, d_sexpr);
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
void GetOptionCommand::invoke(SmtEngine* smtEngine)
{
  try
  {
    SExpr res = smtEngine->getOption(d_flag);
    d_result = res.toString();
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

Command* GetOptionCommand::exportTo(ExprManager* exprManager,
                                    ExprManagerMapCollection& variableMap)
{
  GetOptionCommand* c = new GetOptionCommand(d_flag);
  c->d_result = d_result;
  return c;
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

SetExpressionNameCommand::SetExpressionNameCommand(Expr expr, std::string name)
    : d_expr(expr), d_name(name)
{
}

void SetExpressionNameCommand::invoke(SmtEngine* smtEngine)
{
  smtEngine->setExpressionName(d_expr, d_name);
  d_commandStatus = CommandSuccess::instance();
}

Command* SetExpressionNameCommand::exportTo(
    ExprManager* exprManager, ExprManagerMapCollection& variableMap)
{
  SetExpressionNameCommand* c = new SetExpressionNameCommand(
      d_expr.exportTo(exprManager, variableMap), d_name);
  return c;
}

Command* SetExpressionNameCommand::clone() const
{
  SetExpressionNameCommand* c = new SetExpressionNameCommand(d_expr, d_name);
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
      out, Node::fromExpr(d_expr), d_name);
}

/* -------------------------------------------------------------------------- */
/* class DatatypeDeclarationCommand                                           */
/* -------------------------------------------------------------------------- */

DatatypeDeclarationCommand::DatatypeDeclarationCommand(const Type& datatype)
    : d_datatypes()
{
  d_datatypes.push_back(datatype);
}

DatatypeDeclarationCommand::DatatypeDeclarationCommand(
    const std::vector<Type>& datatypes)
    : d_datatypes(datatypes)
{
}

const std::vector<Type>& DatatypeDeclarationCommand::getDatatypes() const
{
  return d_datatypes;
}

void DatatypeDeclarationCommand::invoke(SmtEngine* smtEngine)
{
  d_commandStatus = CommandSuccess::instance();
}

Command* DatatypeDeclarationCommand::exportTo(
    ExprManager* exprManager, ExprManagerMapCollection& variableMap)
{
  throw ExportUnsupportedException(
      "export of DatatypeDeclarationCommand unsupported");
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
      out, typeVectorToTypeNodes(d_datatypes));
}

}  // namespace CVC4
