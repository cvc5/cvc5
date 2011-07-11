/*********************                                                        */
/*! \file command.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of command objects.
 **
 ** Implementation of command objects.
 **/

#include <iostream>
#include <vector>
#include <utility>
#include <iterator>
#include <sstream>

#include "expr/command.h"
#include "smt/smt_engine.h"
#include "smt/bad_option_exception.h"
#include "util/output.h"
#include "util/sexpr.h"
#include "expr/node.h"
#include "printer/printer.h"

using namespace std;

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const Command& c) {
  c.toStream(out,
             Node::setdepth::getDepth(out),
             Node::printtypes::getPrintTypes(out),
             Node::setlanguage::getLanguage(out));
  return out;
}

ostream& operator<<(ostream& out, const Command* c) {
  if(c == NULL) {
    out << "null";
  } else {
    out << *c;
  }
  return out;
}

/* class Command */

void Command::invoke(SmtEngine* smtEngine, std::ostream& out) {
  invoke(smtEngine);
  printResult(out);
}

std::string Command::toString() const {
  std::stringstream ss;
  toStream(ss);
  return ss.str();
}

void Command::toStream(std::ostream& out, int toDepth, bool types,
                       OutputLanguage language) const {
  Printer::getPrinter(language)->toStream(out, this, toDepth, types);
}

void Command::printResult(std::ostream& out) const {
}

/* class EmptyCommand */

EmptyCommand::EmptyCommand(std::string name) :
  d_name(name) {
}

void EmptyCommand::invoke(SmtEngine* smtEngine) {
  /* empty commands have no implementation */
}

/* class AssertCommand */

AssertCommand::AssertCommand(const BoolExpr& e) :
  d_expr(e) {
}

void AssertCommand::invoke(SmtEngine* smtEngine) {
  smtEngine->assertFormula(d_expr);
}

/* class PushCommand */

void PushCommand::invoke(SmtEngine* smtEngine) {
  smtEngine->push();
}

/* class PopCommand */

void PopCommand::invoke(SmtEngine* smtEngine) {
  smtEngine->pop();
}

/* class CheckSatCommand */

CheckSatCommand::CheckSatCommand(const BoolExpr& expr) :
  d_expr(expr) {
}

void CheckSatCommand::invoke(SmtEngine* smtEngine) {
  d_result = smtEngine->checkSat(d_expr);
}

Result CheckSatCommand::getResult() const {
  return d_result;
}

void CheckSatCommand::printResult(std::ostream& out) const {
  out << d_result << endl;
}

/* class QueryCommand */

QueryCommand::QueryCommand(const BoolExpr& e) :
  d_expr(e) {
}

void QueryCommand::invoke(SmtEngine* smtEngine) {
  d_result = smtEngine->query(d_expr);
}

Result QueryCommand::getResult() const {
  return d_result;
}

void QueryCommand::printResult(std::ostream& out) const {
  out << d_result << endl;
}

/* class QuitCommand */

QuitCommand::QuitCommand() {
}

/* class CommandSequence */

CommandSequence::CommandSequence() :
  d_index(0) {
}

CommandSequence::~CommandSequence() {
  for(unsigned i = d_index; i < d_commandSequence.size(); ++i) {
    delete d_commandSequence[i];
  }
}

void CommandSequence::addCommand(Command* cmd) {
  d_commandSequence.push_back(cmd);
}

void CommandSequence::invoke(SmtEngine* smtEngine) {
  for(; d_index < d_commandSequence.size(); ++d_index) {
    d_commandSequence[d_index]->invoke(smtEngine);
    delete d_commandSequence[d_index];
  }
}

void CommandSequence::invoke(SmtEngine* smtEngine, std::ostream& out) {
  for(; d_index < d_commandSequence.size(); ++d_index) {
    d_commandSequence[d_index]->invoke(smtEngine, out);
    delete d_commandSequence[d_index];
  }
}

/* class DeclarationCommand */

DeclarationCommand::DeclarationCommand(const std::string& id, Type t) :
  d_type(t) {
  d_declaredSymbols.push_back(id);
}

DeclarationCommand::DeclarationCommand(const std::vector<std::string>& ids, Type t) :
  d_declaredSymbols(ids),
  d_type(t) {
}

const std::vector<std::string>& DeclarationCommand::getDeclaredSymbols() const {
  return d_declaredSymbols;
}

Type DeclarationCommand::getDeclaredType() const {
  return d_type;
}

/* class DefineFunctionCommand */

DefineFunctionCommand::DefineFunctionCommand(Expr func,
                                             const std::vector<Expr>& formals,
                                             Expr formula) :
  d_func(func),
  d_formals(formals),
  d_formula(formula) {
}

void DefineFunctionCommand::invoke(SmtEngine* smtEngine) {
  smtEngine->defineFunction(d_func, d_formals, d_formula);
}

/* class DefineFunctionCommand */

DefineNamedFunctionCommand::DefineNamedFunctionCommand(Expr func,
                                                       const std::vector<Expr>& formals,
                                                       Expr formula) :
  DefineFunctionCommand(func, formals, formula) {
}

void DefineNamedFunctionCommand::invoke(SmtEngine* smtEngine) {
  this->DefineFunctionCommand::invoke(smtEngine);
  if(d_func.getType().isBoolean()) {
    smtEngine->addToAssignment(d_func.getExprManager()->mkExpr(kind::APPLY,
                                                               d_func));
  }
}

/* class Simplify */

SimplifyCommand::SimplifyCommand(Expr term) :
  d_term(term) {
}

void SimplifyCommand::invoke(SmtEngine* smtEngine) {
  d_result = smtEngine->simplify(d_term);
}

Expr SimplifyCommand::getResult() const {
  return d_result;
}

void SimplifyCommand::printResult(std::ostream& out) const {
  out << d_result << endl;
}

/* class GetValueCommand */

GetValueCommand::GetValueCommand(Expr term) :
  d_term(term) {
}

void GetValueCommand::invoke(SmtEngine* smtEngine) {
  d_result = d_term.getExprManager()->mkExpr(kind::TUPLE, d_term,
                                             smtEngine->getValue(d_term));
}

Expr GetValueCommand::getResult() const {
  return d_result;
}

void GetValueCommand::printResult(std::ostream& out) const {
  out << d_result << endl;
}

/* class GetAssignmentCommand */

GetAssignmentCommand::GetAssignmentCommand() {
}

void GetAssignmentCommand::invoke(SmtEngine* smtEngine) {
  d_result = smtEngine->getAssignment();
}

SExpr GetAssignmentCommand::getResult() const {
  return d_result;
}

void GetAssignmentCommand::printResult(std::ostream& out) const {
  out << d_result << endl;
}

/* class GetAssertionsCommand */

GetAssertionsCommand::GetAssertionsCommand() {
}

void GetAssertionsCommand::invoke(SmtEngine* smtEngine) {
  stringstream ss;
  const vector<Expr> v = smtEngine->getAssertions();
  copy( v.begin(), v.end(), ostream_iterator<Expr>(ss, "\n") );
  d_result = ss.str();
}

std::string GetAssertionsCommand::getResult() const {
  return d_result;
}

void GetAssertionsCommand::printResult(std::ostream& out) const {
  out << d_result;
}

/* class SetBenchmarkStatusCommand */

SetBenchmarkStatusCommand::SetBenchmarkStatusCommand(BenchmarkStatus status) :
  d_status(status) {
}

void SetBenchmarkStatusCommand::invoke(SmtEngine* smtEngine) {
  stringstream ss;
  ss << d_status;
  SExpr status = ss.str();
  try {
    smtEngine->setInfo(":status", status);
    //d_result = "success";
  } catch(ModalException&) {
    d_result = "error";
  } catch(BadOptionException&) {
    // should not happen
    d_result = "error";
  }
}

/* class SetBenchmarkLogicCommand */

SetBenchmarkLogicCommand::SetBenchmarkLogicCommand(std::string logic) :
  d_logic(logic) {
}

void SetBenchmarkLogicCommand::invoke(SmtEngine* smtEngine) {
  try {
    smtEngine->setLogic(d_logic);
    //d_result = "success";
  } catch(ModalException&) {
    d_result = "error";
  }
}

/* class SetInfoCommand */

SetInfoCommand::SetInfoCommand(std::string flag, SExpr& sexpr) :
  d_flag(flag),
  d_sexpr(sexpr) {
}

void SetInfoCommand::invoke(SmtEngine* smtEngine) {
  try {
    smtEngine->setInfo(d_flag, d_sexpr);
    //d_result = "success";
  } catch(ModalException&) {
    d_result = "error";
  } catch(BadOptionException&) {
    d_result = "unsupported";
  }
}

std::string SetInfoCommand::getResult() const {
  return d_result;
}

void SetInfoCommand::printResult(std::ostream& out) const {
  if(d_result != "") {
    out << d_result << endl;
  }
}

/* class GetInfoCommand */

GetInfoCommand::GetInfoCommand(std::string flag) :
  d_flag(flag) {
}

void GetInfoCommand::invoke(SmtEngine* smtEngine) {
  try {
    stringstream ss;
    ss << smtEngine->getInfo(d_flag);
    d_result = ss.str();
  } catch(BadOptionException&) {
    d_result = "unsupported";
  }
}

std::string GetInfoCommand::getResult() const {
  return d_result;
}

void GetInfoCommand::printResult(std::ostream& out) const {
  if(d_result != "") {
    out << d_result << endl;
  }
}

/* class SetOptionCommand */

SetOptionCommand::SetOptionCommand(std::string flag, SExpr& sexpr) :
  d_flag(flag),
  d_sexpr(sexpr) {
}

void SetOptionCommand::invoke(SmtEngine* smtEngine) {
  try {
    smtEngine->setOption(d_flag, d_sexpr);
    //d_result = "success";
  } catch(ModalException&) {
    d_result = "error";
  } catch(BadOptionException&) {
    d_result = "unsupported";
  }
}

std::string SetOptionCommand::getResult() const {
  return d_result;
}

void SetOptionCommand::printResult(std::ostream& out) const {
  if(d_result != "") {
    out << d_result << endl;
  }
}

/* class GetOptionCommand */

GetOptionCommand::GetOptionCommand(std::string flag) :
  d_flag(flag) {
}

void GetOptionCommand::invoke(SmtEngine* smtEngine) {
  try {
    d_result = smtEngine->getOption(d_flag).getValue();
  } catch(BadOptionException&) {
    d_result = "unsupported";
  }
}

std::string GetOptionCommand::getResult() const {
  return d_result;
}

void GetOptionCommand::printResult(std::ostream& out) const {
  if(d_result != "") {
    out << d_result << endl;
  }
}

/* class DatatypeDeclarationCommand */

DatatypeDeclarationCommand::DatatypeDeclarationCommand(const DatatypeType& datatype) :
  d_datatypes() {
  d_datatypes.push_back(datatype);
  Debug("datatypes") << "Create datatype command." << endl;
}

DatatypeDeclarationCommand::DatatypeDeclarationCommand(const std::vector<DatatypeType>& datatypes) :
  d_datatypes(datatypes) {
  Debug("datatypes") << "Create datatype command." << endl;
}

void DatatypeDeclarationCommand::invoke(SmtEngine* smtEngine) {
  Debug("datatypes") << "Invoke datatype command." << endl;
  //smtEngine->addDatatypeDefinitions(d_datatype);
}

/* output stream insertion operator for benchmark statuses */
std::ostream& operator<<(std::ostream& out,
                         BenchmarkStatus status) {
  switch(status) {

  case SMT_SATISFIABLE:
    return out << "sat";

  case SMT_UNSATISFIABLE:
    return out << "unsat";

  case SMT_UNKNOWN:
    return out << "unknown";

  default:
    return out << "SetBenchmarkStatusCommand::[UNKNOWNSTATUS!]";
  }
}

}/* CVC4 namespace */
