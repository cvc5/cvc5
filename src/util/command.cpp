/*
 * command.cpp
 *
 *  Created on: Nov 25, 2009
 *      Author: dejan
 */

#include <map>
#include "util/command.h"
#include "smt/smt_engine.h"

using namespace std;

namespace CVC4 {

ostream& operator<<(ostream& out, const Command& c) {
  c.toString(out);
  return out;
}

EmptyCommand::EmptyCommand(string name) :
  d_name(name) {
}

void EmptyCommand::invoke(SmtEngine* smt_engine) {
}

AssertCommand::AssertCommand(const BoolExpr& e) :
  d_expr(e) {
}

void AssertCommand::invoke(SmtEngine* smt_engine) {
  smt_engine->assertFormula(d_expr);
}

CheckSatCommand::CheckSatCommand() {
}

CheckSatCommand::CheckSatCommand(const BoolExpr& e) :
  d_expr(e) {
}

void CheckSatCommand::invoke(SmtEngine* smt_engine) {
  smt_engine->checkSat(d_expr);
}

QueryCommand::QueryCommand(const BoolExpr& e) :
  d_expr(e) {
}

void QueryCommand::invoke(CVC4::SmtEngine* smt_engine) {
  smt_engine->query(d_expr);
}

CommandSequence::CommandSequence() :
  d_last_index(0) {
}

CommandSequence::~CommandSequence() {
  for(unsigned i = d_last_index; i < d_command_sequence.size(); ++i)
    delete d_command_sequence[i];
}

void CommandSequence::invoke(SmtEngine* smt_engine) {
  for(; d_last_index < d_command_sequence.size(); ++d_last_index) {
    d_command_sequence[d_last_index]->invoke(smt_engine);
    delete d_command_sequence[d_last_index];
  }
}

void CommandSequence::addCommand(Command* cmd) {
  d_command_sequence.push_back(cmd);
}

void EmptyCommand::toString(ostream& out) const {
  out << "EmptyCommand(" << d_name << ")";
}

void AssertCommand::toString(ostream& out) const {
  out << "Assert(" << d_expr << ")";
}

void CheckSatCommand::toString(ostream& out) const {
  if(d_expr.isNull())
    out << "CheckSat()";
  else
    out << "CheckSat(" << d_expr << ")";
}

void QueryCommand::toString(ostream& out) const {
  out << "Query(" << d_expr << ")";
}

void CommandSequence::toString(ostream& out) const {
  out << "CommandSequence[" << endl;
  for(unsigned i = d_last_index; i < d_command_sequence.size(); ++i) {
    out << *d_command_sequence[i] << endl;
  }
  out << "]";
}

}/* CVC4 namespace */
