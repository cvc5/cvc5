/*
 * command.cpp
 *
 *  Created on: Nov 25, 2009
 *      Author: dejan
 */

#include "util/command.h"
#include "smt/smt_engine.h"
#include "util/result.h"

namespace CVC4 {

EmptyCommand::EmptyCommand() {
}

Result EmptyCommand::invoke(SmtEngine* smt_engine) {
  return Result::VALIDITY_UNKNOWN;
}

AssertCommand::AssertCommand(const Expr& e) :
  d_expr(e) {
}

Result AssertCommand::invoke(SmtEngine* smt_engine) {
  return smt_engine->assert(d_expr);
}

CheckSatCommand::CheckSatCommand() :
  d_expr(Expr::null()) {
}

CheckSatCommand::CheckSatCommand(const Expr& e) :
  d_expr(e) {
}

Result CheckSatCommand::invoke(SmtEngine* smt_engine) {
  return smt_engine->checkSat(d_expr);
}

QueryCommand::QueryCommand(const Expr& e) :
  d_expr(e) {
}

Result QueryCommand::invoke(CVC4::SmtEngine* smt_engine) {
  return smt_engine->query(d_expr);
}

CommandSequence::CommandSequence() :
  d_last_index(0) {
}

CommandSequence::CommandSequence(Command* cmd) :
  d_last_index(0) {
  addCommand(cmd);
}


CommandSequence::~CommandSequence() {
  for(unsigned i = d_last_index; i < d_command_sequence.size(); ++i)
    delete d_command_sequence[i];
}

Result CommandSequence::invoke(SmtEngine* smt_engine) {
  Result r = Result::VALIDITY_UNKNOWN;
  for(; d_last_index < d_command_sequence.size(); ++d_last_index) {
    r = d_command_sequence[d_last_index]->invoke(smt_engine);
    delete d_command_sequence[d_last_index];
  }
  return r;
}

void CommandSequence::addCommand(Command* cmd) {
  d_command_sequence.push_back(cmd);
}

}/* CVC4 namespace */
