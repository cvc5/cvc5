/*
 * command.cpp
 *
 *  Created on: Nov 25, 2009
 *      Author: dejan
 */

#include "command.h"

using namespace CVC4;

void EmptyCommand::invoke(SmtEngine* smt_engine) { }

AssertCommand::AssertCommand(const Expr& e) :
  d_expr(e)
{
}

void AssertCommand::invoke(SmtEngine* smt_engine)
{
  smt_engine->assert(d_expr);
}

CheckSatCommand::CheckSatCommand()
{
}

CheckSatCommand::CheckSatCommand(const Expr& e) :
  d_expr(e)
{
}

void CheckSatCommand::invoke(SmtEngine* smt_engine)
{
  smt_engine->checkSat(d_expr);
}

QueryCommand::QueryCommand(const Expr& e) :
  d_expr(e)
{
}

void QueryCommand::invoke(CVC4::SmtEngine* smt_engine)
{
  smt_engine->query(d_expr);
}

CommandSequence::CommandSequence() :
  d_last_index(0)
{
}

CommandSequence::CommandSequence(Command* cmd) :
  d_last_index(0)
{
  addCommand(cmd);
}


CommandSequence::~CommandSequence()
{
  for (unsigned i = d_last_index; i < d_command_sequence.size(); i++)
    delete d_command_sequence[i];
}

void CommandSequence::invoke(SmtEngine* smt_engine)
{
  for (; d_last_index < d_command_sequence.size(); d_last_index++) {
    d_command_sequence[d_last_index]->invoke(smt_engine);
    delete d_command_sequence[d_last_index];
  }
}

void CommandSequence::addCommand(Command* cmd)
{
  d_command_sequence.push_back(cmd);
}
