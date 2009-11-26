/*
 * command.cpp
 *
 *  Created on: Nov 25, 2009
 *      Author: dejan
 */

#include "command.h"

using namespace CVC4;

AssertCommand::AssertCommand(const Expr& e) :
  d_expr(e)
{
}

void AssertCommand::invoke(CVC4::SmtEngine* smt_engine)
{
  smt_engine->assert(d_expr);
}

CheckSatCommand::CheckSatCommand()
{
}

CheckSatCommand::CheckSatCommand(const Expr& e):
    d_expr(e)
{
}

void CheckSatCommand::invoke(CVC4::SmtEngine* smt_engine)
{
  smt_engine->checkSat(d_expr);
}

QueryCommand::QueryCommand(const Expr& e):
    d_expr(e)
{
}

void QueryCommand::invoke(CVC4::SmtEngine* smt_engine)
{
  smt_engine->query(d_expr);
}

