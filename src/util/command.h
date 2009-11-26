/*********************                                           -*- C++ -*-  */
/** command.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#ifndef __CVC4__COMMAND_H
#define __CVC4__COMMAND_H

#include "expr/expr.h"

namespace CVC4
{

class SmtEngine;

class Command
{
  public:
    virtual void invoke(CVC4::SmtEngine* smt_engine) = 0;
    virtual ~Command() {}
};

class AssertCommand: public Command
{
  public:
    AssertCommand(const Expr& e);
    void invoke(CVC4::SmtEngine* smt_engine);
  protected:
    Expr d_expr;
};

class CheckSatCommand: public Command
{
  public:
    CheckSatCommand();
    CheckSatCommand(const Expr& e);
    void invoke(CVC4::SmtEngine* smt);
  protected:
    Expr d_expr;
};

class QueryCommand: public Command
{
  public:
    QueryCommand(const Expr& e);
    void invoke(CVC4::SmtEngine* smt);
  protected:
    Expr d_expr;
};

}/* CVC4 namespace */

#endif /* __CVC4__COMMAND_H */
