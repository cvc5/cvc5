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
#include "smt/smt_engine.h"

namespace CVC4 {

class Command {
protected:
  SmtEngine* d_smt;

public:
  Command(CVC4::SmtEngine* smt) : d_smt(smt) {}
  SmtEngine* getSmtEngine() { return d_smt; }
  virtual void invoke() = 0;
};

class AssertCommand : public Command {
protected:
  Expr d_expr;

public:
  AssertCommand(CVC4::SmtEngine* smt, const Expr& e) : Command(smt), d_expr(e) {}
  void invoke() { d_smt->assert(d_expr); }
};

class CheckSatCommand : public Command {
protected:
  Expr d_expr;

public:
  CheckSatCommand(CVC4::SmtEngine* smt) : Command(smt), d_expr(Expr::null()) {}
  CheckSatCommand(CVC4::SmtEngine* smt, const Expr& e) : Command(smt), d_expr(e) {}
  void invoke() { d_smt->checkSat(d_expr); }
};

class QueryCommand : public Command {
protected:
  Expr d_expr;

public:
  QueryCommand(CVC4::SmtEngine* smt, const Expr& e) : Command(smt), d_expr(e) {}
  void invoke() { d_smt->query(d_expr); }
};

}/* CVC4 namespace */

#endif /* __CVC4__COMMAND_H */
