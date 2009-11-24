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

namespace CVC4 {

class SmtEngine;

class Command {
  SmtEngine* d_smt;

public:
  Command(CVC4::SmtEngine* smt) : d_smt(smt) {}
  virtual void invoke() = 0;
};

class AssertCommand : public Command {
public:
  AssertCommand(const Expr&);
  void invoke() { }
};

class CheckSatCommand : public Command {
public:
  CheckSatCommand(void);
  CheckSatCommand(const Expr&);
  void invoke() { }
};

class QueryCommand : public Command {
public:
  QueryCommand(const Expr&);
  void invoke() { }
};


}/* CVC4 namespace */

#endif /* __CVC4__COMMAND_H */
