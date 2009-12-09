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

#include <iostream>

#include "cvc4_config.h"
#include "expr/expr.h"

namespace CVC4 {
  class SmtEngine;
  class Command;
  class Expr;
}/* CVC4 namespace */

namespace CVC4 {

std::ostream& operator<<(std::ostream&, const Command&) CVC4_PUBLIC;

class CVC4_PUBLIC Command {
public:
  virtual void invoke(CVC4::SmtEngine* smt_engine) = 0;
  virtual ~Command() {};
  virtual void toString(std::ostream&) const = 0;
};/* class Command */

class CVC4_PUBLIC EmptyCommand : public Command {
public:
  EmptyCommand(std::string name = "");
  void invoke(CVC4::SmtEngine* smt_engine);
  void toString(std::ostream& out) const;
private:
  std::string d_name;
};/* class EmptyCommand */


class CVC4_PUBLIC AssertCommand : public Command {
protected:
  Expr d_expr;
public:
  AssertCommand(const Expr& e);
  void invoke(CVC4::SmtEngine* smt_engine);
  void toString(std::ostream& out) const;
};/* class AssertCommand */


class CVC4_PUBLIC CheckSatCommand : public Command {
public:
  CheckSatCommand();
  CheckSatCommand(const Expr& e);
  void invoke(SmtEngine* smt);
  void toString(std::ostream& out) const;
protected:
  Expr d_expr;
};/* class CheckSatCommand */


class CVC4_PUBLIC QueryCommand : public Command {
public:
  QueryCommand(const Expr& e);
  void invoke(SmtEngine* smt);
  void toString(std::ostream& out) const;
protected:
  Expr d_expr;
};/* class QueryCommand */


class CVC4_PUBLIC CommandSequence : public Command {
public:
  CommandSequence();
  ~CommandSequence();
  void invoke(SmtEngine* smt);
  void addCommand(Command* cmd);
  void toString(std::ostream& out) const;
private:
  /** All the commands to be executed (in sequence) */
  std::vector<Command*> d_command_sequence;
  /** Next command to be executed */
  unsigned int d_last_index;
};/* class CommandSequence */

}/* CVC4 namespace */

#endif /* __CVC4__COMMAND_H */
