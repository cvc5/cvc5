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
#include "util/result.h"

namespace CVC4 {
  class SmtEngine;
  class Command;
  class Expr;
}/* CVC4 namespace */

namespace std {
inline std::ostream& operator<<(std::ostream&, const CVC4::Command*) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream&, CVC4::Expr) CVC4_PUBLIC;
}

namespace CVC4 {

class CVC4_PUBLIC Command {
public:
  virtual Result invoke(CVC4::SmtEngine* smt_engine) = 0;
  virtual ~Command() {};
  virtual void toString(std::ostream&) const = 0;
};/* class Command */

class CVC4_PUBLIC EmptyCommand : public Command {
public:
  EmptyCommand();
  Result invoke(CVC4::SmtEngine* smt_engine);
  void toString(std::ostream& out) const { out << "EmptyCommand"; }
};/* class EmptyCommand */


class CVC4_PUBLIC AssertCommand : public Command {
protected:
  Expr d_expr;
public:
  AssertCommand(const Expr& e);
  Result invoke(CVC4::SmtEngine* smt_engine);
  void toString(std::ostream& out) const { out << "Assert(" << d_expr << ")"; }
};/* class AssertCommand */


class CVC4_PUBLIC CheckSatCommand : public Command {
public:
  CheckSatCommand();
  CheckSatCommand(const Expr& e);
  Result invoke(SmtEngine* smt);
  void toString(std::ostream& out) const { out << "CheckSat(" << d_expr << ")"; }
protected:
  Expr d_expr;
};/* class CheckSatCommand */


class CVC4_PUBLIC QueryCommand : public Command {
public:
  QueryCommand(const Expr& e);
  Result invoke(SmtEngine* smt);
  void toString(std::ostream& out) const { out << "Query(" << d_expr << ")"; }
protected:
  Expr d_expr;
};/* class QueryCommand */


class CVC4_PUBLIC CommandSequence : public Command {
public:
  CommandSequence();
  CommandSequence(Command* cmd);
  ~CommandSequence();
  Result invoke(SmtEngine* smt);
  void addCommand(Command* cmd);
  void toString(std::ostream& out) const {
    out << "CommandSequence(";
    for(std::vector<Command*>::const_iterator i = d_command_sequence.begin();
        i != d_command_sequence.end();
        ++i) {
      out << *i;
      if(i != d_command_sequence.end())
        out << " ; ";
    }
    out << ")";
  }
private:
  /** All the commands to be executed (in sequence) */
  std::vector<Command*> d_command_sequence;
  /** Next command to be executed */
  unsigned int d_last_index;
};/* class CommandSequence */

}/* CVC4 namespace */

inline std::ostream& std::operator<<(std::ostream& out, const CVC4::Command* c) {
  if(c)
    c->toString(out);
  else out << "(null)";
  return out;
}

#endif /* __CVC4__COMMAND_H */
