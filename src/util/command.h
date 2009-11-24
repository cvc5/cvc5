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

namespace CVC4 {

class Command { 
   // distinct from Exprs
};

class AssertCommand : public Command {
  AssertCommand(const Expr&);
};

class CheckSatCommand : public Command {
  CheckSatCommand(void);
  CheckSatCommand(const Expr&);
};

class QueryCommand : public Command {
  QueryCommand(const Expr&);
};


}/* CVC4 namespace */

#endif /* __CVC4__COMMAND_H */
