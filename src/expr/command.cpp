/*********************                                                        */
/** command.cpp
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Implementation of command objects.
 **/

#include "expr/command.h"
#include "smt/smt_engine.h"

using namespace std;

namespace CVC4 {

ostream& operator<<(ostream& out, const Command* command) {
  if (command == NULL) {
    out << "null";
  } else {
    command->toStream(out);
  }
  return out;
}

CommandSequence::~CommandSequence() {
  for(unsigned i = d_index; i < d_commandSequence.size(); ++i) {
    delete d_commandSequence[i];
  }
}

void CommandSequence::invoke(SmtEngine* smtEngine) {
  for(; d_index < d_commandSequence.size(); ++d_index) {
    d_commandSequence[d_index]->invoke(smtEngine);
    delete d_commandSequence[d_index];
  }
}

void CheckSatCommand::toStream(ostream& out) const {
  if(d_expr.isNull()) {
    out << "CheckSat()";
  } else {
    out << "CheckSat(" << d_expr << ")";
  }
}

void CommandSequence::toStream(ostream& out) const {
  out << "CommandSequence[" << endl;
  for(unsigned i = d_index; i < d_commandSequence.size(); ++i) {
    out << *d_commandSequence[i] << endl;
  }
  out << "]";
}

void DeclarationCommand::toStream(std::ostream& out) const {
  out << "Declare(";
  bool first = true;
  for(unsigned i = 0; i < d_declaredSymbols.size(); ++i) {
    if(!first) {
      out << ", ";
    }
    out << d_declaredSymbols[i];
    first = false;
  }
  out << ")";
}

void PushCommand::invoke(SmtEngine* smtEngine) {
  smtEngine->push();
}

void PushCommand::toStream(ostream& out) const {
  out << "Push()";
}

void PopCommand::invoke(SmtEngine* smtEngine) {
  smtEngine->pop();
}

void PopCommand::toStream(ostream& out) const {
  out << "Pop()";
}

}/* CVC4 namespace */
