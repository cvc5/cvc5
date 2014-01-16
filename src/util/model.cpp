/*********************                                                        */
/*! \file model.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief implementation of Model class
 **/

#include "util/model.h"
#include "expr/command.h"
#include "smt/smt_engine_scope.h"
#include "smt/command_list.h"
#include "printer/printer.h"

#include <vector>

using namespace std;

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const Model& m) {
  smt::SmtScope smts(&m.d_smt);
  Expr::dag::Scope scope(out, false);
  Printer::getPrinter(options::outputLanguage())->toStream(out, m);
  return out;
}

Model::Model() :
  d_smt(*smt::currentSmtEngine()) {
}

size_t Model::getNumCommands() const {
  return d_smt.d_modelCommands->size() + d_smt.d_modelGlobalCommands.size();
}

const Command* Model::getCommand(size_t i) const {
  Assert(i < getNumCommands());
  // index the global commands first, then the locals
  if(i < d_smt.d_modelGlobalCommands.size()) {
    return d_smt.d_modelGlobalCommands[i];
  } else {
    return (*d_smt.d_modelCommands)[i - d_smt.d_modelGlobalCommands.size()];
  }
}

}/* CVC4 namespace */
