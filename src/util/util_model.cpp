/*********************                                                        */
/*! \file model.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief implementation of Model class
 **/

#include "util/util_model.h"
#include "expr/command.h"
#include "smt/smt_engine_scope.h"
#include "smt/command_list.h"

#include <vector>

using namespace std;

namespace CVC4 {

Model::Model() :
  d_smt(*smt::currentSmtEngine()) {
}

size_t Model::getNumCommands() const {
  return d_smt.d_modelCommands->size();
}

const Command* Model::getCommand(size_t i) const {
  return (*d_smt.d_modelCommands)[i];
}

}/* CVC4 namespace */
