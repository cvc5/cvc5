/*********************                                                        */
/*! \file model.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief implementation of Model class
 **/

#include "smt/model.h"

#include <vector>

#include "expr/expr_iomanip.h"
#include "options/base_options.h"
#include "printer/printer.h"
#include "smt/dump_manager.h"
#include "smt/node_command.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"

using namespace std;

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const Model& m) {
  smt::SmtScope smts(&m.d_smt);
  expr::ExprDag::Scope scope(out, false);
  Printer::getPrinter(options::outputLanguage())->toStream(out, m);
  return out;
}

Model::Model() : d_smt(*smt::currentSmtEngine()), d_isKnownSat(false) {}

size_t Model::getNumCommands() const
{
  return d_smt.getDumpManager()->getNumModelCommands();
}

const NodeCommand* Model::getCommand(size_t i) const
{
  return d_smt.getDumpManager()->getModelCommand(i);
}

}/* CVC4 namespace */
