/*********************                                                        */
/*! \file unsat_core.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Representation of unsat cores
 **
 ** Representation of unsat cores.
 **/

#include "util/unsat_core.h"
#include "expr/command.h"
#include "smt/smt_engine_scope.h"
#include "printer/printer.h"

namespace CVC4 {

void UnsatCore::initMessage() const {
  Debug("core") << "UnsatCore size " << d_core.size() << std::endl;
}

UnsatCore::const_iterator UnsatCore::begin() const {
  return d_core.begin();
}

UnsatCore::const_iterator UnsatCore::end() const {
  return d_core.end();
}

void UnsatCore::toStream(std::ostream& out) const {
  smt::SmtScope smts(d_smt);
  Expr::dag::Scope scope(out, false);
  Printer::getPrinter(options::outputLanguage())->toStream(out, *this);
}

void UnsatCore::toStream(std::ostream& out, const std::map<Expr, std::string>& names) const {
  smt::SmtScope smts(d_smt);
  Expr::dag::Scope scope(out, false);
  Printer::getPrinter(options::outputLanguage())->toStream(out, *this, names);
}

std::ostream& operator<<(std::ostream& out, const UnsatCore& core) {
  core.toStream(out);
  return out;
}

}/* CVC4 namespace */
