/*********************                                                        */
/*! \file unsat_core.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Clark Barrett, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Representation of unsat cores
 **
 ** Representation of unsat cores.
 **/

#include "proof/unsat_core.h"

#include "base/check.h"
#include "expr/expr_iomanip.h"
#include "options/base_options.h"
#include "printer/printer.h"
#include "smt/smt_engine_scope.h"

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
  Assert(d_smt != NULL);
  smt::SmtScope smts(d_smt);
  expr::ExprDag::Scope scope(out, false);
  Printer::getPrinter(options::outputLanguage())->toStream(out, *this);
}

std::ostream& operator<<(std::ostream& out, const UnsatCore& core) {
  core.toStream(out);
  return out;
}

}/* CVC4 namespace */
