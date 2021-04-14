/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andrew Reynolds, Clark Barrett
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Representation of unsat cores.
 */

#include "proof/unsat_core.h"

#include "base/check.h"
#include "expr/expr_iomanip.h"
#include "options/base_options.h"
#include "printer/printer.h"
#include "smt/smt_engine_scope.h"

namespace cvc5 {

UnsatCore::UnsatCore(const std::vector<Node>& core)
    : d_useNames(false), d_core(core), d_names()
{
  Debug("core") << "UnsatCore size " << d_core.size() << std::endl;
}

UnsatCore::UnsatCore(std::vector<std::string>& names)
    : d_useNames(true), d_core(), d_names(names)
{
  Debug("core") << "UnsatCore (names) size " << d_names.size() << std::endl;
}

const std::vector<Node>& UnsatCore::getCore() const { return d_core; }
const std::vector<std::string>& UnsatCore::getCoreNames() const
{
  return d_names;
}

UnsatCore::const_iterator UnsatCore::begin() const {
  return d_core.begin();
}

UnsatCore::const_iterator UnsatCore::end() const {
  return d_core.end();
}

void UnsatCore::toStream(std::ostream& out) const {
  expr::ExprDag::Scope scope(out, false);
  Printer::getPrinter(options::outputLanguage())->toStream(out, *this);
}

std::ostream& operator<<(std::ostream& out, const UnsatCore& core) {
  core.toStream(out);
  return out;
}

}  // namespace cvc5
