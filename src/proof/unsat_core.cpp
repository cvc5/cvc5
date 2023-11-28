/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Representation of unsat cores.
 */

#include "proof/unsat_core.h"

#include "base/check.h"
#include "expr/node.h"
#include "options/base_options.h"
#include "options/io_utils.h"
#include "printer/printer.h"

namespace cvc5::internal {

UnsatCore::UnsatCore(const std::vector<Node>& core)
    : d_useNames(false), d_core(core), d_names()
{
  Trace("core") << "UnsatCore size " << d_core.size() << std::endl;
}

UnsatCore::UnsatCore(std::vector<std::string>& names)
    : d_useNames(true), d_core(), d_names(names)
{
  Trace("core") << "UnsatCore (names) size " << d_names.size() << std::endl;
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
  options::ioutils::Scope scope(out);
  options::ioutils::applyDagThresh(out, 0);
  Printer::getPrinter(out)->toStream(out, *this);
}

std::ostream& operator<<(std::ostream& out, const UnsatCore& core) {
  core.toStream(out);
  return out;
}

}  // namespace cvc5::internal
