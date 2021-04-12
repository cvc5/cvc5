/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * List of instantiations.
 */

#include "theory/quantifiers/instantiation_list.h"

#include "options/base_options.h"
#include "printer/printer.h"

namespace cvc5 {

std::ostream& operator<<(std::ostream& out, const InstantiationList& ilist)
{
  Printer::getPrinter(options::outputLanguage())->toStream(out, ilist);
  return out;
}

std::ostream& operator<<(std::ostream& out, const SkolemList& skl)
{
  Printer::getPrinter(options::outputLanguage())->toStream(out, skl);
  return out;
}

}  // namespace cvc5
