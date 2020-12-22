/*********************                                                        */
/*! \file instantiation_list.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief list of instantiations
 **/

#include "theory/quantifiers/instantiation_list.h"

#include "printer/printer.h"
#include "options/base_options.h"

namespace CVC4 {

/** Print the unsat core to stream out */
std::ostream& operator<<(std::ostream& out, const InstantiationList& ilist)
{
  Printer::getPrinter(options::outputLanguage())->toStream(out, ilist);
  return out;
}

} /* CVC4 namespace */
