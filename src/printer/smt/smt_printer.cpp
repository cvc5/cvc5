/*********************                                                        */
/*! \file smt_printer.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The pretty-printer interface for the SMT output language
 **
 ** The pretty-printer interface for the SMT output language.
 **/

#include "printer/smt/smt_printer.h"
#include "util/language.h"

#include <iostream>

using namespace std;

namespace CVC4 {
namespace printer {
namespace smt {

void SmtPrinter::toStream(std::ostream& out, TNode n,
                          int toDepth, bool types) const {
  n.toStream(out, toDepth, types, language::output::LANG_SMTLIB_V2);
}/* SmtPrinter::toStream() */

}/* CVC4::printer::smt namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

