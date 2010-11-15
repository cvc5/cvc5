/*********************                                                        */
/*! \file cvc_printer.cpp
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
 ** \brief The pretty-printer interface for the CVC output language
 **
 ** The pretty-printer interface for the CVC output language.
 **/

#include "printer/cvc/cvc_printer.h"

#include <iostream>

using namespace std;

namespace CVC4 {
namespace printer {
namespace cvc {

std::ostream& CvcPrinter::toStream(std::ostream& out, TNode n,
                                   int toDepth, bool types) const {
  return out;
}/* CvcPrinter::toStream() */

}/* CVC4::printer::cvc namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

