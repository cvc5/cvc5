/*********************                                                        */
/*! \file sexpr.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Simple representation of S-expressions
 **
 ** Simple representation of S-expressions.
 **/

#include <iostream>
#include <vector>

#include "util/sexpr.h"
#include "util/Assert.h"
#include "printer/printer.h"
#include "expr/expr.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const SExpr& sexpr) {
  Printer::getPrinter(Expr::setlanguage::getLanguage(out))->toStream(out, sexpr);
  return out;
}

}/* CVC4 namespace */
