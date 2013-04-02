/*********************                                                        */
/*! \file sexpr.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
#include "util/cvc4_assert.h"
#include "printer/printer.h"
#include "expr/expr.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const SExpr& sexpr) {
  Printer::getPrinter(Expr::setlanguage::getLanguage(out))->toStream(out, sexpr);
  return out;
}

}/* CVC4 namespace */
