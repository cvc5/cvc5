/*********************                                                        */
/*! \file smt_printer.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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
#include "expr/expr.h" // for ExprSetDepth etc..
#include "util/language.h" // for LANG_AST
#include "expr/node_manager.h" // for VarNameAttr
#include "expr/command.h"

#include <iostream>
#include <vector>
#include <string>
#include <typeinfo>

using namespace std;

namespace CVC4 {
namespace printer {
namespace smt {

void SmtPrinter::toStream(std::ostream& out, TNode n,
                          int toDepth, bool types, size_t dag) const throw() {
  n.toStream(out, toDepth, types, dag, language::output::LANG_SMTLIB_V2);
}/* SmtPrinter::toStream() */

void SmtPrinter::toStream(std::ostream& out, const Command* c,
                          int toDepth, bool types, size_t dag) const throw() {
  c->toStream(out, toDepth, types, dag, language::output::LANG_SMTLIB_V2);
}/* SmtPrinter::toStream() */

void SmtPrinter::toStream(std::ostream& out, const CommandStatus* s) const throw() {
  s->toStream(out, language::output::LANG_SMTLIB_V2);
}/* SmtPrinter::toStream() */

void SmtPrinter::toStream(std::ostream& out, const SExpr& sexpr) const throw() {
  Printer::getPrinter(language::output::LANG_SMTLIB_V2)->toStream(out, sexpr);
}/* SmtPrinter::toStream() */

void SmtPrinter::toStream(std::ostream& out, Model* m, Command* c, int c_type ) const throw(){
  Printer::getPrinter(language::output::LANG_SMTLIB_V2)->toStream(out, m, c, c_type);
}

}/* CVC4::printer::smt namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

