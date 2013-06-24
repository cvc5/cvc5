/*********************                                                        */
/*! \file tptp_printer.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The pretty-printer interface for the TPTP output language
 **
 ** The pretty-printer interface for the TPTP output language.
 **/

#include "printer/tptp/tptp_printer.h"
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
namespace tptp {

void TptpPrinter::toStream(std::ostream& out, TNode n,
                           int toDepth, bool types, size_t dag) const throw() {
  n.toStream(out, toDepth, types, dag, language::output::LANG_SMTLIB_V2);
}/* TptpPrinter::toStream() */

void TptpPrinter::toStream(std::ostream& out, const Command* c,
                           int toDepth, bool types, size_t dag) const throw() {
  c->toStream(out, toDepth, types, dag, language::output::LANG_SMTLIB_V2);
}/* TptpPrinter::toStream() */

void TptpPrinter::toStream(std::ostream& out, const CommandStatus* s) const throw() {
  s->toStream(out, language::output::LANG_SMTLIB_V2);
}/* TptpPrinter::toStream() */

void TptpPrinter::toStream(std::ostream& out, const SExpr& sexpr) const throw() {
  Printer::getPrinter(language::output::LANG_SMTLIB_V2)->toStream(out, sexpr);
}/* TptpPrinter::toStream() */

void TptpPrinter::toStream(std::ostream& out, const Model& m) const throw() {
  out << "% SZS output start FiniteModel for " << m.getInputName() << endl;
  for(size_t i = 0; i < m.getNumCommands(); ++i) {
    this->Printer::toStreamUsing(language::output::LANG_SMTLIB_V2, out, m, m.getCommand(i));
  }
  out << "% SZS output end FiniteModel for " << m.getInputName() << endl;
}

void TptpPrinter::toStream(std::ostream& out, const Model& m, const Command* c) const throw() {
  // shouldn't be called; only the non-Command* version above should be
  Unreachable();
}

void TptpPrinter::toStream(std::ostream& out, const Result& r) const throw() {
  out << "% SZS status ";
  if(r.isSat() == Result::SAT) {
    out << "Satisfiable";
  } else if(r.isSat() == Result::UNSAT) {
    out << "Unsatisfiable";
  } else if(r.isValid() == Result::VALID) {
    out << "Theorem";
  } else if(r.isValid() == Result::INVALID) {
    out << "CounterSatisfiable";
  } else {
    out << "GaveUp";
  }
  out << " for " << r.getInputName();
}

}/* CVC4::printer::tptp namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */
