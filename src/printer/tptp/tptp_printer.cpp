/*********************                                                        */
/*! \file tptp_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The pretty-printer interface for the TPTP output language
 **
 ** The pretty-printer interface for the TPTP output language.
 **/
#include "printer/tptp/tptp_printer.h"

#include <iostream>
#include <string>
#include <typeinfo>
#include <vector>

#include "expr/expr.h" // for ExprSetDepth etc..
#include "expr/node_manager.h" // for VarNameAttr
#include "options/language.h" // for LANG_AST
#include "smt/command.h"

using namespace std;

namespace CVC4 {
namespace printer {
namespace tptp {

void TptpPrinter::toStream(std::ostream& out, TNode n,
                           int toDepth, bool types, size_t dag) const throw() {
  n.toStream(out, toDepth, types, dag, language::output::LANG_SMTLIB_V2_5);
}/* TptpPrinter::toStream() */

void TptpPrinter::toStream(std::ostream& out, const Command* c,
                           int toDepth, bool types, size_t dag) const throw() {
  c->toStream(out, toDepth, types, dag, language::output::LANG_SMTLIB_V2_5);
}/* TptpPrinter::toStream() */

void TptpPrinter::toStream(std::ostream& out, const CommandStatus* s) const throw() {
  s->toStream(out, language::output::LANG_SMTLIB_V2_5);
}/* TptpPrinter::toStream() */


void TptpPrinter::toStream(std::ostream& out, const Model& m) const throw() {
  out << "% SZS output start FiniteModel for " << m.getInputName() << endl;
  for(size_t i = 0; i < m.getNumCommands(); ++i) {
    this->Printer::toStreamUsing(language::output::LANG_SMTLIB_V2_5, out, m, m.getCommand(i));
  }
  out << "% SZS output end FiniteModel for " << m.getInputName() << endl;
}

void TptpPrinter::toStream(std::ostream& out, const Model& m, const Command* c) const throw() {
  // shouldn't be called; only the non-Command* version above should be
  Unreachable();
}


}/* CVC4::printer::tptp namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */
