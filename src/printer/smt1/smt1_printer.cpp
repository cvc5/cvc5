/*********************                                                        */
/*! \file smt1_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The pretty-printer interface for the SMT output language
 **
 ** The pretty-printer interface for the SMT output language.
 **/
#include "printer/smt1/smt1_printer.h"

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
namespace smt1 {

void Smt1Printer::toStream(std::ostream& out, TNode n,
                           int toDepth, bool types, size_t dag) const throw() {
  n.toStream(out, toDepth, types, dag, language::output::LANG_SMTLIB_V2_5);
}/* Smt1Printer::toStream() */

void Smt1Printer::toStream(std::ostream& out, const Command* c,
                           int toDepth, bool types, size_t dag) const throw() {
  c->toStream(out, toDepth, types, dag, language::output::LANG_SMTLIB_V2_5);
}/* Smt1Printer::toStream() */

void Smt1Printer::toStream(std::ostream& out, const CommandStatus* s) const throw() {
  s->toStream(out, language::output::LANG_SMTLIB_V2_5);
}/* Smt1Printer::toStream() */


void Smt1Printer::toStream(std::ostream& out, const Model& m) const throw() {
  Printer::getPrinter(language::output::LANG_SMTLIB_V2_5)->toStream(out, m);
}

void Smt1Printer::toStream(std::ostream& out, const Model& m, const Command* c) const throw() {
  // shouldn't be called; only the non-Command* version above should be
  Unreachable();
}

}/* CVC4::printer::smt1 namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */
