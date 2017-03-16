/*********************                                                        */
/*! \file printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base of the pretty-printer interface
 **
 ** Base of the pretty-printer interface.
 **/
#include "printer/printer.h"

#include <string>

#include "options/base_options.h"
#include "options/language.h"
#include "printer/ast/ast_printer.h"
#include "printer/cvc/cvc_printer.h"
#include "printer/smt1/smt1_printer.h"
#include "printer/smt2/smt2_printer.h"
#include "printer/tptp/tptp_printer.h"

using namespace std;

namespace CVC4 {

Printer* Printer::d_printers[language::output::LANG_MAX];

Printer* Printer::makePrinter(OutputLanguage lang) throw() {
  using namespace CVC4::language::output;

  switch(lang) {
  case LANG_SMTLIB_V1: // TODO the printer
    return new printer::smt1::Smt1Printer();

  case LANG_SMTLIB_V2_0:
    return new printer::smt2::Smt2Printer(printer::smt2::smt2_0_variant);

  case LANG_SMTLIB_V2_5:
    return new printer::smt2::Smt2Printer();
    
  case LANG_SMTLIB_V2_6:
    return new printer::smt2::Smt2Printer(printer::smt2::smt2_6_variant);

  case LANG_TPTP:
    return new printer::tptp::TptpPrinter();

  case LANG_CVC4:
    return new printer::cvc::CvcPrinter();

  case LANG_Z3STR:
    return new printer::smt2::Smt2Printer(printer::smt2::z3str_variant);

  case LANG_SYGUS:
    return new printer::smt2::Smt2Printer(printer::smt2::sygus_variant);

  case LANG_AST:
    return new printer::ast::AstPrinter();

  case LANG_CVC3:
    return new printer::cvc::CvcPrinter(/* cvc3-mode = */ true);

  default:
    Unhandled(lang);
  }
}/* Printer::makePrinter() */



void Printer::toStream(std::ostream& out, const Model& m) const throw() {
  for(size_t i = 0; i < m.getNumCommands(); ++i) {
    const Command* cmd = m.getCommand(i);
    const DeclareFunctionCommand* dfc = dynamic_cast<const DeclareFunctionCommand*>(cmd);
    if (dfc != NULL && m.isDontCare(dfc->getFunction())) {
      continue;
    }
    toStream(out, m, cmd);
  }
}/* Printer::toStream(Model) */

void Printer::toStream(std::ostream& out, const UnsatCore& core) const throw() {
  std::map<Expr, std::string> names;
  toStream(out, core, names);
}/* Printer::toStream(UnsatCore) */

void Printer::toStream(std::ostream& out, const UnsatCore& core, const std::map<Expr, std::string>& names) const throw() {
  for(UnsatCore::iterator i = core.begin(); i != core.end(); ++i) {
    AssertCommand cmd(*i);
    toStream(out, &cmd, -1, false, -1);
    out << std::endl;
  }
}/* Printer::toStream(UnsatCore, std::map<Expr, std::string>) */

Printer* Printer::getPrinter(OutputLanguage lang) throw() {
  if(lang == language::output::LANG_AUTO) {
  // Infer the language to use for output.
  //
  // Options can be null in certain circumstances (e.g., when printing
  // the singleton "null" expr.  So we guard against segfault
  if(not Options::isCurrentNull()) {
    if(options::outputLanguage.wasSetByUser()) {
      lang = options::outputLanguage();
    }
    if(lang == language::output::LANG_AUTO && options::inputLanguage.wasSetByUser()) {
      lang = language::toOutputLanguage(options::inputLanguage());
     }
   }
   if(lang == language::output::LANG_AUTO) {
      lang = language::output::LANG_CVC4; // default
    }
  }
  if(d_printers[lang] == NULL) {
    d_printers[lang] = makePrinter(lang);
  }
  return d_printers[lang];
}


}/* CVC4 namespace */
