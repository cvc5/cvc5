/*********************                                                        */
/*! \file printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Aina Niemetz, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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
#include "printer/smt2/smt2_printer.h"
#include "printer/tptp/tptp_printer.h"

using namespace std;

namespace CVC4 {

unique_ptr<Printer> Printer::d_printers[language::output::LANG_MAX];

unique_ptr<Printer> Printer::makePrinter(OutputLanguage lang)
{
  using namespace CVC4::language::output;

  switch(lang) {
  case LANG_SMTLIB_V2_0:
    return unique_ptr<Printer>(
        new printer::smt2::Smt2Printer(printer::smt2::smt2_0_variant));

  case LANG_SMTLIB_V2_5:
    return unique_ptr<Printer>(new printer::smt2::Smt2Printer());

  case LANG_SMTLIB_V2_6:
    return unique_ptr<Printer>(
        new printer::smt2::Smt2Printer(printer::smt2::smt2_6_variant));

  case LANG_TPTP:
    return unique_ptr<Printer>(new printer::tptp::TptpPrinter());

  case LANG_CVC4:
    return unique_ptr<Printer>(new printer::cvc::CvcPrinter());

  case LANG_Z3STR:
    return unique_ptr<Printer>(
        new printer::smt2::Smt2Printer(printer::smt2::z3str_variant));

  case LANG_SYGUS_V1:
    return unique_ptr<Printer>(
        new printer::smt2::Smt2Printer(printer::smt2::sygus_variant));

  case LANG_SYGUS_V2:
    // sygus version 2.0 does not have discrepancies with smt2, hence we use
    // a normal smt2 variant here.
    return unique_ptr<Printer>(
        new printer::smt2::Smt2Printer(printer::smt2::smt2_6_variant));

  case LANG_AST:
    return unique_ptr<Printer>(new printer::ast::AstPrinter());

  case LANG_CVC3:
    return unique_ptr<Printer>(
        new printer::cvc::CvcPrinter(/* cvc3-mode = */ true));

  default: Unhandled() << lang;
  }
}

void Printer::toStreamSygus(std::ostream& out, TNode n) const
{
  // no sygus-specific printing associated with this printer,
  // just print the original term, without letification (the fifth argument is
  // set to 0).
  toStream(out, n, -1, false, 0);
}

void Printer::toStream(std::ostream& out, const Model& m) const
{
  for(size_t i = 0; i < m.getNumCommands(); ++i) {
    const Command* cmd = m.getCommand(i);
    const DeclareFunctionCommand* dfc = dynamic_cast<const DeclareFunctionCommand*>(cmd);
    if (dfc != NULL && !m.isModelCoreSymbol(dfc->getFunction()))
    {
      continue;
    }
    toStream(out, m, cmd);
  }
}/* Printer::toStream(Model) */

void Printer::toStream(std::ostream& out, const UnsatCore& core) const
{
  for(UnsatCore::iterator i = core.begin(); i != core.end(); ++i) {
    AssertCommand cmd(*i);
    toStream(out, &cmd, -1, false, -1);
    out << std::endl;
  }
}/* Printer::toStream(UnsatCore) */

Printer* Printer::getPrinter(OutputLanguage lang)
{
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
   if (lang == language::output::LANG_AUTO)
   {
     lang = language::output::LANG_SMTLIB_V2_6;  // default
   }
  }
  if(d_printers[lang] == NULL) {
    d_printers[lang] = makePrinter(lang);
  }
  return d_printers[lang].get();
}


}/* CVC4 namespace */
