/*********************                                                        */
/*! \file printer.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Francois Bobot, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Base of the pretty-printer interface
 **
 ** Base of the pretty-printer interface.
 **/

#include "printer/printer.h"

#include "util/language.h"

#include "printer/smt1/smt1_printer.h"
#include "printer/smt2/smt2_printer.h"
#include "printer/tptp/tptp_printer.h"
#include "printer/cvc/cvc_printer.h"
#include "printer/ast/ast_printer.h"

#include <string>

using namespace std;

namespace CVC4 {

Printer* Printer::d_printers[language::output::LANG_MAX];
const int PrettySExprs::s_iosIndex = std::ios_base::xalloc();

Printer* Printer::makePrinter(OutputLanguage lang) throw() {
  using namespace CVC4::language::output;

  switch(lang) {
  case LANG_SMTLIB_V1:
    return new printer::smt1::Smt1Printer();

  case LANG_SMTLIB_V2:
    return new printer::smt2::Smt2Printer();

  case LANG_TPTP:
    return new printer::tptp::TptpPrinter();

  case LANG_CVC4:
    return new printer::cvc::CvcPrinter();

  case LANG_AST:
    return new printer::ast::AstPrinter();

  default:
    Unhandled(lang);
  }
}/* Printer::makePrinter() */

void Printer::toStream(std::ostream& out, const Result& r) const throw() {
  if(r.getType() == Result::TYPE_SAT) {
    switch(r.isSat()) {
    case Result::UNSAT:
      out << "unsat";
      break;
    case Result::SAT:
      out << "sat";
      break;
    case Result::SAT_UNKNOWN:
      out << "unknown";
      if(r.whyUnknown() != Result::UNKNOWN_REASON) {
        out << " (" << r.whyUnknown() << ")";
      }
      break;
    }
  } else {
    switch(r.isValid()) {
    case Result::INVALID:
      out << "invalid";
      break;
    case Result::VALID:
      out << "valid";
      break;
    case Result::VALIDITY_UNKNOWN:
      out << "unknown";
      if(r.whyUnknown() != Result::UNKNOWN_REASON) {
        out << " (" << r.whyUnknown() << ")";
      }
      break;
    }
  }
}/* Printer::toStream() */

static void toStreamRec(std::ostream& out, const SExpr& sexpr, int indent) throw() {
  if(sexpr.isInteger()) {
    out << sexpr.getIntegerValue();
  } else if(sexpr.isRational()) {
    out << fixed << sexpr.getRationalValue().getDouble();
  } else if(sexpr.isKeyword()) {
    out << sexpr.getValue();
  } else if(sexpr.isString()) {
    string s = sexpr.getValue();
    // escape backslash and quote
    for(size_t i = 0; i < s.length(); ++i) {
      if(s[i] == '"') {
        s.replace(i, 1, "\\\"");
        ++i;
      } else if(s[i] == '\\') {
        s.replace(i, 1, "\\\\");
        ++i;
      }
    }
    out << "\"" << s << "\"";
  } else {
    const vector<SExpr>& kids = sexpr.getChildren();
    out << (indent > 0 && kids.size() > 1 ? "( " : "(");
    bool first = true;
    for(vector<SExpr>::const_iterator i = kids.begin(); i != kids.end(); ++i) {
      if(first) {
        first = false;
      } else {
        if(indent > 0) {
          out << "\n" << string(indent, ' ');
        } else {
          out << ' ';
        }
      }
      toStreamRec(out, *i, indent <= 0 || indent > 2 ? 0 : indent + 2);
    }
    if(indent > 0 && kids.size() > 1) {
      out << '\n';
      if(indent > 2) {
        out << string(indent - 2, ' ');
      }
    }
    out << ')';
  }
}/* toStreamRec() */

void Printer::toStream(std::ostream& out, const SExpr& sexpr) const throw() {
  toStreamRec(out, sexpr, PrettySExprs::getPrettySExprs(out) ? 2 : 0);
}/* Printer::toStream(SExpr) */

void Printer::toStream(std::ostream& out, const Model& m) const throw() {
  for(size_t i = 0; i < m.getNumCommands(); ++i) {
    toStream(out, m, m.getCommand(i));
  }
}/* Printer::toStream(Model) */

}/* CVC4 namespace */
