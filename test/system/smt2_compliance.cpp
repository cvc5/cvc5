/*********************                                                        */
/*! \file smt2_compliance.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A test of SMT-LIBv2 commands, checks for compliant output
 **
 ** A test of SMT-LIBv2 commands, checks for compliant output.
 **/

#include <cassert>
#include <iostream>
#include <sstream>

#include "expr/expr_manager.h"
#include "options/base_options.h"
#include "options/set_language.h"
#include "options/smt_options.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "smt/smt_engine.h"
#include "smt_util/command.h"

using namespace CVC4;
using namespace CVC4::parser;
using namespace std;

void testGetInfo(SmtEngine& smt, const char* s);

int main() {
  Options opts;
  opts.set(options::inputLanguage, language::input::LANG_SMTLIB_V2);
  opts.set(options::outputLanguage, language::output::LANG_SMTLIB_V2);

  cout << language::SetLanguage(language::output::LANG_SMTLIB_V2);

  ExprManager em(opts);
  SmtEngine smt(&em);

  testGetInfo(smt, ":error-behavior");
  testGetInfo(smt, ":name");
  testGetInfo(smt, ":authors");
  testGetInfo(smt, ":version");
  testGetInfo(smt, ":status");
  testGetInfo(smt, ":reason-unknown");
  testGetInfo(smt, ":arbitrary-undefined-keyword");
  testGetInfo(smt, ":56");// legal
  testGetInfo(smt, ":<=");// legal
  testGetInfo(smt, ":->");// legal
  testGetInfo(smt, ":all-statistics");

  return 0;
}

void testGetInfo(SmtEngine& smt, const char* s) {
  ParserBuilder pb(smt.getExprManager(), "<internal>", smt.getExprManager()->getOptions());
  Parser* p = pb.withStringInput(string("(get-info ") + s + ")").build();
  assert(p != NULL);
  Command* c = p->nextCommand();
  assert(c != NULL);
  cout << c << endl;
  stringstream ss;
  c->invoke(&smt, ss);
  assert(p->nextCommand() == NULL);
  delete p;
  delete c;
  cout << ss.str() << endl << endl;
}
