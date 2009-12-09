/*********************                                           -*- C++ -*-  */
/** smt_parser.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** SMT-LIB language parser implementation.
 **/

#include <iostream>
#include <fstream>

#include "parser/parser.h"
#include "util/command.h"
#include "util/Assert.h"
#include "parser/parser_exception.h"
#include "parser/antlr_parser.h"
#include "parser/smt/smt_parser.h"
#include "parser/smt/generated/AntlrSmtParser.hpp"
#include "parser/smt/generated/AntlrSmtLexer.hpp"

using namespace std;

namespace CVC4 {
namespace parser {

Command* SmtParser::parseNextCommand() throw(ParserException) {
  Command* cmd = 0;
  if(!done()) {
    try {
      cmd = d_antlr_parser->benchmark();
      setDone();
    } catch(antlr::ANTLRException& e) {
      setDone();
      throw ParserException(e.toString());
    }
  }
  return cmd;
}

Expr SmtParser::parseNextExpression() throw(ParserException) {
  Expr result;
  if(!done()) {
    try {
      result = d_antlr_parser->an_formula();
    } catch(antlr::ANTLRException& e) {
      setDone();
      throw ParserException(e.toString());
    }
  }
  return result;
}

SmtParser::~SmtParser() {
  delete d_antlr_parser;
  delete d_antlr_lexer;
}

SmtParser::SmtParser(ExprManager* em, istream& input, const char* file_name) :
  Parser(em), d_input(input) {
  if(!d_input) {
    throw ParserException(string("Read error") +
                          ((file_name != NULL) ? (string(" on ") + file_name) : ""));
  }
  d_antlr_lexer = new AntlrSmtLexer(input);
  d_antlr_lexer->setFilename(file_name);
  d_antlr_parser = new AntlrSmtParser(*d_antlr_lexer);
  d_antlr_parser->setExpressionManager(d_expr_manager);
  d_antlr_parser->setFilename(file_name);
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
