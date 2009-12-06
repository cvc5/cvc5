/*********************                                           -*- C++ -*-  */
/** parser.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Parser implementation.
 **/

#include <iostream>
#include <fstream>

#include "parser.h"
#include "util/command.h"
#include "util/assert.h"
#include "parser_exception.h"
#include "parser/antlr_parser.h"
#include "parser/smt/AntlrSmtParser.hpp"
#include "parser/smt/AntlrSmtLexer.hpp"

using namespace std;

namespace CVC4 {
namespace parser {

Parser::Parser(ExprManager* em) :
  d_expr_manager(em) {
}

bool SmtParser::done() const {
  return d_done;
}

Command* SmtParser::parseNextCommand() throw (ParserException) {
  Command* cmd = 0;
  if(!d_done) {
    try {
      cmd = d_antlr_parser->benchmark();
      d_done = true;
    } catch(antlr::ANTLRException& e) {
      d_done = true;
      throw ParserException(e.toString());
    }
  }
  return cmd;
}

Expr SmtParser::parseNextExpression() throw (ParserException) {
  Expr result;
  if (!d_done) {
    try {
      result = d_antlr_parser->an_formula();
    } catch(antlr::ANTLRException& e) {
      d_done = true;
      throw ParserException(e.toString());
    }
  }
  return result;
}

SmtParser::~SmtParser() {
  delete d_antlr_parser;
  delete d_antlr_lexer;
}

SmtParser::SmtParser(ExprManager* em, istream& input) :
  Parser(em), d_done(false) {
  d_antlr_lexer = new AntlrSmtLexer(input);
  d_antlr_parser = new AntlrSmtParser(*d_antlr_lexer);
  d_antlr_parser->setExpressionManager(d_expr_manager);
}

SmtParser::SmtParser(ExprManager*em, const char* file_name) :
  Parser(em), d_done(false), d_input(file_name) {
  d_antlr_lexer = new AntlrSmtLexer(d_input);
  d_antlr_lexer->setFilename(file_name);
  d_antlr_parser = new AntlrSmtParser(*d_antlr_lexer);
  d_antlr_parser->setExpressionManager(d_expr_manager);
  d_antlr_parser->setFilename(file_name);
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */

