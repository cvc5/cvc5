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
#include "util/Assert.h"
#include "parser_exception.h"
#include "parser/antlr_parser.h"
#include "parser/smt/AntlrSmtParser.hpp"
#include "parser/smt/AntlrSmtLexer.hpp"
#include "parser/cvc/AntlrCvcParser.hpp"
#include "parser/cvc/AntlrCvcLexer.hpp"

using namespace std;

namespace CVC4 {
namespace parser {

Parser::Parser(ExprManager* em) :
  d_expr_manager(em), d_done(false) {
}

void Parser::setDone(bool done) {
  d_done = done;
}

bool Parser::done() const {
  return d_done;
}

Command* SmtParser::parseNextCommand() throw (ParserException) {
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

Expr SmtParser::parseNextExpression() throw (ParserException) {
  Expr result;
  if (!done()) {
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

SmtParser::SmtParser(ExprManager* em, istream& input) :
  Parser(em) {
  d_antlr_lexer = new AntlrSmtLexer(input);
  d_antlr_parser = new AntlrSmtParser(*d_antlr_lexer);
  d_antlr_parser->setExpressionManager(d_expr_manager);
}

SmtParser::SmtParser(ExprManager*em, const char* file_name) :
  Parser(em), d_input(file_name) {
  if(!d_input) {
    throw ParserException(string("File not found or inaccessible: ") + file_name);
  }
  d_antlr_lexer = new AntlrSmtLexer(d_input);
  d_antlr_lexer->setFilename(file_name);
  d_antlr_parser = new AntlrSmtParser(*d_antlr_lexer);
  d_antlr_parser->setExpressionManager(d_expr_manager);
  d_antlr_parser->setFilename(file_name);
}

Command* CvcParser::parseNextCommand() throw (ParserException) {
  Command* cmd = 0;
  if(!done()) {
    try {
      cmd = d_antlr_parser->command();
      if (cmd == 0) {
        setDone();
        cmd = new EmptyCommand("EOF");
      }
    } catch(antlr::ANTLRException& e) {
      setDone();
      throw ParserException(e.toString());
    }
  }
  return cmd;
}

Expr CvcParser::parseNextExpression() throw (ParserException) {
  Expr result;
  if (!done()) {
    try {
      result = d_antlr_parser->formula();
    } catch(antlr::ANTLRException& e) {
      setDone();
      throw ParserException(e.toString());
    }
  }
  return result;
}

CvcParser::~CvcParser() {
  delete d_antlr_parser;
  delete d_antlr_lexer;
}

CvcParser::CvcParser(ExprManager* em, istream& input) :
  Parser(em) {
  d_antlr_lexer = new AntlrCvcLexer(input);
  d_antlr_parser = new AntlrCvcParser(*d_antlr_lexer);
  d_antlr_parser->setExpressionManager(d_expr_manager);
}

CvcParser::CvcParser(ExprManager*em, const char* file_name) :
  Parser(em), d_input(file_name) {
  if(!d_input) {
    throw ParserException(string("File not found or inaccessible: ") + file_name);
  }
  d_antlr_lexer = new AntlrCvcLexer(d_input);
  d_antlr_lexer->setFilename(file_name);
  d_antlr_parser = new AntlrCvcParser(*d_antlr_lexer);
  d_antlr_parser->setExpressionManager(d_expr_manager);
  d_antlr_parser->setFilename(file_name);
}


}/* CVC4::parser namespace */
}/* CVC4 namespace */

