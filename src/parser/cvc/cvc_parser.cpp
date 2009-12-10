/*********************                                           -*- C++ -*-  */
/** cvc_parser.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** CVC presentation language parser implementation.
 **/

#include <iostream>
#include <fstream>

#include "parser/parser.h"
#include "util/command.h"
#include "util/Assert.h"
#include "parser/parser_exception.h"
#include "parser/antlr_parser.h"
#include "parser/cvc/cvc_parser.h"
#include "parser/cvc/generated/AntlrCvcParser.hpp"
#include "parser/cvc/generated/AntlrCvcLexer.hpp"

using namespace std;

namespace CVC4 {
namespace parser {

Command* CvcParser::parseNextCommand() throw(ParserException) {
  Command* cmd = 0;
  if(!done()) {
    try {
      cmd = d_antlr_parser->command();
      if(cmd == 0) {
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

Node CvcParser::parseNextExpression() throw(ParserException) {
  Node result;
  if(!done()) {
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

CvcParser::CvcParser(NodeManager*em, istream& input, const char* file_name) :
  Parser(em), d_input(input) {
  if(!d_input) {
    throw ParserException(string("Read error") +
                          ((file_name != NULL) ? (string(" on ") + file_name) : ""));
  }
  d_antlr_lexer = new AntlrCvcLexer(d_input);
  d_antlr_lexer->setFilename(file_name);
  d_antlr_parser = new AntlrCvcParser(*d_antlr_lexer);
  d_antlr_parser->setExpressionManager(d_expr_manager);
  d_antlr_parser->setFilename(file_name);
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
