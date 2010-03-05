/*********************                                                        */
/** parser.cpp
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Parser implementation.
 **/

#include <iostream>
#include <fstream>
#include <antlr/CharScanner.hpp>
#include <antlr/CharBuffer.hpp>

#include "parser/parser.h"
#include "parser/memory_mapped_input_buffer.h"
#include "expr/command.h"
#include "util/output.h"
#include "util/Assert.h"
#include "parser/parser_exception.h"
#include "parser/antlr_parser.h"
#include "parser/smt/generated/AntlrSmtParser.hpp"
#include "parser/smt/generated/AntlrSmtLexer.hpp"
#include "parser/cvc/generated/AntlrCvcParser.hpp"
#include "parser/cvc/generated/AntlrCvcLexer.hpp"

using namespace std;
using namespace antlr;

namespace CVC4 {
namespace parser {

void Parser::setDone(bool done) {
  d_done = done;
}

bool Parser::done() const {
  return d_done;
}

Command* Parser::parseNextCommand() throw (ParserException, AssertionException) {
  Debug("parser") << "parseNextCommand()" << std::endl;
  Command* cmd = NULL;
  if(!done()) {
    try {
      cmd = d_antlrParser->parseCommand();
      if(cmd == NULL) {
        setDone();
      }
    } catch(antlr::ANTLRException& e) {
      setDone();
      throw ParserException(e.toString());
    }
  }
  Debug("parser") << "parseNextCommand() => " << cmd << std::endl;
  return cmd;
}

Expr Parser::parseNextExpression() throw (ParserException, AssertionException) {
  Debug("parser") << "parseNextExpression()" << std::endl;
  Expr result;
  if(!done()) {
    try {
      result = d_antlrParser->parseExpr();
      if(result.isNull())
        setDone();
    } catch(antlr::ANTLRException& e) {
      setDone();
      throw ParserException(e.toString());
    }
  }
  Debug("parser") << "parseNextExpression() => " << result << std::endl;
  return result;
}

Parser::~Parser() {
  delete d_antlrParser;
  delete d_antlrLexer;
  delete d_inputBuffer;
}

Parser::Parser(InputBuffer* inputBuffer, AntlrParser* antlrParser,
               CharScanner* antlrLexer) :
  d_done(false),
  d_antlrParser(antlrParser),
  d_antlrLexer(antlrLexer),
  d_inputBuffer(inputBuffer) {
}

Parser* Parser::getNewParser(ExprManager* em, InputLanguage lang,
                             InputBuffer* inputBuffer, string filename) {

  AntlrParser* antlrParser = 0;
  antlr::CharScanner* antlrLexer = 0;

  switch(lang) {
  case LANG_CVC4: {
    antlrLexer = new AntlrCvcLexer(*inputBuffer);
    antlrParser = new AntlrCvcParser(*antlrLexer);
    break;
  }
  case LANG_SMTLIB: {
//    MemoryMappedInputBuffer inputBuffer(filename);
//    antlrLexer = new AntlrSmtLexer(inputBuffer);
    antlrLexer = new AntlrSmtLexer(*inputBuffer);
    antlrParser = new AntlrSmtParser(*antlrLexer);
    break;
  }
  default:
    Unhandled("Unknown Input language!");
  }

  antlrLexer->setFilename(filename);
  antlrParser->setFilename(filename);
  antlrParser->setExpressionManager(em);

  return new Parser(inputBuffer, antlrParser, antlrLexer);
}

Parser* Parser::getMemoryMappedParser(ExprManager* em, InputLanguage lang, string filename) {
  MemoryMappedInputBuffer* inputBuffer = new MemoryMappedInputBuffer(filename);
  return getNewParser(em, lang, inputBuffer, filename);
}

Parser* Parser::getNewParser(ExprManager* em, InputLanguage lang,
                             istream& input, string filename) {
  antlr::CharBuffer* inputBuffer = new CharBuffer(input);
  return getNewParser(em, lang, inputBuffer, filename);
}

void Parser::disableChecks() {
  d_antlrParser->disableChecks();
}

void Parser::enableChecks() {
  d_antlrParser->enableChecks();
}


}/* CVC4::parser namespace */
}/* CVC4 namespace */
