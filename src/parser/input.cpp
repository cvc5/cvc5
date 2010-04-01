/*********************                                                        */
/** input.cpp
 ** Original author: dejan
 ** Major contributors: mdeters, cconway
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Parser implementation.
 **/

#include <stdint.h>

#include "input.h"
#include "parser_exception.h"
#include "parser_options.h"
#include "parser_state.h"
#include "expr/command.h"
#include "expr/expr.h"
#include "parser/cvc/cvc_input.h"
#include "parser/smt/smt_input.h"
#include "util/output.h"
#include "util/Assert.h"

using namespace std;

namespace CVC4 {
namespace parser {

bool Input::done() const {
  return d_parserState->done();
}

void Input::disableChecks() {
  d_parserState->disableChecks();
}

void Input::enableChecks() {
  d_parserState->enableChecks();
}

Command* Input::parseNextCommand() throw (ParserException) {
  Debug("parser") << "parseNextCommand()" << std::endl;
  Command* cmd = NULL;
  if(!done()) {
    try {
      cmd = doParseCommand();
      if(cmd == NULL) {
        d_parserState->setDone();
      }
    } catch(ParserException& e) {
      d_parserState->setDone();
      throw ParserException(e.toString());
    }
  }
  Debug("parser") << "parseNextCommand() => " << cmd << std::endl;
  return cmd;
}

Expr Input::parseNextExpression() throw (ParserException) {
  Debug("parser") << "parseNextExpression()" << std::endl;
  Expr result;
  if(!done()) {
    try {
      result = doParseExpr();
      if(result.isNull())
        d_parserState->setDone();
    } catch(ParserException& e) {
      d_parserState->setDone();
      throw ParserException(e.toString());
    }
  }
  Debug("parser") << "parseNextExpression() => " << result << std::endl;
  return result;
}

Input::Input(ExprManager* exprManager, const std::string& filename) {
  d_parserState = new ParserState(exprManager,filename,this);
}

Input::~Input() {
  delete d_parserState;
}

Input* Input::newFileInput(ExprManager* em, InputLanguage lang,
                           const std::string& filename, bool useMmap) {

  Input* input = 0;

  switch(lang) {
  case LANG_CVC4:
    input = new CvcInput(em,filename,useMmap);
    break;
  case LANG_SMTLIB:
    input = new SmtInput(em,filename,useMmap);
    break;

  default:
    Unhandled(lang);
  }

  return input;
}

Input* Input::newStringInput(ExprManager* em, InputLanguage lang,
                             const std::string& str, const std::string& name) {
  Input* input = 0;

  switch(lang) {
  case LANG_CVC4: {
    input = new CvcInput(em,str,name);
    break;
  }
  case LANG_SMTLIB:
    input = new SmtInput(em,str,name);
    break;

  default:
    Unhandled(lang);
  }
  return input;
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
