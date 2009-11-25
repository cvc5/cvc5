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

#include "parser/parser.h"
#include "parser/parser_state.h"
#include "parser/parser_exception.h"
#include "parser/pl.hpp"
//#include "parser/smtlib.hpp"

// The communication entry points of the actual parsers

// for presentation language (PL.y and PL.lex)
extern int PLparse(); 
extern void *PL_createBuffer(int);
extern void PL_deleteBuffer(void *);
extern void PL_switchToBuffer(void *);
extern int PL_bufSize();
extern void *PL_bufState();
void PL_setInteractive(bool);

// for smtlib language (smtlib.y and smtlib.lex)
extern int smtlibparse(); 
extern void *smtlib_createBuffer(int);
extern void smtlib_deleteBuffer(void *);
extern void smtlib_switchToBuffer(void *);
extern int smtlib_bufSize();
extern void *smtlibBufState();
void smtlib_setInteractive(bool);

namespace CVC4 {
namespace parser {

ParserState *parserState;

Parser::Parser(CVC4::SmtEngine* smt, Language lang, std::istream& is, CVC4::Options* opts, bool interactive) throw()
  : d_smt(smt),
    d_is(is),
    d_opts(opts),
    d_lang(lang),
    d_interactive(interactive),
    d_buffer(0) {

  parserState->lineNum = 1;
  switch(d_lang) {
  case PL:
    d_buffer = ::PL_createBuffer(::PL_bufSize());
    break;
  case SMTLIB:
    //d_buffer = ::smtlib_createBuffer(::smtlib_bufSize());
    break;
  default:
    Unhandled();
  }
}

Parser::~Parser() throw() {
  switch(d_lang) {
  case PL:
    ::PL_deleteBuffer(d_buffer);
    break;
  case SMTLIB:
    //::smtlib_deleteBuffer(d_buffer);
    break;
  default:
    Unhandled();
  }
}

CVC4::Command* Parser::next() throw() {
  return 0;
}

bool Parser::done() const throw() {
  return false;
}

void Parser::printLocation(std::ostream & out) const throw() {
}

void Parser::reset() throw() {
}


}/* CVC4::parser namespace */
}/* CVC4 namespace */
