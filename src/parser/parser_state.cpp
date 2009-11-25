/*********************                                           -*- C++ -*-  */
/** parser_state.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Parser state implementation.
 **/

#include <string>
#include "parser/parser_state.h"
#include "parser/parser_exception.h"

namespace CVC4 {
namespace parser {

void ParserState::error(const std::string& s) throw(ParserException*) {
  throw new ParserException(s);
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
