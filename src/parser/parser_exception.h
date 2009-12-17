/*********************                                           -*- C++ -*-  */
/** parser_exception.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Exception class for parse errors.
 **/

#ifndef __CVC4__PARSER__PARSER_EXCEPTION_H
#define __CVC4__PARSER__PARSER_EXCEPTION_H

#include "util/exception.h"
#include "cvc4_config.h"
#include <string>
#include <iostream>

namespace CVC4 {
namespace parser {

class CVC4_PUBLIC ParserException: public Exception {
public:
  // Constructors
  ParserException() { }
  ParserException(const std::string& msg): Exception(msg) { }
  ParserException(const char* msg): Exception(msg) { }
  // Destructor
  virtual ~ParserException() { }
  virtual std::string toString() const {
    return "Parse Error: " + d_msg;
  }
}; // end of class ParserException

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_EXCEPTION_H */
