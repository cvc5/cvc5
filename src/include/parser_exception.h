/*********************                                           -*- C++ -*-  */
/** exception.h
 ** This file is part of the CVC4 prototype.
 **
 ** Exception class.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4_PARSER_EXCEPTION_H
#define __CVC4_PARSER_EXCEPTION_H

#include "exception.h"
#include <string>
#include <iostream>

namespace CVC4 {

  class ParserException: public Exception {
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

}/* CVC4 namespace */

#endif /* __CVC4_PARSER_EXCEPTION_H */
