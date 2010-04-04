/*********************                                                        */
/** parser_exception.h
 ** Original author: mdeters
 ** Major contributors: cconway
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Exception class for parse errors.
 **/

#include "cvc4parser_public.h"

#ifndef __CVC4__PARSER__PARSER_EXCEPTION_H
#define __CVC4__PARSER__PARSER_EXCEPTION_H

#include <iostream>
#include <string>
#include <sstream>

#include "util/exception.h"

namespace CVC4 {
namespace parser {

class CVC4_PUBLIC ParserException : public Exception {
public:
  // Constructors
  ParserException() :
    d_filename(),
    d_line(0),
    d_column(0) {
  }

  ParserException(const std::string& msg) :
    Exception(msg),
    d_filename(),
    d_line(0),
    d_column(0) {
  }

  ParserException(const char* msg) :
    Exception(msg),
    d_filename(),
    d_line(0),
    d_column(0) {
  }

  ParserException(const std::string& msg, const std::string& filename,
                  unsigned long line, unsigned long column) :
    Exception(msg),
    d_filename(filename),
    d_line(line),
    d_column(column) {
  }

  // Destructor
  virtual ~ParserException() throw() {}

  virtual std::string toString() const {
    if( d_line > 0 ) {
      std::stringstream ss;
      ss <<  "Parse Error: " << d_filename << ":" << d_line << "."
         << d_column << ": " << d_msg;
      return ss.str();
    } else {
      return "Parse Error: " + d_msg;
    }
  }

  std::string getFilename() const {
    return d_filename;
  }

  int getLine() const {
    return d_line;
  }

  int getColumn() const {
    return d_column;
  }

protected:
  std::string d_filename;
  unsigned long d_line;
  unsigned long d_column;
}; // end of class ParserException

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_EXCEPTION_H */
